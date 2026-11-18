import Langlands.GroupScheme.MatrixRepresentation.CharacterSpaces
import Langlands.GroupScheme.MatrixRepresentation.StableSubrepresentation
import Langlands.GroupScheme.Rational.TorusCentralizer
import Langlands.GroupScheme.Torus.MaximalBaseChangeForwardReduction
import Langlands.GroupScheme.Torus.LatticeGalois

/-! # Character spaces of a commutative subgroup are stable under its centralizer -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]

/-- The `R`-linear functional `id_R ⊗ ℓ : R ⊗[k] A → R`. -/
def tensorFunctional (R A : Type u) [CommRing R] [Algebra k R] [CommRing A] [Algebra k A]
    (ℓ : A →ₗ[k] k) : R ⊗[k] A →ₗ[R] R :=
  (TensorProduct.AlgebraTensorModule.rid k R R).toLinearMap ∘ₗ
    TensorProduct.AlgebraTensorModule.map (LinearMap.id : R →ₗ[R] R) ℓ

theorem tensorFunctional_tmul {R A : Type u} [CommRing R] [Algebra k R] [CommRing A]
    [Algebra k A] (ℓ : A →ₗ[k] k) (r : R) (a : A) :
    tensorFunctional R A ℓ (r ⊗ₜ a) = ℓ a • r := by
  simp [tensorFunctional]

theorem tensorFunctional_includeRight {R A : Type u} [CommRing R] [Algebra k R] [CommRing A]
    [Algebra k A] (ℓ : A →ₗ[k] k) (a : A) :
    tensorFunctional R A ℓ (Algebra.TensorProduct.includeRight a) =
      algebraMap k R (ℓ a) := by
  rw [Algebra.TensorProduct.includeRight_apply, tensorFunctional_tmul, Algebra.smul_def,
    mul_one]

theorem tensorFunctional_includeLeft_mul {R A : Type u} [CommRing R] [Algebra k R] [CommRing A]
    [Algebra k A] (ℓ : A →ₗ[k] k) (r : R) (c : R ⊗[k] A) :
    tensorFunctional R A ℓ ((r ⊗ₜ[k] (1 : A)) * c) =
      r * tensorFunctional R A ℓ c := by
  have : (r ⊗ₜ[k] (1 : A)) * c = r • c := by
    rw [Algebra.smul_def]
    rfl
  rw [this, LinearMap.map_smul, smul_eq_mul]

section Centralizer

variable {G H : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))} [IsAffineHom T.toGrp.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem tensorFunctional_map_includeLeft_mulVec {R A : Type u} [CommRing R] [Algebra k R]
    [CommRing A] [Algebra k A] (ℓ : A →ₗ[k] k) (M : Matrix n n R) (z : n → R ⊗[k] A) :
    (fun r => tensorFunctional R A ℓ
        (((M.map (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] A)) *ᵥ z) r)) =
      M *ᵥ fun r => tensorFunctional R A ℓ (z r) := by
  funext r
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.TensorProduct.includeLeft_apply, tensorFunctional_includeLeft_mul]

/-- Let `f : H ⟶ G` take values in the centralizer of `i : T ⟶ G` on every test scheme,
for a commutative group scheme `T`. Then every character space of the restriction of a
representation `ρ` of `G` to `T` is stable under the restriction of `ρ` to `H`. -/
theorem isStableSubspace_characterSpace_of_centralizes (i : T.toGrp ⟶ G) (f : H ⟶ G)
    (hf : SubgroupFunctor.range f ≤ torusCentralizer i)
    (ρ : MatrixRepresentation G n) (χ : rationalCharacters T.toGrp) :
    (ρ.restrict f).IsStableSubspace ((ρ.restrict i).characterSpace χ) := by
  intro A x v hv ℓ
  have hfx : x ≫ f.hom.hom ∈ (torusCentralizer i).carrier _ :=
    SubgroupFunctor.le_def.mp hf _ (SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩)
  let R := CharacterUnits.Coord T.toGrp
  let C : CommAlgCat (CommRingCat.of k) := CommAlgCat.of (CommRingCat.of k) (R ⊗[k] A)
  let iL : R →ₐ[k] R ⊗[k] A := Algebra.TensorProduct.includeLeft
  let iR : A →ₐ[k] R ⊗[k] A := Algebra.TensorProduct.includeRight
  let jL : R ⟶ C := CommAlgCat.ofHom iL
  let jR : A ⟶ C := CommAlgCat.ofHom iR
  let s : (algSpec (CommRingCat.of k)).obj (op C) ⟶ T.X :=
    (algSpec (CommRingCat.of k)).map jL.op ≫ CharacterUnits.universalPoint T.toGrp
  let a := (algSpec (CommRingCat.of k)).map jR.op
  have hcomm := (hfx _ a s).map (ρ.affineMatrix C)
  have hM1 : ρ.affineMatrix C (a ≫ x ≫ f.hom.hom) =
      Matrix.GeneralLinearGroup.map iR.toRingHom (ρ.affineMatrix A (x ≫ f.hom.hom)) :=
    ρ.affineMatrix_naturality jR (x ≫ f.hom.hom)
  have hM2 : ρ.affineMatrix C (s ≫ i.hom.hom) =
      Matrix.GeneralLinearGroup.map iL.toRingHom
        ((ρ.restrict i).affineMatrix R (CharacterUnits.universalPoint T.toGrp)) := by
    have h := (ρ.restrict i).affineMatrix_naturality jL (CharacterUnits.universalPoint T.toGrp)
    rw [affineMatrix_restrict] at h
    exact h
  rw [hM1, hM2] at hcomm
  have hc := congrArg Units.val hcomm.eq
  simp only [Units.val_mul] at hc
  set U1 : Matrix n n A := (ρ.affineMatrix A (x ≫ f.hom.hom) : Matrix n n A) with hU1
  set US : Matrix n n R := (ρ.restrict i).universalCharacterMatrix with hUS
  change U1.map iR * US.map iL = US.map iL * U1.map iR at hc
  have hv' := (mem_characterSpace_iff _ χ v).mp hv
  rw [← hUS] at hv'
  rw [affineMatrix_restrict]
  apply (mem_characterSpace_iff _ χ _).mpr
  rw [← hUS]
  set y : n → A := U1 *ᵥ fun j => algebraMap k A (v j) with hy
  have hw : (fun r => algebraMap k R (ℓ (y r))) =
      fun r => tensorFunctional R A ℓ (iR (y r)) := by
    funext r
    exact (tensorFunctional_includeRight ℓ (y r)).symm
  change US *ᵥ (fun r => algebraMap k R (ℓ (y r))) =
    (CharacterUnits.unit χ : R) • fun r => algebraMap k R (ℓ (y r))
  rw [hw]
  have hiRy : (fun r => iR (y r)) = U1.map iR *ᵥ fun j => iL (algebraMap k R (v j)) := by
    rw [hy]
    funext r
    have h := RingHom.map_mulVec iR.toRingHom U1 (fun j => algebraMap k A (v j)) r
    rw [show (fun j => iL (algebraMap k R (v j))) =
        iR.toRingHom ∘ (fun j => algebraMap k A (v j)) from by
      funext j; simp only [Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        AlgHom.commutes]]
    exact h
  rw [← tensorFunctional_map_includeLeft_mulVec, hiRy, Matrix.mulVec_mulVec, ← hc,
    ← Matrix.mulVec_mulVec]
  have hS : US.map iL *ᵥ (fun j => iL (algebraMap k R (v j))) =
      iL (CharacterUnits.unit χ : R) • fun j => iL (algebraMap k R (v j)) := by
    have h := congrArg (fun z : n → R => fun j => iL (z j)) hv'
    simp only at h
    rw [show (fun j => iL ((US *ᵥ fun j => algebraMap k R (v j)) j)) =
      US.map iL *ᵥ fun j => iL (algebraMap k R (v j)) from by
        funext r; exact (iL.toRingHom.map_mulVec US _ r)] at h
    rw [h]
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    rfl
  rw [hS, Matrix.mulVec_smul, ← hiRy]
  funext r
  simp only [Pi.smul_apply, smul_eq_mul]
  exact tensorFunctional_includeLeft_mul ℓ (CharacterUnits.unit χ : R) (iR (y r))

omit [IsAffineHom T.toGrp.X.hom] in
/-- If `j` represents the centralizer of `i`, then every morphism `g ≫ j` takes values in
that centralizer. -/
theorem range_comp_le_torusCentralizer {M : GroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) {j : M ⟶ G} (hj : (torusCentralizer i).IsRepresentedBy j) (g : H ⟶ M) :
    SubgroupFunctor.range (g ≫ j) ≤ torusCentralizer i := by
  rw [← hj.2, SubgroupFunctor.le_def]
  intro U x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  exact SubgroupFunctor.mem_range.mpr ⟨y ≫ g.hom.hom, by
    simp only [Grp.comp_hom_hom, Category.assoc]⟩

end Centralizer

section BaseChange

variable {K : Type u} [Field K] [Algebra k K]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Taking values in the all-test centralizer is preserved by base change. -/
theorem range_le_torusCentralizer_baseChange (i : T.toGrp ⟶ G) {f : H ⟶ G}
    (hf : SubgroupFunctor.range f ≤ torusCentralizer i) :
    SubgroupFunctor.range ((GroupScheme.baseChange (algebraBaseMap k K)).map f) ≤
      torusCentralizer (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
        ((GroupScheme.baseChange (algebraBaseMap k K)).map i) := by
  rw [SubgroupFunctor.range_baseChangeHom, torusCentralizer_baseChange, SubgroupFunctor.le_def]
  intro U x hx
  rw [SubgroupFunctor.mem_baseChange] at hx ⊢
  exact SubgroupFunctor.le_def.mp hf _ hx

end BaseChange

end Langlands.GroupScheme.MatrixRepresentation
