import Langlands.GroupScheme.FiniteAlgebraIdempotentDynamic
import Langlands.GroupScheme.Quaternionic.HyperbolicTorus
import Langlands.GroupScheme.Quaternionic.HyperbolicLevi
import Langlands.GroupScheme.Quaternionic.RationalIsometryPoints
import Langlands.GroupScheme.Dynamic.ClosedSubgroup

/-!
# Eichler transformations are contracted by the hyperbolic cocharacter

Let `(e, f)` be a hyperbolic pair of `q` and let `μ = h.hyperbolicIsometryTorus` be the
cocharacter of `O(q)` scaling `e` by `t` and `f` by `t⁻¹`. Every Eichler transformation along
`f` is the matrix of a rational point of `O(q)` lying in the dynamic unipotent subgroup `U(μ)`.

The matrix of a rational point is `isometryRationalMatrix`, the Library's matrix of a
ground-field point (`FirstKindInvolution.isometryMatrixPoint`) composed with the comparison of
rational and coefficient points.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Matrix
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace FiniteAlgebraUnits

variable {K A : Type u} [Field K] [Ring A] [Algebra K A]
  {p q N₁ N₂ : A} (h : IsContracting p q N₁ N₂)
  {d : ℕ} (b : Module.Basis (Fin d) K A)

/-- On affine test schemes the contracting point is the unit `1 + N₁ + N₂` of `R ⊗ A`. -/
theorem affinePointsEquiv_contractingPoint (R : CommAlgCat.{u} (CommRingCat.of K)) :
    affinePointsEquiv b R (contractingPoint h b ((algSpec (CommRingCat.of K)).obj (op R))) =
      contractingUnit (K := K) (R := R) h 1 := by
  change Corepresented.affinePointsEquiv (functor K A) (corepresentableBy b) R
    (contractingPoint h b ((algSpec (CommRingCat.of K)).obj (op R))) = _
  rw [← Corepresented.map_affineSectionsIso_pointsEquiv]
  change Units.map
    (Algebra.TensorProduct.map (Corepresented.affineSectionsIso R).hom.hom
      (AlgHom.id K A)).toMonoidHom
    (pointsEquiv b _ (contractingPoint h b ((algSpec (CommRingCat.of K)).obj (op R)))) = _
  rw [contractingPoint, MulEquiv.apply_symm_apply]
  erw [contractingUnit_map]
  rw [map_one]

/-- Over the ground field, the contracting unit is `1 + N₁ + N₂`. -/
theorem lid_contractingUnit_one :
    Algebra.TensorProduct.lid K A
        (contractingUnit (K := K) (R := K) h 1 : K ⊗[K] A) = 1 + N₁ + N₂ := by
  simp [contractingValue]

end FiniteAlgebraUnits

namespace Quaternionic

namespace FirstKindInvolution.Eichler

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  (σ : FirstKindInvolution K D) {n : Type} [Fintype n] [DecidableEq n]
  (q : σ.QuadraticForms n)

/-! ### Matrices of rational points -/

/-- The matrix of a rational point of `O(q)`: the Library's matrix of the corresponding
ground-field coefficient point. -/
def isometryRationalMatrix : rationalPoints (σ.isometryGroup q) →* (Matrix n n D)ˣ :=
  (σ.isometryMatrixPoint q).comp
    (GaloisPointComparison.rationalCoeffEquiv K (σ.isometryGroup q)).toMonoidHom

theorem isometryRationalMatrix_apply (x : rationalPoints (σ.isometryGroup q)) :
    isometryRationalMatrix σ q x =
      Units.map (Algebra.TensorProduct.lid K (Matrix n n D)).toMonoidHom
        (FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis K (Matrix n n D))
          (CommAlgCat.of K K)
          (GaloisPointComparison.rationalCoeffEquiv K (σ.isometryGroup q) x ≫
            (σ.isometryGroupι q).hom.hom)) :=
  rfl

/-- The matrix of a rational point is a rational isometry. -/
theorem isometryRationalMatrix_mem (x : rationalPoints (σ.isometryGroup q)) :
    isometryRationalMatrix σ q x ∈ rationalIsometryGroup σ q :=
  σ.isometryMatrixPoint_defect_mem q _

/-- A rational point is determined by its matrix. -/
theorem isometryRationalMatrix_injective :
    Function.Injective (isometryRationalMatrix σ q) := by
  intro x y hxy
  rw [isometryRationalMatrix_apply, isometryRationalMatrix_apply] at hxy
  have h1 := (Units.map_injective
    (f := (Algebra.TensorProduct.lid K (Matrix n n D)).toMonoidHom)
    (Algebra.TensorProduct.lid K (Matrix n n D)).injective) hxy
  have h2 := (FiniteAlgebraUnits.affinePointsEquiv _ _).injective h1
  have : IsClosedImmersion (σ.isometryGroupι q).hom.hom.left :=
    σ.isClosedSubgroup_isometryGroupι q
  have : Mono (σ.isometryGroupι q).hom.hom := Over.mono_of_mono_left _
  exact (GaloisPointComparison.rationalCoeffEquiv K _).injective ((cancel_mono _).1 h2)

/-- Every rational isometry is the matrix of a rational point. -/
theorem exists_isometryRationalMatrix_eq {u : (Matrix n n D)ˣ}
    (hu : u ∈ rationalIsometryGroup σ q) :
    ∃ x, isometryRationalMatrix σ q x = u := by
  set u' : (K ⊗[K] Matrix n n D)ˣ :=
    Units.map (Algebra.TensorProduct.lid K (Matrix n n D)).symm.toMonoidHom u with hu'
  have hlid : Units.map (Algebra.TensorProduct.lid K (Matrix n n D)).toMonoidHom u' = u := by
    ext
    simp [hu']
  have hdef := (map_lid_mem_rationalIsometryGroup_iff σ q u').1 (by rw [hlid]; exact hu)
  obtain ⟨z, hz⟩ := IsHyperbolicPair.exists_isometryAffinePoint_of_defect (σ := σ) (q := q)
    (CommAlgCat.of K K) u' hdef
  refine ⟨(GaloisPointComparison.rationalCoeffEquiv K (σ.isometryGroup q)).symm z, ?_⟩
  rw [isometryRationalMatrix_apply, MulEquiv.apply_symm_apply, hz, MulEquiv.apply_symm_apply,
    hlid]

/-! ### Eichler transformations as contracting elements -/

variable {σ q}

omit [FiniteDimensional K D] in
/-- The rank-one matrix `v ↦ h(v, y) x` is the hyperbolic line matrix of `(x, y)`. -/
theorem formRankOne_eq_hyperbolicLineMatrix (y x : n → D) :
    formRankOne σ q y x = σ.hyperbolicLineMatrix q x y := by
  rw [ext_iff_vecMul]
  intro v
  rw [vecMul_formRankOne, vecMul_hyperbolicLineMatrix]

omit [FiniteDimensional K D] in
/-- The Eichler matrix along `f` as `1 + N₁ + N₂`. -/
theorem eichlerMatrix_eq_one_add (f x : n → D) (c : D) :
    eichlerMatrix σ q f x c =
      1 + (formRankOne σ q f x - formRankOne σ q x f) + -formRankOne σ q f (c • f) := by
  rw [eichlerMatrix]
  abel

variable {e f : n → D}

omit [FiniteDimensional K D] in
/-- For `x` orthogonal to `e` and `f`, the two parts `N₁ = (v ↦ h(v,f) x - h(v,x) f)` and
`N₂ = (v ↦ -h(v,f) c f)` of the Eichler matrix `E^f_{x,c}` have weights `1` and `2` for the
idempotents `v ↦ h(v,f) e` and `v ↦ h(v,e) f` of the hyperbolic pair. -/
theorem isContracting_eichler (h : σ.IsHyperbolicPair q e f) {x : n → D}
    (hxe : σ.sesqForm (σ.polar q) x e = 0) (hxf : σ.sesqForm (σ.polar q) x f = 0) (c : D) :
    FiniteAlgebraUnits.IsContracting (σ.hyperbolicLineMatrix q e f)
      (σ.hyperbolicLineMatrix q f e) (formRankOne σ q f x - formRankOne σ q x f)
      (-formRankOne σ q f (c • f)) := by
  have hee : σ.sesqForm (σ.polar q) e e = 0 := sesqForm_polar_self_eq_zero σ q e h.1
  have hff : σ.sesqForm (σ.polar q) f f = 0 := sesqForm_polar_self_eq_zero σ q f h.2.1
  have hef : σ.sesqForm (σ.polar q) e f = 1 := h.2.2
  have hfe : σ.sesqForm (σ.polar q) f e = 1 := by
    rw [← sesqForm_polar_swap, hef, map_one]
  have hex : σ.sesqForm (σ.polar q) e x = 0 := by
    rw [← sesqForm_polar_swap, hxe, map_zero]
  have hfx : σ.sesqForm (σ.polar q) f x = 0 := by
    rw [← sesqForm_polar_swap, hxf, map_zero]
  constructor <;> rw [ext_iff_vecMul] <;> intro v <;>
    simp only [← vecMul_vecMul, vecMul_sub, vecMul_neg, vecMul_add, vecMul_formRankOne,
      vecMul_hyperbolicLineMatrix, vecMul_zero, sesqForm_sub_left, sesqForm_neg_left,
      sesqForm_smul_left, hff, hef, hfe, hex, hfx, hxe, hxf, mul_zero, zero_mul, mul_one,
      zero_smul, sub_zero, zero_sub, neg_zero, neg_smul, smul_smul, sub_self]
  all_goals abel

omit [FiniteDimensional K D] in
/-- Moving the defining vector into `{e, f}^⊥`: with `β = h(x, e)`,
`E^f_{x,c} = E^f_{x - β f, c + σ(β) - β}`. -/
theorem eichlerMatrix_eq_sub_smul (x : n → D) (c : D) :
    eichlerMatrix σ q f x c =
      eichlerMatrix σ q f (x - σ.sesqForm (σ.polar q) x e • f)
        (c + σ (σ.sesqForm (σ.polar q) x e) - σ.sesqForm (σ.polar q) x e) := by
  rw [ext_iff_vecMul]
  intro v
  simp only [vecMul_eichlerMatrix, sesqForm_sub_right, sesqForm_smul_right]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  noncomm_ring

omit [FiniteDimensional K D] in
/-- The vector `x - h(x, e) f` is orthogonal to `e`. -/
theorem sesqForm_sub_smul_left (h : σ.IsHyperbolicPair q e f) (x : n → D) :
    σ.sesqForm (σ.polar q) (x - σ.sesqForm (σ.polar q) x e • f) e = 0 := by
  have hfe : σ.sesqForm (σ.polar q) f e = 1 := by
    rw [← sesqForm_polar_swap, h.2.2, map_one]
  rw [sesqForm_sub_left, sesqForm_smul_left, hfe, mul_one, sub_self]

omit [FiniteDimensional K D] in
/-- For `x` orthogonal to `f`, the vector `x - h(x, e) f` is orthogonal to `f`. -/
theorem sesqForm_sub_smul_right (h : σ.IsHyperbolicPair q e f) {x : n → D}
    (hxf : σ.sesqForm (σ.polar q) x f = 0) :
    σ.sesqForm (σ.polar q) (x - σ.sesqForm (σ.polar q) x e • f) f = 0 := by
  rw [sesqForm_sub_left, sesqForm_smul_left, sesqForm_polar_self_eq_zero σ q f h.2.1, hxf,
    mul_zero, sub_self]

/-! ### Rational points in the dynamic unipotent subgroup -/

omit [FiniteDimensional K D] in
/-- A coefficient point over `K` in a subgroup functor gives a rational point in it. -/
theorem rationalCoeffEquiv_symm_mem {G : GroupScheme (Spec (CommRingCat.of K))}
    (F : SubgroupFunctor G) {z : G.affinePoints (CommAlgCat.of K K)}
    (hz : z ∈ F.carrier ((algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of K K)))) :
    (GaloisPointComparison.rationalCoeffEquiv K G).symm z ∈ F.carrier (Over.mk (𝟙 _)) :=
  F.comp_mem (AlgebraicGeometry.PointTopology.ringTestSelfIso K).inv hz

variable [Infinite K]

/-- **Eichler transformations along `f` are contracting.** Every Eichler transformation along
`f` is the matrix of a rational point of `O(q)` in the dynamic unipotent subgroup of the
hyperbolic cocharacter `h.hyperbolicIsometryTorus` (which scales `e` by `t` and `f` by `t⁻¹`). -/
theorem exists_mem_unipotent_of_mem_eichlerSet [LinearOrder n] (h : σ.IsHyperbolicPair q e f)
    {u : (Matrix n n D)ˣ} (hu : u ∈ eichlerSet σ q f) :
    ∃ g ∈ (Dynamic.unipotent h.hyperbolicIsometryTorus).carrier (Over.mk (𝟙 _)),
      isometryRationalMatrix σ q g = u := by
  obtain ⟨g, hg⟩ := exists_isometryRationalMatrix_eq σ q (eichlerSet_subset σ q h.2.1 hu)
  refine ⟨g, ?_, hg⟩
  obtain ⟨x, c, hxf, -, hux⟩ := hu
  have hC := isContracting_eichler h (sesqForm_sub_smul_left h x)
    (sesqForm_sub_smul_right h hxf)
    (c + σ (σ.sesqForm (σ.polar q) x e) - σ.sesqForm (σ.polar q) x e)
  set b := Module.finBasis K (Matrix n n D)
  set T := (algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of K K))
  set z := GaloisPointComparison.rationalCoeffEquiv K (σ.isometryGroup q) g with hz
  have hzι : z ≫ (σ.isometryGroupι q).hom.hom = FiniteAlgebraUnits.contractingPoint hC b T := by
    apply (FiniteAlgebraUnits.affinePointsEquiv b (CommAlgCat.of K K)).injective
    apply Units.map_injective (f := (Algebra.TensorProduct.lid K (Matrix n n D)).toMonoidHom)
      (Algebra.TensorProduct.lid K (Matrix n n D)).injective
    change isometryRationalMatrix σ q g = _
    rw [hg, FiniteAlgebraUnits.affinePointsEquiv_contractingPoint]
    apply Units.ext
    change (u : Matrix n n D) = Algebra.TensorProduct.lid K (Matrix n n D)
      (FiniteAlgebraUnits.contractingUnit (K := K) (R := K) hC 1 : K ⊗[K] Matrix n n D)
    rw [FiniteAlgebraUnits.lid_contractingUnit_one, hux, eichlerMatrix_eq_sub_smul,
      eichlerMatrix_eq_one_add]
  have hzU : z ∈ (Dynamic.unipotent h.hyperbolicIsometryTorus).carrier T := by
    rw [Dynamic.unipotent_eq_comap_of_isClosedSubgroup _ _ (σ.isClosedSubgroup_isometryGroupι q),
      SubgroupFunctor.mem_comap, h.hyperbolicIsometryTorus_comp, hzι]
    exact FiniteAlgebraUnits.contractingPoint_mem_unipotent hC _ _ _ _ b T
  have := rationalCoeffEquiv_symm_mem _ hzU
  rwa [hz, MulEquiv.symm_apply_apply] at this

/-- **Eichler transformations along `e` are contracting** for the opposite cocharacter
`h.symm.hyperbolicIsometryTorus` (which scales `f` by `t` and `e` by `t⁻¹`). -/
theorem exists_mem_unipotent_of_mem_eichlerSet_left [LinearOrder n]
    (h : σ.IsHyperbolicPair q e f) {u : (Matrix n n D)ˣ} (hu : u ∈ eichlerSet σ q e) :
    ∃ g ∈ (Dynamic.unipotent h.symm.hyperbolicIsometryTorus).carrier (Over.mk (𝟙 _)),
      isometryRationalMatrix σ q g = u :=
  exists_mem_unipotent_of_mem_eichlerSet h.symm hu

end FirstKindInvolution.Eichler

end Quaternionic

end Langlands.GroupScheme
