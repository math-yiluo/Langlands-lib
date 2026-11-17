import Langlands.GroupScheme.CentralSimpleNormOneSplitting
import Langlands.GroupScheme.CorepresentedAffineComparison
import Langlands.GroupScheme.SpecialLinearOuterAutomorphism
import Langlands.GroupScheme.CenterAutomorphismBaseChange
import Langlands.GroupScheme.NormOneCoefficientAutomorphism

/-! # The splitting chart on affine norm-one points -/

noncomputable section

set_option maxHeartbeats 800000
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Conjugating an automorphism through an actual isomorphism commutes with its
point action. -/
theorem point_comp_conjugateIso {S : Scheme.{u}} {G H : GroupScheme S}
    (i : G ≅ H) (f : G ≅ G) (T : Over S) (x : T ⟶ G.X) :
    (x ≫ i.hom.hom.hom) ≫ ((i.symm.trans f).trans i).hom.hom.hom =
      (x ≫ f.hom.hom.hom) ≫ i.hom.hom.hom := by
  have hc : i.hom.hom.hom ≫ i.inv.hom.hom = 𝟙 _ := by
    simpa only [Grp.comp_hom_hom, Grp.id_hom_hom] using
      congrArg (fun h => h.hom.hom) i.hom_inv_id
  change (x ≫ i.hom.hom.hom) ≫
    (i.inv.hom.hom ≫ f.hom.hom.hom ≫ i.hom.hom.hom) = _
  rw [Category.assoc, ← Category.assoc i.hom.hom.hom, hc, Category.id_comp,
    Category.assoc]

/-- The inverse pullback point equivalence respects the original point action. -/
theorem baseChangePointsEquiv_symm_comp {S S' : Scheme.{u}} (b : S' ⟶ S)
    {G H : GroupScheme S} (f : G ⟶ H) (T : Over S')
    (x : (Over.map b).obj T ⟶ G.X) :
    (baseChangePointsEquiv b G T).symm x ≫ ((GroupScheme.baseChange b).map f).hom.hom =
      (baseChangePointsEquiv b H T).symm (x ≫ f.hom.hom) := by
  apply (baseChangePointsEquiv b H T).injective
  rw [baseChangePointsEquiv_comp, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

/-- The split outer matrix formula in every positive matrix size. -/
theorem SpecialLinear.exists_outer_matrix_of_pos {k : Type u} [Field k] {d : ℕ}
    (hd : 0 < d)
    (f : SpecialLinear.groupScheme (Fin d) (CommRingCat.of k) ≅
      SpecialLinear.groupScheme (Fin d) (CommRingCat.of k))
    (hf : ¬ AutomorphismFixesCenter f) :
    ∃ H : GL (Fin d) k,
      ∀ (T : Over (Spec (CommRingCat.of k)))
        (z : T ⟶ (SpecialLinear.groupScheme (Fin d) (CommRingCat.of k)).X),
        (SpecialLinear.pointsEquiv (Fin d) (CommRingCat.of k) T
          (z ≫ f.hom.hom.hom) : Matrix (Fin d) (Fin d) Γ(T.left, ⊤)) =
          (Matrix.GeneralLinearGroup.map (scalarMap T) H : Matrix (Fin d) (Fin d) Γ(T.left, ⊤)) *
            (((SpecialLinear.pointsEquiv (Fin d) (CommRingCat.of k) T z)⁻¹ :
              Matrix.SpecialLinearGroup (Fin d) Γ(T.left, ⊤)) :
              Matrix (Fin d) (Fin d) Γ(T.left, ⊤)).transpose *
            (Matrix.GeneralLinearGroup.map (scalarMap T) H⁻¹ :
              Matrix (Fin d) (Fin d) Γ(T.left, ⊤)) := by
  cases d with
  | zero => exact (Nat.not_lt_zero _ hd).elim
  | succ n => exact SpecialLinear.exists_outer_matrix f hf

end Langlands.GroupScheme

namespace Langlands.GroupScheme.CentralSimpleUnits.Splitting

open Langlands.CentralSimple Langlands.ReducedNorm

variable (K A : Type u) [Field K] [Ring A] [Algebra K A]
  [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]
  {L : Type u} [Field L] [Algebra K L]
  (e : L ⊗[K] A ≃ₐ[L]
    Matrix (Fin (reducedDegree K A)) (Fin (reducedDegree K A)) L)

local notation "Z" => Over.mk (𝟙 (Spec (CommRingCat.of L)))
local notation "R" => CommAlgCat.of (CommRingCat.of K) L
local notation "ιΓ" => (Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom

local instance : Algebra L (coefficients (K := K) Z) := sectionsAlgebra K Z
local instance : IsScalarTower K L (coefficients (K := K) Z) := sectionsScalarTower K Z

/-- Over the identity affine test, the section scalar map is the inverse of the
canonical spectrum/global-sections isomorphism. -/
theorem basePoint_algebraMap :
    algebraMap L (coefficients (K := K) Z) = ιΓ := by
  ext r
  change (𝟙 (Spec (CommRingCat.of L)) : Spec (CommRingCat.of L) ⟶
    Spec (CommRingCat.of L)).appTop
    ((Scheme.ΓSpecIso (CommRingCat.of L)).inv r) = _
  simp
  rfl

omit [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A] in
/-- The section-valued splitting matrix is the affine chart matrix with its
coefficients transported to global sections. -/
theorem splittingMap_affine (x : L ⊗[K] A) :
    splittingMap e (coefficients (K := K) Z)
      (Algebra.TensorProduct.map (Corepresented.affineSectionsIso R).inv.hom
        (AlgHom.id K A) x) = (e x).map ιΓ := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, splittingMap_tmul]
    rw [basePoint_algebraMap K]
    have he : e (r ⊗ₜ[K] a) = r • e (1 ⊗ₜ[K] a) := by
      simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
        map_smul e r (1 ⊗ₜ[K] a)
    rw [he]
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul]
    rfl
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    ext i j
    simp only [Matrix.add_apply, Matrix.map_apply, map_add]

/-- At the identity test over the splitting field, the actual scheme splitting
is exactly the original algebra chart on affine norm-one tensor units. -/
theorem splittingIso_affine_points
    (z : (algSpec (CommRingCat.of K)).obj (op R) ⟶ (normOne K A).X) :
    (SpecialLinear.pointsEquiv (Fin (reducedDegree K A)) (CommRingCat.of L) Z
      ((baseChangePointsEquiv (baseMap (K := K) (L := L)) (normOne K A) Z).symm z ≫
        (splittingIso K A e).hom.hom.hom) : Matrix (Fin (reducedDegree K A)) (Fin (reducedDegree K A)) Γ((Z).left, ⊤)) =
      (e ((normOneAffinePointsEquiv K A R z).val : L ⊗[K] A)).map ιΓ := by
  rw [splittingIso_hom_points, basePointsEquiv_val, MulEquiv.apply_symm_apply]
  have hp := Corepresented.pointsEquiv_eq_affinePointsEquiv
    (FiniteAlgebraUnits.functor K A)
    (FiniteAlgebraUnits.corepresentableBy (Module.finBasis K A)) R
    (z ≫ (normOneι K A).hom.hom)
  change (normOnePointsEquiv K A ((Over.map (baseMap (K := K) (L := L))).obj Z) z).val =
    Units.map (Algebra.TensorProduct.map (Corepresented.affineSectionsIso R).inv.hom
      (AlgHom.id K A)).toMonoidHom (normOneAffinePointsEquiv K A R z).val at hp
  rw [hp]
  exact splittingMap_affine K A e _

/-- The splitting comparison on affine coefficient units, with matrix entries
in the actual global sections of the identity splitting-field test. -/
def affineSplittingEquiv :
    reducedNormOne K A L ≃*
      Matrix.SpecialLinearGroup (Fin (reducedDegree K A)) Γ((Z).left, ⊤) :=
  (normOneAffinePointsEquiv K A R).symm.trans
    ((baseChangePointsEquiv (baseMap (K := K) (L := L)) (normOne K A) Z).symm.trans
      ((((yonedaGrp.mapIso (splittingIso K A e)).app (op Z)).groupIsoToMulEquiv).trans
        (SpecialLinear.pointsEquiv (Fin (reducedDegree K A)) (CommRingCat.of L) Z)))

theorem affineSplittingEquiv_apply (x : reducedNormOne K A L) :
    affineSplittingEquiv K A e x =
      SpecialLinear.pointsEquiv (Fin (reducedDegree K A)) (CommRingCat.of L) Z
        ((baseChangePointsEquiv (baseMap (K := K) (L := L)) (normOne K A) Z).symm
          ((normOneAffinePointsEquiv K A R).symm x) ≫
            (splittingIso K A e).hom.hom.hom) := rfl

/-- The affine splitting comparison recovers the original chart matrix. -/
theorem affineSplittingEquiv_val (x : reducedNormOne K A L) :
    (affineSplittingEquiv K A e x : Matrix (Fin (reducedDegree K A)) (Fin (reducedDegree K A)) Γ((Z).left, ⊤)) =
      (e (x.val : L ⊗[K] A)).map ιΓ := by
  rw [affineSplittingEquiv_apply, splittingIso_affine_points,
    MulEquiv.apply_symm_apply]

/-- An actual norm-one automorphism expressed in the split special-linear model. -/
def splitAutomorphism (f : normOne K A ≅ normOne K A) :
    SpecialLinear.groupScheme (Fin (reducedDegree K A)) (CommRingCat.of L) ≅
      SpecialLinear.groupScheme (Fin (reducedDegree K A)) (CommRingCat.of L) :=
  ((splittingIso K A e).symm.trans
    ((GroupScheme.baseChange (baseMap (K := K) (L := L))).mapIso f)).trans
      (splittingIso K A e)

/-- Coordinate transport through the splitting agrees with the affine action of
the original actual automorphism. -/
theorem affineSplittingEquiv_action (f : normOne K A ≅ normOne K A)
    (x : reducedNormOne K A L) :
    SpecialLinear.pointsEquiv (Fin (reducedDegree K A)) (CommRingCat.of L) Z
      ((SpecialLinear.pointsEquiv (Fin (reducedDegree K A)) (CommRingCat.of L) Z).symm
        (affineSplittingEquiv K A e x) ≫ (splitAutomorphism K A e f).hom.hom.hom) =
      affineSplittingEquiv K A e
        (normOneAffinePointsEquiv K A R
          ((normOneAffinePointsEquiv K A R).symm x ≫ f.hom.hom.hom)) := by
  rw [affineSplittingEquiv_apply, MulEquiv.symm_apply_apply]
  rw [show (splitAutomorphism K A e f) =
    (((splittingIso K A e).symm.trans
      ((GroupScheme.baseChange (baseMap (K := K) (L := L))).mapIso f)).trans
        (splittingIso K A e)) from rfl]
  rw [point_comp_conjugateIso]
  simp only [Functor.mapIso_hom]
  rw [baseChangePointsEquiv_symm_comp]
  rw [affineSplittingEquiv_apply, MulEquiv.symm_apply_apply]

/-- A centre-moving actual automorphism remains centre-moving in the split model. -/
theorem not_fixesCenter_splitAutomorphism (f : normOne K A ≅ normOne K A)
    (hf : ¬ AutomorphismFixesCenter f) :
    ¬ AutomorphismFixesCenter (splitAutomorphism K A e f) := by
  intro h
  apply hf
  apply AutomorphismFixesCenter.of_baseChange (baseMap (K := K) (L := L))
  exact (AutomorphismFixesCenter.conjugate_iff (splittingIso K A e)
    ((GroupScheme.baseChange (baseMap (K := K) (L := L))).mapIso f)).mp h

/-- Every centre-moving norm-one automorphism has an outer matrix formula in a
splitting chart, expressed directly on affine coefficient tensor units. -/
theorem exists_coefficient_outer_matrix (f : normOne K A ≅ normOne K A)
    (hf : ¬ AutomorphismFixesCenter f) :
    ∃ H : GL (Fin (reducedDegree K A)) L,
      ∀ x : reducedNormOne K A L,
        e ((coefficientAutomorphism K A f R x).val : L ⊗[K] A) =
          (H : Matrix (Fin (reducedDegree K A)) (Fin (reducedDegree K A)) L) * (e ((x⁻¹).val : L ⊗[K] A)).transpose *
            ((H⁻¹ : GL (Fin (reducedDegree K A)) L) : Matrix (Fin (reducedDegree K A)) (Fin (reducedDegree K A)) L) := by
  classical
  have hs := not_fixesCenter_splitAutomorphism K A e f hf
  have hpos := reducedDegree_pos K A
  have hex : ∃ H : GL (Fin (reducedDegree K A)) L,
      ∀ (T : Over (Spec (CommRingCat.of L)))
        (z : T ⟶ (SpecialLinear.groupScheme (Fin (reducedDegree K A))
          (CommRingCat.of L)).X),
        (SpecialLinear.pointsEquiv (Fin (reducedDegree K A)) (CommRingCat.of L) T
          (z ≫ (splitAutomorphism K A e f).hom.hom.hom) :
          Matrix (Fin (reducedDegree K A)) (Fin (reducedDegree K A)) Γ(T.left, ⊤)) =
          (Matrix.GeneralLinearGroup.map (scalarMap T) H : Matrix (Fin (reducedDegree K A)) (Fin (reducedDegree K A)) Γ(T.left, ⊤)) *
            (((SpecialLinear.pointsEquiv (Fin (reducedDegree K A)) (CommRingCat.of L) T z)⁻¹ :
              Matrix.SpecialLinearGroup (Fin (reducedDegree K A)) Γ(T.left, ⊤)) :
              Matrix (Fin (reducedDegree K A)) (Fin (reducedDegree K A)) Γ(T.left, ⊤)).transpose *
            (Matrix.GeneralLinearGroup.map (scalarMap T) H⁻¹ : Matrix (Fin (reducedDegree K A)) (Fin (reducedDegree K A)) Γ(T.left, ⊤)) := by
    exact SpecialLinear.exists_outer_matrix_of_pos hpos (splitAutomorphism K A e f) hs
  obtain ⟨H, hH⟩ := hex
  refine ⟨H, fun x => ?_⟩
  have hm := hH Z
    ((SpecialLinear.pointsEquiv (Fin (reducedDegree K A)) (CommRingCat.of L) Z).symm
      (affineSplittingEquiv K A e x))
  rw [affineSplittingEquiv_action, MulEquiv.apply_symm_apply] at hm
  change (affineSplittingEquiv K A e (coefficientAutomorphism K A f R x) :
    Matrix (Fin (reducedDegree K A)) (Fin (reducedDegree K A)) Γ((Z).left, ⊤)) = _ at hm
  rw [affineSplittingEquiv_val, ← map_inv, affineSplittingEquiv_val] at hm
  have hscalar : scalarMap Z = ιΓ := by
    change ((𝟙 (Spec (CommRingCat.of L)) : Spec (CommRingCat.of L) ⟶
      Spec (CommRingCat.of L)).appTop.hom.comp ιΓ) = ιΓ
    ext r
    rfl
  simp only [hscalar] at hm
  have hm' : (e ((coefficientAutomorphism K A f R x).val : L ⊗[K] A)).map ιΓ =
      ((H : Matrix (Fin (reducedDegree K A)) (Fin (reducedDegree K A)) L) *
        (e ((x⁻¹).val : L ⊗[K] A)).transpose *
          ((H⁻¹ : GL (Fin (reducedDegree K A)) L) : Matrix (Fin (reducedDegree K A)) (Fin (reducedDegree K A)) L)).map ιΓ := by
    simp only [Matrix.map_mul, Matrix.transpose_map]
    exact hm
  have hinj : Function.Injective ιΓ :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of L)).inv).1
  ext i j
  exact hinj (congrArg (fun M => M i j) hm')

end Langlands.GroupScheme.CentralSimpleUnits.Splitting
