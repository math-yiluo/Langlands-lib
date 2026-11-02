import Langlands.AlgebraicGeometry.ProjectiveSpace.RationalCoordinates
import Langlands.AlgebraicGeometry.ProjectiveSpace.PointComparison
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Projective lines of actual rational points -/

noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization
open scoped LinearAlgebra.Projectivization

namespace Langlands.AlgebraicGeometry.ProjectiveSpace

universe u

variable {K : Type u} [Field K] (n : ℕ)

/-- The line of the normalized coordinates of an actual rational point. -/
def pointLine (p : Spec (CommRingCat.of K) ⟶ ProjectiveSpace K n)
    (hp : p ≫ projectiveSpaceToSpec K n = 𝟙 _) : ℙ K (Fin (n + 1) → K) :=
  Projectivization.mk K (pointCoordinates n p hp) (pointCoordinates_ne_zero n p hp)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Equal coordinate lines determine equal actual scheme morphisms. -/
theorem eq_of_pointLine_eq
    (p q : Spec (CommRingCat.of K) ⟶ ProjectiveSpace K n)
    (hp : p ≫ projectiveSpaceToSpec K n = 𝟙 _)
    (hq : q ≫ projectiveSpaceToSpec K n = 𝟙 _)
    (h : pointLine n p hp = pointLine n q hq) : p = q := by
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ _ _).mp h
  let i := pointChartIndex n p hp
  let j := pointChartIndex n q hq
  have hi : IsUnit (pointCoordinates n p hp i) := by
    simp [i]
  have hjval : pointCoordinates n p hp j = (a : K) := by
    have hj := congrFun ha j
    simpa [j, Units.smul_def] using hj.symm
  have hj : IsUnit (pointCoordinates n p hp j) := hjval.symm ▸ a.isUnit
  have hpi (l : Fin (n + 1)) :
      pointChartMap n p hp (_root_.AlgebraicGeometry.ProjSpace.ratio K n i l) *
        pointCoordinates n p hp i = pointCoordinates n p hp l := by
    simp only [i, pointCoordinates_index, mul_one]
    rfl
  have hqj (l : Fin (n + 1)) :
      pointChartMap n q hq (_root_.AlgebraicGeometry.ProjSpace.ratio K n j l) *
        pointCoordinates n p hp j = pointCoordinates n p hp l := by
    rw [hjval]
    have hl := congrFun ha l
    change pointCoordinates n q hq l * (a : K) = pointCoordinates n p hp l
    simpa [mul_comm, Units.smul_def] using hl
  have he := _root_.AlgebraicGeometry.ProjSpace.specMap_comp_awayInclusion_eq_of_forall_apply_ratio_mul_eq
    K n K (pointCoordinates n p hp) i j hi hj
    (pointChartMap n p hp) (pointChartMap n q hq) hpi hqj
  change chartPoint n i (pointChartMap n p hp) = chartPoint n j (pointChartMap n q hq) at he
  simpa [i, j] using he

theorem pointLine_eq_iff
    (p q : Spec (CommRingCat.of K) ⟶ ProjectiveSpace K n)
    (hp : p ≫ projectiveSpaceToSpec K n = 𝟙 _)
    (hq : q ≫ projectiveSpaceToSpec K n = 𝟙 _) :
    pointLine n p hp = pointLine n q hq ↔ p = q := by
  constructor
  · exact eq_of_pointLine_eq n p q hp hq
  · rintro rfl
    rfl

/-- Actual points over the coefficient field embed into the vector-space projectivization. -/
def pointLineEmbedding :
    {p : Spec (CommRingCat.of K) ⟶ ProjectiveSpace K n //
      p ≫ projectiveSpaceToSpec K n = 𝟙 _} ↪ ℙ K (Fin (n + 1) → K) where
  toFun p := pointLine n p.1 p.2
  inj' p q h := Subtype.ext (eq_of_pointLine_eq n p.1 q.1 p.2 q.2 h)

/-- Incidence is unchanged by the representative chosen by vector-space projectivization. -/
theorem pointLine_linearForm_mem_iff
    (p : Spec (CommRingCat.of K) ⟶ ProjectiveSpace K n)
    (hp : p ≫ projectiveSpaceToSpec K n = 𝟙 _)
    (ℓ : (Fin (n + 1) → K) →ₗ[K] K) :
    (linearFormPolynomialEquiv K n ℓ : ProjectiveCoordinateRing K n) ∈
      (p (IsLocalRing.closedPoint K)).asHomogeneousIdeal ↔
        ℓ (pointLine n p hp).rep = 0 := by
  rw [pointCoordinates_linearForm_mem_iff n p hp ℓ]
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K
    (pointCoordinates n p hp) (pointCoordinates_ne_zero n p hp)
  change a • pointCoordinates n p hp = (pointLine n p hp).rep at ha
  rw [← ha, Units.smul_def, map_smul]
  simp

/-- Vanishing of all linear forms determines a point of vector-space projectivization. -/
theorem projectiveLine_eq_of_linear_vanishing
    (v w : ℙ K (Fin (n + 1) → K))
    (h : ∀ ℓ : (Fin (n + 1) → K) →ₗ[K] K, ℓ v.rep = 0 ↔ ℓ w.rep = 0) : v = w := by
  apply Projectivization.submodule_injective
  apply Subspace.dualAnnihilator_inj.mp
  ext ℓ
  rw [Projectivization.submodule_eq, Projectivization.submodule_eq]
  change ℓ ∈ ((Submodule.span K {v.rep}).dualAnnihilator : Set _) ↔
    ℓ ∈ ((Submodule.span K {w.rep}).dualAnnihilator : Set _)
  simpa only [Submodule.coe_dualAnnihilator_span, Set.mem_ofPred_eq,
    Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker] using h ℓ

/-- All actual linear incidence tests determine the actual rational-point morphism. -/
theorem eq_iff_linear_incidence
    (p q : Spec (CommRingCat.of K) ⟶ ProjectiveSpace K n)
    (hp : p ≫ projectiveSpaceToSpec K n = 𝟙 _)
    (hq : q ≫ projectiveSpaceToSpec K n = 𝟙 _) :
    p = q ↔ ∀ ℓ : (Fin (n + 1) → K) →ₗ[K] K,
      (linearFormPolynomialEquiv K n ℓ : ProjectiveCoordinateRing K n) ∈
        (p (IsLocalRing.closedPoint K)).asHomogeneousIdeal ↔
      (linearFormPolynomialEquiv K n ℓ : ProjectiveCoordinateRing K n) ∈
        (q (IsLocalRing.closedPoint K)).asHomogeneousIdeal := by
  constructor
  · rintro rfl ℓ
    rfl
  · intro h
    apply eq_of_pointLine_eq n p q hp hq
    apply projectiveLine_eq_of_linear_vanishing
    intro ℓ
    simpa only [pointLine_linearForm_mem_iff n p hp ℓ,
      pointLine_linearForm_mem_iff n q hq ℓ] using h ℓ

end Langlands.AlgebraicGeometry.ProjectiveSpace
