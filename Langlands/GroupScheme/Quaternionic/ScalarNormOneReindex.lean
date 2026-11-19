import Langlands.GroupScheme.Dynamic.UnitriangularEmbedding
import Langlands.GroupScheme.Quaternionic.ScalarNormOnePoints
import Langlands.GroupScheme.Quaternionic.RadicalFreeQuadratic
import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Coordinate reindexing for scalar norm-one isometry groups -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.Quaternionic.ScalarNormOnePoints

open FirstKindInvolution
open OrthogonalMatrix (IsAlt)

variable {K : Type u} [Field K] {i j : Type} [Fintype i] [DecidableEq i]
  [Fintype j] [DecidableEq j] (e : i ≃ j) (Q : Matrix i i K)

/-- The scalar quadratic form given by renumbering the representative matrix. -/
def reindexForm : (scalar K).QuadraticForms j := Submodule.Quotient.mk (Matrix.reindex e e Q)

omit [Fintype i] [DecidableEq i] [Fintype j] [DecidableEq j] in
private theorem isAlt_reindex {R : Type*} [CommRing R] {M : Matrix i i R} (h : IsAlt M) :
    IsAlt (Matrix.reindex e e M) := by
  obtain ⟨U, rfl⟩ := h
  exact ⟨Matrix.reindex e e U, rfl⟩

omit [Fintype i] [DecidableEq i] [Fintype j] [DecidableEq j] in
private theorem isAlt_reindex_iff {R : Type*} [CommRing R] (M : Matrix i i R) :
    IsAlt (Matrix.reindex e e M) ↔ IsAlt M := by
  refine ⟨fun h => ?_, isAlt_reindex e⟩
  have h' := isAlt_reindex e.symm h
  change IsAlt ((Matrix.reindex e e).symm ((Matrix.reindex e e) M)) at h'
  simpa only [Equiv.symm_apply_apply] using h'

variable [Nonempty i] [Nonempty j]

local notation "q" => (Submodule.Quotient.mk Q : QuadraticForms (scalar K) i)

private theorem reindex_mem_range_iff (T : Over (Spec (CommRingCat.of K)))
    (g : GL i Γ(T.left, ⊤)) :
    GeneralLinear.matrixReindex e Γ(T.left, ⊤) g ∈ (matrix (reindexForm e Q) T).range ↔
      g ∈ (matrix q T).range := by
  rw [mem_range_matrix_iff (reindexForm e Q) (Matrix.reindex e e Q) rfl,
    mem_range_matrix_iff q Q rfl]
  let f : K →+* Γ(T.left, ⊤) := algebraMap K ((algΓ (CommRingCat.of K)).obj T).unop
  let D := Q.map f
  let r := Matrix.reindexRingEquiv Γ(T.left, ⊤) e
  change (IsAlt (r g.val * r D * (r g.val)ᵀ - r D) ∧ (Matrix.reindex e e g.val).det = 1) ↔
    IsAlt (g.val * D * g.valᵀ - D) ∧ g.val.det = 1
  have ht : (r g.val)ᵀ = r g.valᵀ := rfl
  rw [ht, ← _root_.map_mul, ← _root_.map_mul, ← _root_.map_sub, Matrix.det_reindex_self]
  exact and_congr_left' (isAlt_reindex_iff e _)

private def reindexPointsEquiv (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ ((scalar K).normOneIsometryGroup q).X) ≃*
      (T ⟶ ((scalar K).normOneIsometryGroup (reindexForm e Q)).X) :=
  pointsEquiv q (reindexForm e Q) T (GeneralLinear.matrixReindex e Γ(T.left, ⊤)) (reindex_mem_range_iff e Q T)

private theorem matrix_reindexPointsEquiv (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ ((scalar K).normOneIsometryGroup q).X) :
    matrix (reindexForm e Q) T (reindexPointsEquiv e Q T x) =
      GeneralLinear.matrixReindex e Γ(T.left, ⊤) (matrix q T x) :=
  matrix_pointsEquiv q (reindexForm e Q) T (GeneralLinear.matrixReindex e Γ(T.left, ⊤)) (reindex_mem_range_iff e Q T) x

/-- Reindexing gives an actual isomorphism of the two scalar norm-one groups. -/
def reindexGroupIso : (scalar K).normOneIsometryGroup q ≅
    (scalar K).normOneIsometryGroup (reindexForm e Q) :=
  isoOfPoints (reindexPointsEquiv e Q) (by
    intro T T' b x
    apply matrix_injective
    rw [matrix_naturality, matrix_reindexPointsEquiv, matrix_reindexPointsEquiv, matrix_naturality]
    rfl)

omit [DecidableEq i] [DecidableEq j] [Nonempty i] [Nonempty j] in
private theorem sesqForm_reindex (x y : j → K) :
    (scalar K).sesqForm (Matrix.reindex e e Q) x y = (scalar K).sesqForm Q (x ∘ e) (y ∘ e) := by
  simp only [scalar_sesqForm, Matrix.reindex_apply, Matrix.submatrix_apply, Function.comp_apply]
  apply Fintype.sum_equiv e.symm
  intro a
  apply Fintype.sum_equiv e.symm
  intro b
  simp

omit [Nonempty i] [Nonempty j] in
/-- Zero quadratic radical is preserved by the coordinate reindexing. -/
theorem radicalFree_reindexForm (hq : (scalar K).IsRadicalFreeQuadratic q) :
    (scalar K).IsRadicalFreeQuadratic (reindexForm e Q) := by
  intro x hx hpol
  have hx' : (scalar K).quadraticValue (x ∘ e) q = 0 := by
    rw [scalar_quadraticValue_mk_eq_zero_iff, ← scalar_sesqForm, ← sesqForm_reindex e Q x x]
    simpa only [reindexForm, scalar_quadraticValue_mk_eq_zero_iff, scalar_sesqForm] using hx
  have hp (y : i → K) : (scalar K).sesqForm ((scalar K).polar q) (x ∘ e) y = 0 := by
    have h := hpol (y ∘ e.symm)
    change (scalar K).sesqForm (Matrix.reindex e e ((scalar K).polar q)) x (y ∘ e.symm) = 0 at h
    have hy : (y ∘ e.symm) ∘ e = y := funext fun a => congrArg y (e.symm_apply_apply a)
    rwa [sesqForm_reindex, hy] at h
  have hzero := hq (x ∘ e) hx' hp
  funext a
  simpa only [Function.comp_apply, Equiv.apply_symm_apply, Pi.zero_apply] using congrFun hzero (e.symm a)

omit [DecidableEq i] [Nonempty i] in
/-- The nullity of multiplication on row vectors is the coordinate count minus matrix rank. -/
theorem finrank_ker_vecMulLinear (M : Matrix i i K) :
    Module.finrank K (LinearMap.ker M.vecMulLinear) = Fintype.card i - M.rank := by
  have hn := LinearMap.finrank_range_add_finrank_ker M.vecMulLinear
  have hr : Module.finrank K (LinearMap.range M.vecMulLinear) = M.rank := by
    rw [← Matrix.rank_transpose M, Matrix.rank, ← Matrix.vecMulLinear_transpose,
      Matrix.transpose_transpose]
  rw [hr, Module.finrank_fintype_fun_eq_card] at hn
  omega

omit [Nonempty i] [Nonempty j] in
/-- Coordinate reindexing preserves the polar kernel dimension. -/
theorem finrank_polarKer_reindexForm :
    Module.finrank K (LinearMap.ker ((scalar K).polar (reindexForm e Q)).vecMulLinear) =
      Module.finrank K (LinearMap.ker ((scalar K).polar q).vecMulLinear) := by
  have hQ : (scalar K).polar (reindexForm e Q) = Matrix.reindex e e ((scalar K).polar q) := rfl
  rw [hQ, finrank_ker_vecMulLinear, finrank_ker_vecMulLinear, Matrix.rank_reindex, Fintype.card_congr e]

end Langlands.GroupScheme.Quaternionic.ScalarNormOnePoints
