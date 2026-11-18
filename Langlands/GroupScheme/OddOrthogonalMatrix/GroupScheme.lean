import Langlands.GroupScheme.OddOrthogonalMatrix.Form
import Langlands.GroupScheme.Quaternionic.ScalarNormOneSplitRank

/-! # The actual norm-one group of the split odd quadratic form -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Quaternionic.FirstKindInvolution

variable {K : Type u} {D : Type v} [Field K] [DivisionRing D] [Algebra K D]
  {σ : FirstKindInvolution K D} {n : Type} [Fintype n] [DecidableEq n]
  {q : σ.QuadraticForms n} {I : Type*} [Fintype I] [DecidableEq I] {x y : I → n → D}

/-- The two halves of a hyperbolic family are jointly linearly independent. -/
theorem IsHyperbolicFamily.linearIndependent_sum (h : σ.IsHyperbolicFamily q x y) :
    LinearIndependent D (Sum.elim x y) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hl : ∀ j, c (Sum.inl j) = 0 := by
    intro j
    have h' := congrArg (fun z => σ.sesqForm (σ.polar q) z (y j)) hc
    rw [sesqForm_sum_smul_left] at h'
    simpa [Fintype.sum_sum_type, h.polar_left_right, h.polar_right_right] using h'
  have hr : ∀ j, c (Sum.inr j) = 0 := by
    intro j
    have h' := congrArg (fun z => σ.sesqForm (σ.polar q) z (x j)) hc
    rw [sesqForm_sum_smul_left] at h'
    simpa [Fintype.sum_sum_type, h.polar_left_left, h.polar_right_left] using h'
  rcases i with i | i
  · exact hl i
  · exact hr i

/-- A hyperbolic family has at most half the ambient dimension. -/
theorem IsHyperbolicFamily.two_mul_card_le (h : σ.IsHyperbolicFamily q x y) :
    2 * Fintype.card I ≤ Fintype.card n := by
  have h' := h.linearIndependent_sum.fintype_card_le_finrank
  simpa only [Fintype.card_sum, Module.finrank_fintype_fun_eq_card, two_mul] using h'

/-- Zero quadratic radical bounds twice the Witt index by the ambient dimension,
even when the polar radical is nonzero. -/
theorem two_mul_quadraticWittIndex_le_card_of_radicalFree
    (hq : σ.IsRadicalFreeQuadratic q) :
    2 * σ.quadraticWittIndex q ≤ Fintype.card n := by
  obtain ⟨x, y, h⟩ := exists_isHyperbolicFamily_of_radicalFree q hq
  simpa only [Fintype.card_fin] using h.two_mul_card_le

end Quaternionic.FirstKindInvolution

namespace OddOrthogonalMatrix

open Quaternionic.FirstKindInvolution

variable (l : Type) [Fintype l] [DecidableEq l] (K : Type u) [Field K]

/-- The actual determinant-one isometry group of the split odd quadratic form. -/
def groupScheme : GroupScheme (Spec (CommRingCat.of K)) :=
  (scalar K).normOneIsometryGroup (form l K)

instance isAffineHom_groupScheme : IsAffineHom (groupScheme l K).X.hom :=
  inferInstanceAs (IsAffineHom ((scalar K).normOneIsometryGroup (form l K)).X.hom)

instance locallyOfFiniteType_groupScheme : LocallyOfFiniteType (groupScheme l K).X.hom :=
  inferInstanceAs (LocallyOfFiniteType ((scalar K).normOneIsometryGroup (form l K)).X.hom)

/-- The standard left hyperbolic coordinate vectors. -/
def leftVector (i : l) : Index l → K := Pi.single (Sum.inr (Sum.inl i)) 1

/-- The standard right hyperbolic coordinate vectors. -/
def rightVector (i : l) : Index l → K := Pi.single (Sum.inr (Sum.inr i)) 1

/-- The coordinate hyperbolic pairs of the split odd quadratic form. -/
theorem standardFamily :
    (scalar K).IsHyperbolicFamily (form l K) (leftVector l K) (rightVector l K) := by
  constructor
  · intro i
    rw [quadraticValue_form_eq_zero_iff]
    simp [leftVector, Pi.single_apply]
  · intro i
    rw [quadraticValue_form_eq_zero_iff]
    simp [rightVector, Pi.single_apply]
  · intro i j
    simp [leftVector, rightVector, scalar_sesqForm, polar_form, polarMatrix,
      OrthogonalMatrix.polarMatrix, Pi.single_apply, Matrix.one_apply]
  · intro i j
    simp [leftVector, scalar_sesqForm, polar_form, polarMatrix,
      OrthogonalMatrix.polarMatrix, Pi.single_apply]
  · intro i j
    simp [rightVector, scalar_sesqForm, polar_form, polarMatrix,
      OrthogonalMatrix.polarMatrix, Pi.single_apply]

/-- The standard closed split torus in the actual norm-one isometry group. -/
def torus : splitTorus (Spec (CommRingCat.of K)) (ULift.{u} l) ⟶ groupScheme l K :=
  ((standardFamily l K).comp (fun i : ULift.{u} l => i.down) ULift.down_injective).normOneTorus

/-- The standard split torus is a closed subgroup. -/
theorem isClosedSubgroup_torus : IsClosedSubgroup (torus l K) :=
  ((standardFamily l K).comp (fun i : ULift.{u} l => i.down)
    ULift.down_injective).isClosedSubgroup_normOneTorus

/-- Inclusion of the left totally singular coordinate subspace. -/
def leftEmbedding : (l → K) →ₗ[K] (Index l → K) where
  toFun v := Sum.elim 0 (Sum.elim v 0)
  map_add' v w := by
    funext i
    rcases i with i | i
    · simp
    · rcases i with i | i <;> simp
  map_smul' a v := by
    funext i
    rcases i with i | i
    · simp
    · rcases i with i | i <;> simp

variable {l K}

omit [Fintype l] [DecidableEq l] in
/-- The left coordinate embedding is injective. -/
theorem leftEmbedding_injective : Function.Injective (leftEmbedding l K) := by
  intro v w h
  funext i
  exact congrFun h (Sum.inr (Sum.inl i))

/-- The left coordinate subspace is totally singular. -/
theorem isTotallySingular_range_leftEmbedding :
    (scalar K).IsTotallySingular (form l K) (LinearMap.range (leftEmbedding l K)) := by
  rintro _ ⟨v, rfl⟩
  rw [quadraticValue_form_eq_zero_iff]
  simp [leftEmbedding]

/-- The quadratic Witt index of the split odd form is the number of hyperbolic pairs. -/
theorem quadraticWittIndex_form : (scalar K).quadraticWittIndex (form l K) = Fintype.card l := by
  apply le_antisymm
  · have h := two_mul_quadraticWittIndex_le_card_of_radicalFree
      (radicalFree_form (l := l) (K := K))
    simp only [Index, Fintype.card_sum, Fintype.card_unique] at h
    omega
  · have h := isTotallySingular_range_leftEmbedding (l := l) (K := K)
    have h' := h.finrank_le_quadraticWittIndex
    rwa [LinearMap.finrank_range_of_inj leftEmbedding_injective,
      Module.finrank_fintype_fun_eq_card] at h'

/-- The actual norm-one group of the split odd form has split rank `|l|`. -/
theorem splitRank_groupScheme : splitRank (groupScheme l K) = (Fintype.card l : ℕ∞) := by
  rw [groupScheme, splitRank_normOneIsometryGroup_eq _ radicalFree_form,
    quadraticWittIndex_form]

end OddOrthogonalMatrix

end Langlands.GroupScheme
