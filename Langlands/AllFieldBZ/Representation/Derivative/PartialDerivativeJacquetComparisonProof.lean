import Langlands.AllFieldBZ.Representation.Derivative.PartialDerivativeJacquetLHS
import Langlands.AllFieldBZ.Representation.Derivative.PartialDerivativeJacquetRHSComparison
import Langlands.Representation.Derivative.PartialDerivativeJacquetComparisonProof

/-!
# All-field port of `Langlands.Representation.Derivative.PartialDerivativeJacquetComparisonProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.PartialDerivativeJacquetComparisonProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding PartialDerivativeJacquetComparisonStatement generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap mirabolicDerivative mirabolicDerivative_eq mirabolicDerivative_succ mirabolicDerivative_zero partialDerivative partialDerivativeJacquetComparison partialDerivativeMk partialDerivativeMk_surjective partialDerivativeMk_unipotent partialDerivative_action_mk partialDerivative_map_mk phiMinusIterate phiMinusIterate_succ phiMinusIterate_zero positiveTwoBlockNormalizedJacquet
universe uF uV

variable {F : LocalFieldPackage.{uF}}

namespace PartialJacquetComparison
open Langlands.Derivative.PartialJacquetComparison hiding componentEquiv componentLinearEquiv componentLinearEquiv_mk componentLinearEquiv_natural derivative_add_succ lhs_natural positiveIso
/-- The LHS quotient equivalence respects every actual mapped intertwiner. -/
theorem lhs_natural (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (k j : ℕ) :
    letI := T.topology
    ∀ {A B : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + j + 1) F.Carrier)}
      (f : A ⟶ B) (x : (generalLinearDerivativePositive T ψ k j).obj A),
      Jacquet.Localization.mapLinear (PartialLocalization.partialUpper k (j + 1) F.Carrier)
          (PartialLocalization.character ψ.complex k (j + 1)) (SmoothRep.hom f)
          (JacquetLHS.generalLinearLinearEquiv T ψ k j A x) =
        JacquetLHS.generalLinearLinearEquiv T ψ k j B
          (SmoothRep.hom ((generalLinearDerivativePositive T ψ k j).map f) x) := by
  let := T.topology
  intro A B f x
  obtain ⟨v, rfl⟩ := JacquetNormalization.generalLinearDerivativePositiveMk_surjective
    T ψ k j A x
  rw [JacquetLHS.generalLinearLinearEquiv_mk,
    JacquetNormalization.generalLinearDerivativePositiveMk_natural,
    JacquetLHS.generalLinearLinearEquiv_mk]
  rfl

/-- The two actual quotient equivalences give an inverse-equipped carrier map. -/
def componentLinearEquiv (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k j : ℕ) (hk : 0 < k) :
    letI := T.topology
    ∀ A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + (j + 1)) F.Carrier),
      (generalLinearDerivativePositive T ψ k j).obj A ≃ₗ[ℂ]
        ((positiveTwoBlockNormalizedJacquet T k (j + 1) hk (Nat.succ_pos j)) ⋙
          partialDerivative T ψ k (j + 1)).obj A := by
  letI := T.topology
  intro A
  exact (JacquetLHS.generalLinearLinearEquiv T ψ k j A).trans
    (JacquetRHSComparison.linearEquiv T ψ k (j + 1) hk (Nat.succ_pos j) A).symm

@[simp] theorem componentLinearEquiv_mk (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k j : ℕ) (hk : 0 < k) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + (j + 1)) F.Carrier)) (v : A),
      componentLinearEquiv T ψ k j hk A
        (JacquetNormalization.generalLinearDerivativePositiveMk T ψ k j A v) =
        JacquetRHS.rhsMk T ψ k (j + 1) hk (Nat.succ_pos j) A v := by
  let := T.topology
  intro A v
  change (JacquetRHSComparison.linearEquiv T ψ k (j + 1) hk (Nat.succ_pos j) A).symm
    (JacquetLHS.generalLinearLinearEquiv T ψ k j A
      (JacquetNormalization.generalLinearDerivativePositiveMk T ψ k j A v)) = _
  rw [JacquetLHS.generalLinearLinearEquiv_mk, JacquetRHSComparison.linearEquiv_symm_mk]

/-- The component map intertwines the actual normalized GL_k actions. -/
def componentEquiv (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k j : ℕ) (hk : 0 < k) :
    letI := T.topology
    ∀ A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + (j + 1)) F.Carrier),
      ((generalLinearDerivativePositive T ψ k j).obj A).representation.Equiv
        (((positiveTwoBlockNormalizedJacquet T k (j + 1) hk (Nat.succ_pos j)) ⋙
          partialDerivative T ψ k (j + 1)).obj A).representation := by
  letI := T.topology
  intro A
  refine Representation.Equiv.mk (componentLinearEquiv T ψ k j hk A) ?_
  intro g
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := JacquetNormalization.generalLinearDerivativePositiveMk_surjective
    T ψ k j A x
  change componentLinearEquiv T ψ k j hk A
    (((generalLinearDerivativePositive T ψ k j).obj A).representation g
      (JacquetNormalization.generalLinearDerivativePositiveMk T ψ k j A v)) =
    (((positiveTwoBlockNormalizedJacquet T k (j + 1) hk (Nat.succ_pos j)) ⋙
      partialDerivative T ψ k (j + 1)).obj A).representation g
        (componentLinearEquiv T ψ k j hk A
          (JacquetNormalization.generalLinearDerivativePositiveMk T ψ k j A v))
  rw [JacquetNormalization.generalLinearDerivativePositive_action_mk_eq_inverseHalf
    T ψ k j hk, map_smul, componentLinearEquiv_mk, componentLinearEquiv_mk,
    JacquetRHS.rhs_action_mk]
  rfl

/-- Naturality covers all quotient vectors and every actual ambient intertwiner. -/
theorem componentLinearEquiv_natural (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k j : ℕ) (hk : 0 < k) :
    letI := T.topology
    ∀ {A B : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + (j + 1)) F.Carrier)}
      (f : A ⟶ B) (x : (generalLinearDerivativePositive T ψ k j).obj A),
      SmoothRep.hom (((positiveTwoBlockNormalizedJacquet T k (j + 1) hk (Nat.succ_pos j)) ⋙
          partialDerivative T ψ k (j + 1)).map f)
          (componentLinearEquiv T ψ k j hk A x) =
        componentLinearEquiv T ψ k j hk B
          (SmoothRep.hom ((generalLinearDerivativePositive T ψ k j).map f) x) := by
  let := T.topology
  intro A B f x
  change SmoothRep.hom (((positiveTwoBlockNormalizedJacquet T k (j + 1) hk (Nat.succ_pos j)) ⋙
    partialDerivative T ψ k (j + 1)).map f)
      ((JacquetRHSComparison.linearEquiv T ψ k (j + 1) hk (Nat.succ_pos j) A).symm
        (JacquetLHS.generalLinearLinearEquiv T ψ k j A x)) = _
  rw [JacquetRHSComparison.linearEquiv_symm_natural, lhs_natural]
  rfl

/-- A genuine natural isomorphism of the unchanged positive-order functors. -/
def positiveIso (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k j : ℕ) (hk : 0 < k) :
    letI := T.topology
    generalLinearDerivativePositive.{uF,uV} T ψ k j ≅
      positiveTwoBlockNormalizedJacquet T k (j + 1) hk (Nat.succ_pos j) ⋙
        partialDerivative T ψ k (j + 1) := by
  letI := T.topology
  refine NatIso.ofComponents (fun A => SmoothRep.mkIso (componentEquiv T ψ k j hk A)) ?_
  intro A B f
  apply ObjectProperty.hom_ext
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact (componentLinearEquiv_natural T ψ k j hk f x).symm

/-- Cancel the two rank transports in the actual derivative at positive order. -/
theorem derivative_add_succ (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (k j : ℕ) :
    letI := T.topology
    generalLinearDerivative.{uF,uV} T ψ (k + (j + 1)) (j + 1)
        (Nat.le_add_left (j + 1) k) ⋙
      generalLinearRankCast T (Nat.add_sub_cancel k (j + 1)) =
        generalLinearDerivativePositive T ψ k j := by
  let := T.topology
  have key : ∀ (r : ℕ) (h : r = k) (h₁ : k + (j + 1) = r + j + 1),
      (generalLinearRankCast.{uF,uV} T h₁ ⋙ generalLinearDerivativePositive T ψ r j) ⋙
        generalLinearRankCast T h = generalLinearDerivativePositive T ψ k j := by
    intro r h h₁
    subst r
    rw [generalLinearRankCast_refl, generalLinearRankCast_refl,
      Functor.id_comp, Functor.comp_id]
  exact key (k + (j + 1) - (j + 1)) (Nat.add_sub_cancel k (j + 1))
    (rank_eq_of_succ_le (Nat.le_add_left (j + 1) k))

end PartialJacquetComparison
/-- Zelevinsky 3.7(b) for the actual positive two-block functors and supplied topology. -/
theorem partialDerivativeJacquetComparison (F : LocalFieldPackage.{uF}) (T : F.TopologicalData) :
    PartialDerivativeJacquetComparisonStatement.{uF,uV} F T := by
  let := T.topology
  intro ψ k m hk hm
  cases m with
  | zero => exact (Nat.lt_irrefl 0 hm).elim
  | succ j =>
    rw [PartialJacquetComparison.derivative_add_succ]
    exact ⟨PartialJacquetComparison.positiveIso T ψ k j hk⟩

end Langlands.AllFieldBZ.Derivative
