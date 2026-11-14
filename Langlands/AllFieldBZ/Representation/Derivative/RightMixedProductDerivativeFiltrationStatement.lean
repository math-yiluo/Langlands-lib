import Langlands.AllFieldBZ.Representation.Derivative.Homogeneity
import Langlands.AllFieldBZ.Representation.Mirabolic.MixedProducts
import Langlands.Representation.Derivative.RightMixedProductDerivativeFiltrationStatement

/-!
# All-field port of `Langlands.Representation.Derivative.RightMixedProductDerivativeFiltrationStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.RightMixedProductDerivativeFiltrationStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding HasNonzeroDerivative IsHomogeneous RightMixedProductDerivativeFiltrationStatement generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap hasNonzeroDerivative_iff isHomogeneous_of_subsingleton le_level_of_hasNonzeroDerivative level level_eq_iff level_eq_zero_iff level_eq_zero_of_subsingleton level_le mirabolicDerivative mirabolicDerivativeOfOrder mirabolicDerivativeOfOrder_eq mirabolicDerivativeOfOrder_obj mirabolicDerivativeOfOrder_obj_subsingleton mirabolicDerivativeOfOrder_one mirabolicDerivativeOfOrder_top mirabolicDerivative_eq mirabolicDerivative_obj_subsingleton mirabolicDerivative_succ mirabolicDerivative_zero mirabolicRankCast mirabolicRankCast_obj_subsingleton mirabolicRankCast_refl phiMinusIterate phiMinusIterate_obj_subsingleton phiMinusIterate_succ phiMinusIterate_zero rightMixedDerivativePiece rightMixedDerivativeSource
open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis
universe uF uV

variable {F : LocalFieldPackage.{uF}}

/-- The literal derivative of the published right mixed product, viewed in `Rep`. -/
def rightMixedDerivativeSource (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k r d : ℕ) (hd : 0 < d ∧ d ≤ (k + r) + 1) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ⥤
      Rep.{max uF uV} ℂ (GeneralLinear ((k + r) + 1 - d) F.Carrier) := by
  letI := T.topology
  exact T.rightMixedProductFunctor k r ⋙
    mirabolicDerivativeOfOrder T ψ (k + r) d hd ⋙ SmoothRep.toRep

/-- A feasible grade in the order `B^(j) × A^(t)`, with smooth rank transport. -/
def rightMixedDerivativePiece (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k r d : ℕ) (x : RightMixedDerivativeIndex k r d) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ⥤
      Rep.{max uF uV} ℂ (GeneralLinear ((k + r) + 1 - d) F.Carrier) := by
  letI := T.topology
  exact (mirabolicDerivativeOfOrder T ψ r x.val.1
        (rightMixedDerivativeIndices_left_bound x.property)).prod
      (generalLinearDerivative T ψ k x.val.2
        (rightMixedDerivativeIndices_right_le x.property)) ⋙
    T.binaryNormalizedProductFunctor (r + 1 - x.val.1) (k - x.val.2) ⋙
    generalLinearRankCast T (rightMixedDerivativeIndices_rank x.property) ⋙ SmoothRep.toRep

variable (F) in
/-- BZ77 4.14(b) with an actual finite natural filtration and every feasible
order pair exactly once, including all rank-zero and top-order boundaries. -/
def RightMixedProductDerivativeFiltrationStatement (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
    (k r d : ℕ) (hd : 0 < d ∧ d ≤ (k + r) + 1),
    ∃ e : Fin (rightMixedDerivativeIndices k r d).card ≃ RightMixedDerivativeIndex k r d,
      IsGluedFrom (rightMixedDerivativeSource.{uF, uV} T ψ k r d hd)
        (fun i => rightMixedDerivativePiece T ψ k r d (e i))

set_option maxHeartbeats 1000000 in
/-- Extract the actual filtration, its complete grade enumeration, and natural
graded isomorphisms from a supplied assertion. This does not prove the assertion. -/
theorem RightMixedProductDerivativeFiltrationStatement.filtration
    (T : F.TopologicalData)
    (h : RightMixedProductDerivativeFiltrationStatement.{uF, uV} F T)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k r d : ℕ) (hd : 0 < d ∧ d ≤ (k + r) + 1) :
    letI := T.topology
    ∃ s : RepFunctorFiltration (rightMixedDerivativeSource.{uF, uV} T ψ k r d hd)
        (rightMixedDerivativeIndices k r d).card,
      ∃ e : Fin (rightMixedDerivativeIndices k r d).card ≃ RightMixedDerivativeIndex k r d,
        ∀ i, Nonempty (s.graded i ≅ rightMixedDerivativePiece T ψ k r d (e i)) := by
  let _ := T.topology
  obtain ⟨e, σ, s, hs⟩ := h ψ k r d hd
  exact ⟨s, σ.trans e, hs⟩

end Langlands.AllFieldBZ.Derivative
