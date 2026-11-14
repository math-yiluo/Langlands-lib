import Langlands.AllFieldBZ.Representation.Derivative.Iteration
import Langlands.AllFieldBZ.Representation.Derivative.Partial
import Langlands.AllFieldBZ.Representation.Jacquet.Parabolic
import Langlands.AllFieldBZ.Representation.Shahidi.TwoBlocks
import Langlands.Representation.Derivative.PartialDerivativeJacquetComparisonStatement

/-!
# All-field port of `Langlands.Representation.Derivative.PartialDerivativeJacquetComparisonStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.PartialDerivativeJacquetComparisonStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
open CategoryTheory
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding PartialDerivativeJacquetComparisonStatement generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap mirabolicDerivative mirabolicDerivative_eq mirabolicDerivative_succ mirabolicDerivative_zero partialDerivative partialDerivativeMk partialDerivativeMk_surjective partialDerivativeMk_unipotent partialDerivative_action_mk partialDerivative_map_mk phiMinusIterate phiMinusIterate_succ phiMinusIterate_zero positiveTwoBlockNormalizedJacquet
open Langlands.HarmonicAnalysis
universe uF uV

/-- The normalized Jacquet functor for the positive ordered standard parabolic of
shape `(k,m)`, followed by restriction along the inverse of the actual continuous
equivalence between its Levi subgroup and `GL_k × GL_m`. Carriers and linear maps are
those of the normalized Jacquet module. -/
noncomputable def positiveTwoBlockNormalizedJacquet {F : LocalFieldPackage.{uF}}
    (T : F.TopologicalData) (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + m) F.Carrier) ⥤
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier × GeneralLinear m F.Carrier) :=
  letI := T.topology
  T.normalizedJacquetFunctor (Shahidi.twoBlocks k m hk hm) ⋙
    Mirabolic.continuousPullbackFunctor
      (Shahidi.twoBlockLeviContinuousEquiv hk hm F.Carrier).symm.toMonoidHom
      (Shahidi.twoBlockLeviContinuousEquiv hk hm F.Carrier).symm.continuous

/-- Zelevinsky (1980), Proposition 3.7(b), for positive block sizes: for every
unitary additive character `ψ` and all `k m > 0`, the ordinary `m`-th derivative on
`GL_(k+m)`, followed by the rank cast `k + m - m = k`, is naturally isomorphic to the
normalized `(k,m)` Jacquet functor transported to `GL_k × GL_m`, followed by the
partial derivative for the same character. -/
def PartialDerivativeJacquetComparisonStatement (F : LocalFieldPackage.{uF}) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k m : ℕ) (hk : 0 < k)
    (hm : 0 < m),
    Nonempty
      (generalLinearDerivative.{uF, uV} T ψ (k + m) m (Nat.le_add_left m k) ⋙
          generalLinearRankCast.{uF, uV} T (Nat.add_sub_cancel k m) ≅
        positiveTwoBlockNormalizedJacquet.{uF, uV} T k m hk hm ⋙
          partialDerivative.{uF, uV} T ψ k m)

end Langlands.AllFieldBZ.Derivative
