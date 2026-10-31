import Langlands.Representation.Derivative.Iteration
import Langlands.Representation.Derivative.Partial
import Langlands.Representation.Jacquet.Parabolic
import Langlands.Representation.Shahidi.TwoBlocks

/-!
# Positive two-block Jacquet-to-derivative comparison

Zelevinsky (1980), Proposition 3.7(b), identifies the ordinary `m`-th derivative of a
representation of `GL_(k+m)` with the partial derivative of its normalized Jacquet
module for the standard parabolic of shape `(k,m)`. This module states the clause for
positive block sizes `k` and `m`, using the actual normalized Jacquet functor, the
actual Levi-to-product equivalence, the partial derivative and the ordinary derivative
of the Library. It does not prove the comparison.
-/

open CategoryTheory

namespace Langlands.Derivative

open HarmonicAnalysis

universe uF uV

/-- The normalized Jacquet functor for the positive ordered standard parabolic of
shape `(k,m)`, followed by restriction along the inverse of the actual continuous
equivalence between its Levi subgroup and `GL_k × GL_m`. Carriers and linear maps are
those of the normalized Jacquet module. -/
noncomputable def positiveTwoBlockNormalizedJacquet {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
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
def PartialDerivativeJacquetComparisonStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k m : ℕ) (hk : 0 < k)
    (hm : 0 < m),
    Nonempty
      (generalLinearDerivative.{uF, uV} T ψ (k + m) m (Nat.le_add_left m k) ⋙
          generalLinearRankCast.{uF, uV} T (Nat.add_sub_cancel k m) ≅
        positiveTwoBlockNormalizedJacquet.{uF, uV} T k m hk hm ⋙
          partialDerivative.{uF, uV} T ψ k m)

end Langlands.Derivative
