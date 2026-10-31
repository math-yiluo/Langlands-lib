import Langlands.Representation.Mirabolic.MixedProducts
import Langlands.Representation.Derivative.Homogeneity

/-!
# Minus functors and derivatives of mirabolic mixed products

Statements of Bernstein–Zelevinsky 1977, Proposition 4.13(d) and Corollary 4.14(a),
for the actual mixed products `T.rightMixedProductFunctor` (BZ77 §4.12(III)) and
`T.leftMixedProductFunctor` (BZ77 §4.12(II)), the determinant-normalized `Φ⁻`, and
the actual derivative `mirabolicDerivativeOfOrder`. This module states these
assertions and proves nothing.
-/

namespace Langlands.Derivative

open CategoryTheory GeneralLinear HarmonicAnalysis

universe uF uV

/-- BZ77 4.13(d): if the general linear factor has positive rank `k + 1`, every
nonzero invariant subspace `ω` of the right mixed product `B × A`, with `B` a smooth
representation of `P_(r+1) = mirabolic r` and `A` one of `GL_(k+1)`, has nonzero
`Φ⁻(ω)`. The product lies on `P_(k+1+r+1)`; the actual rank cast to
`P_(k+r+1+1)` makes the source of `Mirabolic.phiMinus T ψ (k + r)` match. -/
def RightMixedProductPhiMinusDetection {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (k r : ℕ)
    (B : SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier))
    (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier))
    (U : Subrepresentation ((T.rightMixedProductFunctor (k + 1) r).obj (B, A)).representation),
    U ≠ ⊥ →
      Nontrivial ((Mirabolic.phiMinus T ψ (k + r)).obj
        ((mirabolicRankCast T (Nat.add_right_comm k 1 r)).obj
          (SmoothRep.subrepresentation _ U)))

/-- BZ77 4.14(a), at the orders where `B^{(i)}` is defined: for every `GL` rank `k`
(including `k = 0`), every `P_(r+1)` and every order `1 ≤ i ≤ r + 1`, the order-`i`
derivative of the left mixed product `A × B` is naturally isomorphic, after the
actual rank cast `GL_(k+r+1-i) = GL_(k+(r+1-i))`, to the binary product
`A × B^{(i)}`. -/
def LeftMixedProductDerivativeIso {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (k r i : ℕ) (hi : 0 < i ∧ i ≤ r + 1),
    Nonempty
      (T.leftMixedProductFunctor.{uF, uV} k r ⋙
          mirabolicDerivativeOfOrder T ψ (k + r) i ⟨hi.1, by omega⟩ ⋙
            generalLinearRankCast T (show k + r + 1 - i = k + (r + 1 - i) by omega) ≅
        (𝟭 _).prod (mirabolicDerivativeOfOrder T ψ r i hi) ⋙
          T.binaryNormalizedProductFunctor k (r + 1 - i))

/-- BZ77 4.14(a) at the remaining orders, with the source convention `B^{(i)} = 0`
for `i > r + 1`: every order-`i` derivative of the left mixed product `A × B` with
`r + 1 < i ≤ k + r + 1` has zero carrier. -/
def LeftMixedProductDerivativeVanishing {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (k r i : ℕ) (hi : 0 < i ∧ i ≤ k + r + 1),
    r + 1 < i →
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier))
      (B : SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier)),
      Subsingleton ((mirabolicDerivativeOfOrder T ψ (k + r) i hi).obj
        ((T.leftMixedProductFunctor k r).obj (A, B)))

/-- BZ77 4.14(a) in full: both the natural isomorphism and the vanishing above. -/
def LeftMixedProductDerivative {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  LeftMixedProductDerivativeIso.{uF, uV} F T ∧ LeftMixedProductDerivativeVanishing.{uF, uV} F T

end Langlands.Derivative
