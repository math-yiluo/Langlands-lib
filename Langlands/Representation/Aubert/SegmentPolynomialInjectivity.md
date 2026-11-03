# Injectivity of the segment polynomial evaluation from a derivation

Module `Langlands.Representation.Aubert.SegmentPolynomialInjectivity`, namespace
`Langlands.Aubert`.

This module proves the injectivity half of
`Langlands.Aubert.SegmentPolynomialComparisonStatement` (Zelevinsky 1980,
Corollary 7.5), conditional on a ring endomorphism of the graded Grothendieck
ring that acts on segment classes like the total Bernstein–Zelevinsky
derivative. The route is internal; Zelevinsky proves 7.5 through the
classification. It combines two helper modules:
`Aubert/SegmentEndDerivation` (polynomial end derivations and the injectivity
criterion `injective_of_endExpansion`) and `Aubert/SupportGrading` (the
cuspidal-support grading and the expansion `E`).

## Statement

`segmentPolynomialEvaluation_injective_of_derivation F T hx hl D hD₁ hD₂`: let
`A = GradedGrothendieckGroup F T` with the ring structure
`gradedInductionRing F T hx hl`, and let `D : A →+* A` be a ring homomorphism
such that, for every segment `Δ` (in the universe `max uF uV`):

- `hD₁`: if `Δ.length = 1`, then `D ζ(Δ) = ζ(Δ) + gradedUnit F T`;
- `hD₂`: if `2 ≤ Δ.length`, then `D ζ(Δ) = ζ(Δ) + ζ(Δ⁻)`, where
  `Δ⁻ = ⟨Δ.base, Δ.length - 1, _⟩` has the same beginning and one element fewer.

Here `ζ(Δ) = gradedSegmentSocle F T Δ`. Then `segmentPolynomialEvaluation F T hx hl`
is injective. Zelevinsky 1980, 3.5, computes the derivatives of a segment socle;
they give exactly these formulas for the total derivative.

## Proof

Apply `SegmentEndDerivation.injective_of_endExpansion` with
`φ = segmentPolynomialEvaluation`, `E = SupportGrading.expansion F T hx hl D` and
the integer hypothesis `SupportGrading.intCast_eq_zero`. It remains to show
`E ζ(Δ) = single 0 ζ(Δ) + single (e_{Δ.last}) (φ (endTail Δ))` for every segment
`Δ`, using `φ (X Δ) = ζ(Δ)`.

- If `1 < Δ.length`: `endTail Δ = X (Δ.dropLastNonempty h)`, so
  `φ (endTail Δ) = ζ(Δ⁻)`.
  Apply `SupportGrading.expansion_segmentSocle` with `y = ζ(Δ⁻)`, `hD₂`, and
  `c` the support degree of the content of `Δ⁻`: `χ_{-1} ζ(Δ⁻) = single (-c) ζ(Δ⁻)`
  by `supportTwist_segmentSocle`, and the content of `Δ` is the content of `Δ⁻`
  plus `{Δ.last}` (`cuspidalContent_dropLastNonempty`). The segment `Δ⁻` in
  `hD₂` is written `⟨Δ.base, Δ.length - 1, _⟩`, which is `Δ.dropLastNonempty h`
  by definition.
- If `Δ.length = 1`: `endTail Δ = 1` and `φ 1 = 1 = gradedUnit F T`. Apply
  `expansion_segmentSocle` with `y = 1`, `hD₁` and `c = 0`: `χ_{-1}(1) = 1 =
  single 0 1`, and the content of `Δ` is `{Δ.last}`.

## Use

With `D` the graded total derivative ring homomorphism of
`Aubert/GradedDerivative` and its segment formulas, this gives injectivity of
`segmentPolynomialEvaluation`. The final comparison proof combines it with
surjectivity.
