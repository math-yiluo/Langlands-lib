# Products of actual Langlands heads: rank bounds and leading multiplicity

Authors: Worker 859 and Worker 597.

`Langlands.Aubert.HeadProductLeadingTermStatement.{uF, uV} F T` is a
Prop-valued target for an arbitrary p-adic field `F : PadicField.{uF} p`,
with `[Fact p.Prime]`, and supplied topology `T : F.TopologicalData`.
The field and carrier parameters `uF` and `uV` are independent. The actual
complex smooth representations have carriers in `Type (max uF uV)`.
Both ranks range over all natural numbers, including zero.

For data `dA`, `dB`, `dC` of ranks `m`, `n`, `m+n`, and actual representations
`A`, `B`, `C` of those ranks, the hypotheses are the existing weak relations
`dA.IsLanglandsQuotient A`, `dB.IsLanglandsQuotient B`, and
`dC.IsLanglandsQuotient C`. Each relation includes precedence order, the
segment-head relations for its blocks, and an actual irreducible quotient
of its induced module. In particular, all three representations are
irreducible; the stronger `IsLanglandsHead` relation is unnecessary.

Write `P = (T.binaryNormalizedProductFunctor m n).obj (A, B)` and
`a = dA.multisegment + dB.multisegment`. The target asserts three conclusions:

1. If `SmoothRep.IsSubquotient C P`, then
   `Multisegment.RankLE dC.multisegment a`.
2. If `dC.multisegment = a`, then for every `hfin : P.HasFiniteLength`,
   `SmoothRep.IrreducibleGrothendieckProof.compositionMultiplicity
   ⟨P, hfin⟩ C = 1`.
3. For any natural `l`, if `C` is an actual subquotient of `P`, every segment
   occurrence in `a` has length `l`, and `dC.multisegment ≠ a`, then some segment
   in `dC.multisegment` has length greater than `l`.

The subquotient relation uses actual invariant submodules and their quotients,
up to smooth representation isomorphism. The binary product is the existing
normalized upper-block parabolic induction functor, with its existing rank-zero
models. The multiplicity is the existing natural-valued count from an actual
composition series of the finite-length object. It is quantified over any
finite-length certificate, and the second conclusion needs no separate
subquotient hypothesis. Finite length is available from the published
`Derivative.ProductDerivativesFiniteLength.binaryProduct_hasFiniteLength`,
or its wrapper `Aubert.binaryProduct_preservesFiniteLength`, because irreducible
representations have finite length. Finite length is therefore not an additional
representation-theoretic premise.

Here `RankLE b a` is exactly the published containment-count relation: equal
cuspidal content and
`Multisegment.containmentCount I a ≤ Multisegment.containmentCount I b` for every
segment `I`. No identification with an order generated
by elementary multisegment operations is asserted. There is no positivity
hypothesis on the common length `l`. In particular `l = 0` remains covered;
segment lengths themselves are positive in the existing definition.

This is a derived internal target, extracted from Worker 597's
`HeadProductLeadingTerm` development shared with Task 5496. It packages its
three actual-representation conclusions for reuse. It is not a transcription
of a numbered literature theorem. The proposed proof route transports
socle-product coefficients through adjusted Aubert exchange and then uses
uniform-length rigidity of the published rank order. Those ingredients are
proof obligations or published results to be supplied in a separate proof;
none is a hypothesis of this proposition. This module imports the public
definitions of Langlands data, rank order, the binary normalized product, and
actual composition multiplicity, and proves none of the three assertions.
