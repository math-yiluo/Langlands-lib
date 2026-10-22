# Simultaneous local invariants and fundamental-class targets

This proposition pair is authored by Worker 49, with invariant/comparison
interface design by Worker 42.
`LocalRelativeClassFormationStatement` quantifies every prime `p` and
asserts the existence of one data-only invariant family satisfying the
arithmetic normalization, finite-level class-formation axioms,
conjugacy and finite corestriction compatibility, unique fundamental classes with exact order and
generation, and their inflation, restriction, corestriction, and conjugacy laws.
The family ranges over all `PadicField.{u} p` and all finite Galois
extensions represented in the arbitrary common universe `u`.
No invariant, fundamental class, class-formation record, or reciprocity
isomorphism is a hypothesis of this existence claim.

`LocalCompatibleClassFormationStatement` strengthens that local
existence target by requiring the **same** existential invariant family
to satisfy `ContinuousInvariantProperties`. In addition to every finite
relative property above, it therefore asserts continuous absolute H¹
vanishing, bijectivity of each absolute invariant map onto the actual
`ℚ/ℤ`, the degree formula for actual absolute restriction, and the
finite-stage/absolute commuting diagram from `FiniteInvariantCompatibility`.
It also asserts `TateIsomorphisms` for the same family: every fundamental
class induces a bijection in every integer Tate degree. It additionally
asserts `PositiveTateInflation` for this family. The separately
conjoined `FundamentalClasses` property ensures existence and uniqueness,
so the cup condition is not vacuous.
It does not quantify separate, potentially unrelated families for the
two cohomology models.

Explicitly, for a finite Galois intermediate field `E` of the actual
algebraic closure of `F` and every ordinary relative H² class `x`, the
diagram asserts `inv_F(closureInflation x) = inv_(E/F)(x)`.
The map uses the proved ordinary/continuous finite comparison and genuine
continuous inflation. The theorem `closureCompatibility_iff` identifies
this predicate with the continuous finite-stage formulation. No inverse
comparison is supplied as an assumption. The whole target ranges over an
arbitrary common carrier universe `u`, including the actual closure and
its intermediate fields, for every prime. It imposes no extra extension
degree, unramifiedness, or class-formation assumption. Arithmetic
normalization is tested on unramified cyclic coordinates inside the
normalization property without restricting the other clauses.

The finite invariant corestriction clause says
`inv_F(Cor(c)) = inv_E(c)`. Fundamental classes satisfy
`Cor(u[M/E]) = [E:F] u[M/F]` for every quantified finite Galois top
extension. Both use the published positive-degree `relativeCorestriction`.
The Tate clause uses `relativeTateCup` with the fundamental class on the
left, and covers every `n : ℤ`. Its degree-minus-two norm-quotient target
is identified in the imported `TateCup` and `TateNormQuotient` modules.

The positive Tate inflation clause quantifies every finite Galois tower
`F ⊆ L ⊆ M`, every pair of fundamental classes `c` for `L/F` and `d` for
`M/F`, every positive natural degree `n`, and every integral Tate class
`x` in degree `n`. Its equation is
`Inf(c ∪ x) = [M:L] • (d ∪ Inf(x))`.
The two invariant maps specifying `c` and `d` are `I.relative F L` and
`I.relative F M` from the same existential family, whose fundamental
classes exist by the conjoined property. Both inflation maps are the
published transports of ordinary inflation through the proved positive
Tate comparisons. Unit-valued inflation has degree `n + 2`; integral
inflation has degree `n`. The clause does not extend Tate inflation to
zero or negative degrees.

`RelativeFundamentalClassConsequencesStatement` is the accompanying
generic implication: if the raw invariant family satisfies the honest
finite-level class-formation axiom predicate and conjugacy compatibility,
then its fundamental classes exist uniquely, have the specified order,
generate the actual relative cohomology groups, and satisfy the four
genuine-map formulas, including fundamental-class corestriction. This conditional implication
does not replace the independent local existence target.

All three declarations are definitions returning `Prop`. No theorem proof,
choice-based constructor, or axiom has been introduced.
The definitions in `ClassFormation` and `FundamentalClasses` give the
exact quantifiers and formulas; all group cohomology, field actions,
restriction, inflation, corestriction, cup product, and conjugacy maps are actual mathematical objects.

Source: Jean-Pierre Serre, *Local Fields* (1979),
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Chapter X, §§3--4, printed pages 154--156 (PDF pages 160--162), supplies
the continuous cohomology model, absolute H¹ vanishing, and the genuine
finite-stage maps. Chapter XIII, §3, Propositions 6--7 and Corollary 2 to
Proposition 7, printed pages 193--194 (PDF pages 198--199), supplies the
absolute invariant isomorphism, restriction-degree formula, and relative
image. The compatible realization target collects these properties
using the two Lean cochain models and the actual comparison diagram.
Chapter XI, §2, printed pages 166--167 (PDF pages 172--173), gives the
axioms; §3, printed page 168 (PDF page 174), gives the fundamental-class
consequences. Chapter XIII, §4, Theorem 1, printed pages 195--196 (PDF pages
200--201), is the local realization claim. Chapter XI, §3, Theorem 1,
printed page 168 (PDF page 174), and Chapter XIII, §4, Proposition 8,
printed page 196 (PDF page 201), give the all-integer Tate cup bijection. The arithmetic sign comes from
the actual cyclic cocycle normalization described in `Invariants.md`.
Chapter XI, §3, printed page 169 (PDF page 175), gives the inflation
diagram with multiplier `[M:L]`; `PositiveTateInflation` expresses its
positive-degree part using the published comparison constructions.
The simultaneous proposition is derived content assembling these source
claims on one invariant family; it asserts no proof of their realization.

This is a progressive realization target using the published definition
interfaces. It does not yet contain the separately assigned absolute
continuous corestriction or all-integer Tate restriction/corestriction
compatibility predicates. The ordinary degree-zero inflation diagram,
ordinary-to-Tate cup comparison, generic direct-limit comparison theorem and
the subsequent proofs are separate bound work. These boundaries do not
complete the umbrella task. Subsequent theorem proofs require separate
tasks naming exact accepted Library proposition declarations.
