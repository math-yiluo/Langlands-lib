# Fundamental-class consequences of relative class formation

Author: Worker 159.

The theorem `Langlands.ClassFieldTheory.Local.relativeFundamentalClassConsequences`
proves exactly the published
`RelativeFundamentalClassConsequencesStatement.{u}` from
`ClassFormationStatement`. For every prime `p` and raw invariant family
`I : InvariantFamily.{u,u} p`, the hypotheses are precisely
`I.RelativeClassFormation` and `I.RelativeConjugacy`. The conclusion gives
unique fundamental classes, their exact extension-degree additive order and
generation of actual relative H², and their inflation, restriction,
corestriction and conjugacy formulas. The common carrier universe `u` is
arbitrary. Each formula retains the finite-extension and Galois hypotheses
of its published predicate.

The fundamental class has invariant the positive class `1/[L:K]` in the
actual quotient of the rationals by the integers. The proof uses the existing
relative cohomology groups and constructed maps. It adds no invariant
isomorphism, chosen fundamental class, or corestriction assumption. This is
a consequence of the stated finite class-formation axioms; it asserts no
existence of an invariant family or unconditional local class formation.

## Provenance

The target and fundamental-class predicates are the published interfaces in
`ClassFormationStatement`, `ClassFormation` and `FundamentalClasses`.
Their original source is Jean-Pierre Serre, *Local Fields* (1979), registered
as `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Chapter XI, section 2, printed pages 166–167 (PDF pages 172–173), supplies
the axioms. Section 3, printed page 168 (PDF page 174), gives unique
existence, order, generation and the four displayed fundamental-class
formulas. The implemented proof below derives those consequences from the
published finite-level predicates; it does not construct the source's
direct-limit formation or prove its reciprocity and cup-product claims.

The helper lemmas in this file are derived proofs for those predicates.
The quotient arithmetic uses `denominatorEquiv` and `denominatorEquiv_one`
from the published `UnramifiedInvariant` module. These particular lemmas
are abstract arithmetic statements about `ZMod n` and `denominatorSubgroup n`;
their use imposes no unramifiedness condition on the field extensions.
The corestriction step imports the published theorem
`relativeH2CorestrictionRestriction` from
`RelativeH2CorestrictionRestrictionProof`. That theorem already proves the
ordinary/Tate restriction comparison and the subgroup-index identification
needed to apply the genuine transfer identity to relative H².

## Existence, order and generation

For a positive natural number `n`, `denominatorEquiv n hn` identifies
`ZMod n` with `denominatorSubgroup n`, and its value at `1` is the
positive reciprocal class. The private lemmas `reciprocalClass_mem`,
`reciprocalClass_addOrderOf` and `denominatorSubgroup_mem_zmultiples` give,
respectively, membership of that class, its exact additive order `n`, and
an integer-multiple expression for every element of the denominator subgroup.
For the order, injectivity of the subgroup inclusion and the additive
equivalence transfers `ZMod.addOrderOf_one`. For the integer-multiple
expression, `ZMod.intCast_surjective` expresses the inverse image as an
integer multiple of `1`, then the equivalence transports that expression.

The private lemma `fundamentalProperties_of_invariantImage` applies this
arithmetic with `n = Module.finrank K L`, which is positive for a finite
field extension. The exact invariant range gives a class mapping to `1/n`;
injectivity gives uniqueness. Injectivity also transports additive order.
For generation, the invariant of any cohomology class is an integer multiple
of `1/n`, and injectivity identifies the original class with the same
multiple of a fundamental class. Thus its subgroup of integer multiples is
all of relative H². This argument includes degree one.

`InvariantFamily.fundamentalClasses_of_relativeImages` applies that lemma
to every extension quantified by `I.FundamentalClasses`. Its only invariant
hypothesis is `I.RelativeImages`.

## Inflation and restriction

The private arithmetic lemma `reciprocalClass_mul_left` proves
`a • reciprocalClass (a * b) = reciprocalClass b` for positive `a` and `b`.
It moves the natural scalar through the quotient homomorphism and proves
the corresponding rational equality by cancelling the nonzero degrees.

`fundamentalInflation_of_relativeClassFormation` uses injectivity of the
invariant for the top extension. The inflation compatibility axiom replaces
the invariant of the inflated class by the lower invariant. The tower law
`[M:K] = [L:K] * [M:L]` and the reciprocal identity then give
`Inf(c) = [M:L] • d` for any respective fundamental classes.

`fundamentalRestriction_of_relativeClassFormation` uses injectivity of the
invariant over the new base. The invariant restriction axiom multiplies by
`[E:F]`; the tower law and reciprocal identity give `Res(c) = d`.
The H¹-vanishing component of `RelativeClassFormation` is retained in the
exact target but is not needed by these consequence proofs.

## Corestriction and conjugacy

`fundamentalCorestriction_of_relativeClassFormation` lets `d` be any
fundamental class for `M/F` and `c` any fundamental class for `M/E`.
The proved restriction formula gives `Res(d) = c`. Substituting this into
`Cor(c)` and applying the imported theorem
`relativeH2CorestrictionRestriction F.Carrier E.Carrier M d` gives
`Cor(c) = [E:F] • d`. No normality of `E/F` is required, and the transfer
identity is a proved dependency rather than a hypothesis of this theorem.

`fundamentalConjugacy_of_relativeImages` uses invariant injectivity and
the given `RelativeConjugacy` compatibility to reduce the conclusion to
equality of the two reciprocal classes. The constructed `galoisConjugacy`
equivalence identifies the finite Galois-group cardinalities, and
`IsGalois.card_aut_eq_finrank` identifies their extension degrees.
Consequently the conjugacy map carries every source fundamental class to
the target fundamental class.

Finally, `relativeFundamentalClassConsequences` introduces exactly the prime,
its primality instance, the invariant family and the two published
hypotheses, then conjoins these five results. All target and imported pairs
are unchanged; the only new pair is this proof and its explanation.
