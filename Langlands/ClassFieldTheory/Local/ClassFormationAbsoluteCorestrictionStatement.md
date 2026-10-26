# Simultaneous local realization with absolute corestriction

Author: Worker 49, with invariant and compatibility interface design by
Worker 42.

`Langlands.ClassFieldTheory.Local.LocalAbsoluteCorestrictionCompatibleClassFormationStatement`
asserts, for every prime `p`, the existence of one raw
`InvariantFamily.{u,u} p` satisfying all fourteen clauses of
`LocalOrdinaryInflationCompatibleClassFormationStatement` together with
`InvariantFamily.AbsoluteCorestriction`. The single existential quantifier
encloses all fifteen conjuncts. Absolute invariant bijectivity, finite
relative invariant properties, fundamental-class existence and every
compatibility law are conclusions about this same family.
`InvariantFamily` contains raw additive maps on actual cohomology groups;
it assumes none of these properties.

The carrier universe `u` is arbitrary. Every `PadicField.{u} p` is
included, and the relative extension carriers lie in that same universe,
as required by the inherited simultaneous predicates. The imported
absolute-corestriction predicate allows its relative-component universe
to vary independently; this assembly specializes both family universes to
`u`. There is no restriction to `Type 0`.

For every `F E : PadicField.{u} p`, every finite extension algebra
`F.Carrier → E.Carrier` compatible with their specified `Padic p`
algebras, and every supplied compatible algebra on their actual algebraic
closures, the added conjunct asserts

```
I.absolute F (absoluteCorestriction F.Carrier E.Carrier 2 x) =
  I.absolute E x
```

for every `x : absoluteCohomology E.Carrier 2`. The invariant of the
upper-to-lower transfer equals the upper invariant without a degree
multiplier. These extensions need not be normal or Galois. The closure
data are exactly
`Algebra (AlgebraicClosure F.Carrier) (AlgebraicClosure E.Carrier)` and
`IsScalarTower F.Carrier (AlgebraicClosure F.Carrier)
(AlgebraicClosure E.Carrier)`; every such supplied structure is
quantified, with no additional tower condition over `E.Carrier`.
Characteristic zero of `F.Carrier` is derived locally from its specified
p-adic algebra by the imported predicate.

`absoluteCohomology` is actual continuous absolute Galois cohomology with
discrete algebraic-closure unit coefficients. The imported
`absoluteCorestriction` transports upper-field cohomology to that of the
actual open image of absolute Galois restriction, then applies genuine
continuous corestriction. Its intrinsic finite-stage certificate
identifies this operation with ordinary finite-stage transfer. This
statement uses its underlying module map; it asserts no continuity
between cohomology topologies. The invariant law is not an input to this
construction.

The first fourteen conjuncts, in order, are
`ArithmeticNormalization`, `ContinuousInvariantProperties`,
`RelativeClassFormation`, `RelativeConjugacy`, `RelativeCorestriction`,
`FundamentalClasses`, `FundamentalInflation`, `FundamentalRestriction`,
`FundamentalCorestriction`, `FundamentalConjugacy`, `TateIsomorphisms`,
`PositiveTateInflation`, `TateTransferCompatibility` and
`OrdinaryInflation`. Their definitions and field hypotheses are imported
unchanged. In particular, the relative groups remain distinct from
continuous absolute cohomology and are linked by actual
`closureInflation`, whose invariant diagram belongs to the continuous
conjunct.

These inherited clauses include absolute and relative H¹ vanishing,
absolute invariant bijectivity, the relative degree-torsion image in the
actual `Q/Z`, and degree-scaled absolute and relative restriction.
They also include unique fundamental classes with positive invariant
`+1/[L:K]`, exact order and generation, and all four fundamental-class
functorial laws. Left cup with a fundamental class is bijective in every
integer Tate degree; its restriction and corestriction diagrams are
unscaled, while its positive-degree Tate inflation diagram has the
upper-extension degree multiplier. The new absolute invariant equality
does not alter the separate formula that corestriction of a fundamental
class multiplies the lower-base fundamental class by the base-extension
degree.

Ordinary inflation still asserts
`Inf(c ∪ x) = [M:L] • (d ∪ Inf(x))` for every compatible finite Galois
tower `K ⊆ L ⊆ M`, all fundamental classes `c,d` for this same family,
every natural input degree and every ordinary integral class `x`.
`FundamentalClasses` supplies both classes, so this law cannot be
satisfied merely because they are absent. Input degree zero uses
ordinary H⁰ and its canonical map to the Tate norm quotient. The
statement introduces no degree-zero or negative Tate inflation and no
claim that this degree-zero comparison is an isomorphism.

The arithmetic normalization, positive fundamental invariant and left
cup order agree with Serre. In degree minus two the Tate cup map runs
from the Galois abelianization to the norm quotient; its inverse gives
arithmetic reciprocity. The host's geometric convention further inverts
the output, as documented in `TateAbelianization.md`. The added invariant
equality makes no Frobenius choice and introduces no inversion.

This is a derived existential assembly of published predicates. Its
direct imports are `ClassFormationOrdinaryInflationStatement` and
`AbsoluteCorestrictionInvariant`. The table gives the original-source
correspondence for all fifteen clauses; page numbers are printed pages
of Jean-Pierre Serre, *Local Fields* (1979).

| Clauses | Imported definitions and constructions | Original source |
| --- | --- | --- |
| `ArithmeticNormalization` | `Invariants`, actual cyclic cocycle | XIII.3, p. 193 |
| `ContinuousInvariantProperties` | `ClassFormation`, `Invariants`, `FiniteInvariantCompatibility`, `FiniteComparison` | X.3–4, pp. 154–156; XIII.3, pp. 193–194 |
| `RelativeClassFormation` | `ClassFormation`, `Invariants` | XI.2, pp. 166–167; XIII.4, Theorem 1, pp. 195–196 |
| `RelativeConjugacy`, `RelativeCorestriction` | `ClassFormation`, `Conjugacy`, `Corestriction` | XI.2–3, pp. 167–168 |
| `FundamentalClasses` and its four functorial laws | `ClassFormation`, `FundamentalClasses`, `Conjugacy`, `Corestriction` | XI.3, p. 168 |
| `TateIsomorphisms` | `TateCup`, actual left cup | XI.3, Theorem 1, p. 168; XIII.4, Proposition 8, p. 196 |
| `PositiveTateInflation` | `TateInflation`, positive-degree comparisons | XI.3, p. 169 |
| `TateTransferCompatibility` | `TateTransferCompatibility`, `TateTransfers`, `TateCup` | XI.3, pp. 168–169 |
| `OrdinaryInflation` | `OrdinaryCupInflation`, actual ordinary cup and inflation | XI.1, pp. 165–166; XI.3, pp. 168–169 |
| `AbsoluteCorestriction` | `AbsoluteCorestrictionInvariant`, `AbsoluteCorestriction`, `AbsoluteRestrictionImage`, continuous corestriction | XI.2, Proposition 1(ii), pp. 167–168; XIII.4, Theorem 1, pp. 195–196 |

The registered source is `serre-1979-local-fields`, retained at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The corresponding PDF pages are 160–162, 171–175, 198–199 and 200–201.
XI.2 Proposition 1(ii), printed p. 167 / PDF p. 173, states the unscaled
invariant/corestriction equality for every extension; its proof continues
on p. 168 / PDF p. 174. XIII.4 Theorem 1 realizes one local
multiplicative class formation with these invariants, supporting their
simultaneous quantification here. Serre uses an inflation direct limit
for absolute H². This target uses the Library's constructed continuous
cohomology and finite-stage comparison maps and does not add a general
direct-limit comparison theorem. The ordinary degree-zero clause is the
ordinary-range interpretation of XI.3's scaled diagram, using XI.1's
range `q ≥ 0`.

Worker 49 read the cited original passages, including visual inspection
of Proposition 1(ii). Serre's 2019 book corrections, PDF pp. 2–3, do not
change these passages. The printed-p. 193 connecting-arrow correction
agrees with the inherited inverse-boundary normalization. No
project-specific errata file for the 1979 source was present.

The Lean declaration defines an unproved proposition. It constructs no
invariant family, chooses no fundamental class and asserts no uniqueness
of the whole family. Earlier statement declarations and their proof
bindings are preserved. A later realization proof must bind this exact
published target; this focused strengthening does not declare completion
of the umbrella task.
