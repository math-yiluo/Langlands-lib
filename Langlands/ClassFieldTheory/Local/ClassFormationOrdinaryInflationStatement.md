# Simultaneous local realization with ordinary cup inflation

Author: Worker 49, with invariant and ordinary-inflation interface design
by Worker 42.

`LocalOrdinaryInflationCompatibleClassFormationStatement` asserts, for
every prime `p`, the existence of one raw `InvariantFamily.{u,u} p`
satisfying the clauses of
`LocalTransferCompatibleClassFormationStatement` together with
`InvariantFamily.OrdinaryInflation`. The existential quantifier encloses
all fourteen conjuncts. In particular, the ordinary inflation clause
uses the same relative invariant maps for which fundamental classes
are asserted to exist uniquely and generate their degree-two groups.

The common carrier universe `u` is arbitrary. The target ranges over
every `PadicField.{u} p` and finite Galois extensions represented in
that universe. The ordinary-inflation predicate itself supports an
independent base universe; here it is specialized to the common
universe required by the inherited simultaneous predicates. There is
no restriction to `Type 0`. No invariant isomorphism, fundamental
class, class-formation property or reciprocity theorem is supplied as
an input: `InvariantFamily` contains only raw additive maps on actual
relative and continuous absolute cohomology.

The inherited conjuncts assert arithmetic normalization; continuous
absolute H¹ vanishing, invariant bijectivity, restriction multiplication
by degree and the ordinary finite-stage closure-inflation diagram;
relative H¹ vanishing, the degree-torsion image of the relative
invariant and its inflation, restriction, conjugacy and corestriction
laws; unique fundamental classes with exact order, generation and
their four functorial laws; left-cup bijectivity in every integer Tate
degree; positive Tate inflation with its upper-extension multiplier;
and the two unscaled Tate restriction/corestriction cup diagrams.
Relative and absolute cohomology remain distinct groups connected
by constructed maps.

The added ordinary clause says the following. Let `K = F.Carrier`
for any field `F` in this family, and let `K ⊆ L ⊆ M` be a compatible
tower with `L/K` and `M/K` finite Galois. For every
`c ∈ H²(L/K,Lˣ)` and `d ∈ H²(M/K,Mˣ)` having invariants
`+1/[L:K]` and `+1/[M:K]`, respectively, every natural number `n`,
and every ordinary integral class `x ∈ Hⁿ(Gal(L/K),ℤ)`, it asserts

`Inf(c ∪ x) = [M:L] • (d ∪ Inf(x))`.

The Lean coefficient ring is the existing `IntegerScalars`, a lift
of the integers to the carrier universe. The left-hand map is
`relativeInflationLinear K L M (n + 2)` on unit cohomology.
The right-hand map on `x` is `integralInflation K L M n`.
The cups are the actual `relativeOrdinaryCup` with the degree-two
unit class on the left. The scalar is `Module.finrank L M`,
the upper-extension degree. The clause quantifies all fundamental
classes, with no choice of representatives or classes.

In degree zero, `x` belongs to ordinary H⁰. The imported
`relativeOrdinaryCup_comparison` relates this cup to the existing
Tate cup through `relativeOrdinaryToTate` and `integralOrdinaryToTate`.
The integral comparison at zero maps invariants to the Tate norm
quotient; it is not asserted to be an isomorphism. This target
introduces no degree-zero or negative Tate inflation. The separately
retained `PositiveTateInflation` clause concerns positive Tate input
degrees, and `TateTransferCompatibility` concerns all integer degrees.

`FundamentalClasses` applies to both `L/K` and `M/K` for every tower
in the new clause. Thus its quantified fundamental classes exist for
the same witness `I`, and the new conditional law cannot be satisfied
merely because those classes are absent. The declaration does not
assert the unscaled naturality predicate `OrdinaryCupInflation` for
all degree-two classes; it asserts the scaled fundamental-class
predicate specified above.

The positive invariant and left-cup conventions are unchanged. With
the existing degree-minus-two abelianization and norm-quotient
identifications, the inverse Tate cup isomorphism gives arithmetic
reciprocity. The host's geometric convention further inverts its
output, as documented in `TateAbelianization.md`. The new ordinary
formula performs neither inversion.

This is derived content assembling the following source claims on one
existential family. It is a `Prop`-valued definition, with no proof of
local realization, choice-based constructor or uniqueness assertion
for the entire invariant family. It has a new name and leaves the
earlier statement declarations and their paired files unchanged.
Its direct imports are `ClassFormation`, `TateTransferCompatibility`
and `OrdinaryCupInflation`; the last imports `TateInflation`.

| Clauses | Published definitions and constructions | Serre source |
| --- | --- | --- |
| `ArithmeticNormalization` | `Invariants`, actual cyclic cocycle | XIII.3, p. 193 |
| `ContinuousInvariantProperties` | `ClassFormation`, `Invariants`, `FiniteInvariantCompatibility`, proved `FiniteComparison` | X.3–4, pp. 154–156; XIII.3, pp. 193–194 |
| `RelativeClassFormation` | `ClassFormation`, `Invariants` | XI.2, pp. 166–167; XIII.4, Theorem 1, pp. 195–196 |
| `RelativeConjugacy`, `RelativeCorestriction` | `ClassFormation`, `Conjugacy`, `Corestriction` | XI.2–3, pp. 167–168 |
| `FundamentalClasses` and its four functorial laws | `ClassFormation`, `FundamentalClasses`, `Conjugacy`, `Corestriction` | XI.3, p. 168 |
| `TateIsomorphisms` | `TateCup`, actual left cup | XI.3, Theorem 1, p. 168; XIII.4, Proposition 8, p. 196 |
| `PositiveTateInflation` | `TateInflation`, positive-degree comparisons | XI.3, p. 169 |
| `TateTransferCompatibility` | `TateTransferCompatibility`, `TateTransfers`, `TateCup` | XI.3, pp. 168–169 |
| `OrdinaryInflation` | `OrdinaryCupInflation`, actual ordinary cup and inflation maps | XI.1, pp. 165–166; XI.3, pp. 168–169 |

Source: Jean-Pierre Serre, *Local Fields* (1979),
`serre-1979-local-fields`, retained PDF SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The table uses printed pages. Their PDF pages are 160–162 for X.3–4,
171–175 for XI.1–3, 198–199 for XIII.3, and 200–201 for XIII.4.
In the new clause, Serre's `E`, `F`, `F′` correspond to `K`, `L`, `M`.
XI.1 specifies ordinary inflation for degrees `q ≥ 0`; the degree-zero
clause interprets XI.3's scaled diagram in that ordinary range.
The explicit local cup and comparison are internal specializations of
published constructions, not additional claims of the original text.

Absolute continuous corestriction and its simultaneous invariant
compatibility remain separate work, as does a general direct-limit
comparison. This target asserts neither those missing clauses nor
completion of the umbrella task. The source's local existence claims
are proposition conclusions here; subsequent proof work must be bound
to this exact published declaration.
