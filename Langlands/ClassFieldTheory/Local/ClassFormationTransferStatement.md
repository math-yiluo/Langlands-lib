# Simultaneous local realization with Tate transfer compatibility

Author: Worker 49, with invariant and transfer interface design by Worker 42.

`LocalTransferCompatibleClassFormationStatement` asserts, for every prime
`p`, the existence of one raw `InvariantFamily.{u,u} p` satisfying all the
properties of `LocalCompatibleClassFormationStatement` and the additional
predicate `InvariantFamily.TateTransferCompatibility`. The existential
quantifier encloses the whole conjunction. In particular, the invariant
family in the transfer clause is the family with the asserted invariant
images and fundamental-class existence.

The common carrier universe `u` is arbitrary. The family ranges over every
`PadicField.{u} p` and every finite Galois extension represented in that
universe. The declaration supplies no invariant isomorphism, fundamental
class, class-formation law, or reciprocity theorem as a hypothesis.
`InvariantFamily` itself contains only raw additive maps.

The inherited clauses assert arithmetic normalization, continuous absolute
H¹ vanishing, absolute invariant bijectivity and the restriction-degree
law, and the actual ordinary finite-stage-to-absolute compatibility
diagram. They also assert relative H¹ vanishing, the degree-torsion image
of the finite relative invariant, invariant compatibility with inflation,
restriction, conjugacy and corestriction, and unique fundamental classes
with their exact order, generation, and four functorial laws.
The actual finite relative and continuous absolute cohomology groups
remain distinct and are connected by the constructed closure-inflation
map and proved finite comparison.

The remaining inherited clauses assert that left cup product with every
fundamental class is bijective in every integer Tate degree, and that
the positive-degree inflation diagram has multiplier `[M:L]` for a
tower `F ⊆ L ⊆ M`. The formulation does not extend Tate inflation to
degree zero or negative degrees.

The new clause covers every tower of p-adic fields `F ⊆ E` and finite
upper field `M` Galois over both, without requiring `E/F` to be Galois.
For every pair of classes `c ∈ H²(M/F)` and `d ∈ H²(M/E)` with respective
invariants `+1/[M:F]` and `+1/[M:E]`, and every integer `n`, it asserts:

- `Res(c ∪ x) = d ∪ Res(x)` for every integral Tate class `x` of
  `Gal(M/F)` in degree `n`.
- `Cor(d ∪ y) = c ∪ Cor(y)` for every integral Tate class `y` of
  `Gal(M/E)` in degree `n`.

The maps on the left have unit coefficients and degree `n + 2`; those
on the right have trivial lifted-integer coefficients and degree `n`.
They are the constructed subgroup transfers and reindexing maps from
`TateTransfers`. There is no multiplier in these two diagrams.
The separate fundamental-class formula
`Cor(d) = [E:F] • c` concerns ordinary degree two and is retained in
`FundamentalCorestriction`. It is not substituted for the cup diagram.
The `FundamentalClasses` conjunct supplies existence and uniqueness
for both invariant maps, so these conditional cup statements are
nonvacuous on every quantified tower.

The positive invariant and left cup conventions are unchanged. At degree
minus two, the existing Tate abelianization and norm-quotient
identifications apply. The inverse of that cup isomorphism is arithmetic
reciprocity; the host's geometric convention additionally inverts the
output, as explained in `TateAbelianization.md`. The transfer diagrams
themselves perform no such inversion.

This is a new `Prop`-valued definition strengthening the earlier target,
whose declaration and paired documentation are unchanged. It is derived
content assembling source claims on one existential family; it provides
no proof, choice-based constructor, or uniqueness claim for the entire
invariant family.

The module imports `ClassFormation`, `TateInflation`, and
`TateTransferCompatibility` directly. It does not import or change
`ClassFormationStatement`. The source correspondence for the conjunction
is as follows; all page numbers are printed pages of the edition below.

| Clauses | Published definitions and constructions | Source |
| --- | --- | --- |
| `ArithmeticNormalization` | `Invariants`, with the actual cyclic cocycle | XIII.3, p. 193 |
| `ContinuousInvariantProperties` | `ClassFormation`, `Invariants`, `FiniteInvariantCompatibility`, and the proved `FiniteComparison` | X.3–4, pp. 154–156; XIII.3, pp. 193–194 |
| `RelativeClassFormation` | `ClassFormation` and `Invariants` on actual relative cohomology | XI.2, pp. 166–167; XIII.4, Theorem 1, pp. 195–196 |
| `RelativeConjugacy`, `RelativeCorestriction` | `ClassFormation`, `Conjugacy`, and `Corestriction` | XI.2–3, pp. 167–168 |
| `FundamentalClasses` and its four functorial laws | `ClassFormation`, `FundamentalClasses`, `Conjugacy`, and `Corestriction` | XI.3, p. 168 |
| `TateIsomorphisms` | `TateCup`, using the constructed left cup map | XI.3, Theorem 1, p. 168; XIII.4, Proposition 8, p. 196 |
| `PositiveTateInflation` | `TateInflation`, using proved positive-degree comparisons | XI.3, p. 169 |
| `TateTransferCompatibility` | `TateTransferCompatibility`, using `TateTransfers` and `TateCup` | XI.3, pp. 168–169 |

Source: Jean-Pierre Serre, *Local Fields* (1979),
`serre-1979-local-fields`, retained PDF SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Chapter XI, §3, printed pp. 168–169 (PDF pp. 174–175), supplies positive
fundamental classes, their four formulas, all-integer left cup
bijectivity, the unscaled restriction and corestriction diagrams, the
scaled inflation formula, and the inverse reciprocity convention.
Chapter XIII, §4, Theorem 1 and Proposition 8, printed pp. 195–196
(PDF pp. 200–201), specializes the class formation and cup statements to
local fields. The inherited invariant and cohomology claims use X.3–4,
printed pp. 154–156 (PDF pp. 160–162), XI.2, printed pp. 166–167
(PDF pp. 172–173), and XIII.3, Propositions 6–7 and Corollary 2,
printed pp. 193–194 (PDF pp. 198–199).

This progressive target still leaves absolute continuous corestriction,
ordinary degree-zero inflation, the ordinary-to-Tate cup comparison and
the generic direct-limit comparison to separate assigned work. It does
not assert completion of the whole class-formation assignment or a proof
of local class field theory. Subsequent proof tasks must name the exact
published proposition declaration.
