# Parabolic chamber linear algebra

Worker 705, Task 6450. Module
`Langlands.Representation.LanglandsClassification.ParabolicChamberLinearAlgebraProof`,
namespace `Langlands.GroupScheme`.

The theorem `parabolicChamberLinearAlgebra` proves exactly the published
`ParabolicChamberLinearAlgebraStatement.{u}`. It applies the intermediate theorem
`parabolicChamberLinearAlgebra_of_statements` to the published proofs
`relativeFundamentalWeight` and `standardLeviRealDecomposition`, so the final
theorem has no additional premises.

## Scope and source

The target concerns an arbitrary field `k`, a connected reductive group scheme
`G`, a maximal split torus `i : T.toGrp ⟶ G`, a generic cocharacter `ν`, supplied
integral reflection data `D : RelativeRootReflectionData i`, and a subset `J` of
the simple relative roots `Δ = simpleRelativeRoots i ν`. In the following
notation, all the spaces are actual Library submodules:

| Symbol | Submodule |
| --- | --- |
| `X` | `relativeRootSpanReal i` in `Vstar T` |
| `C` | `LinearMap.range (rationalCharacterRestrictReal i)` in `Vstar T` |
| `N` | `cocharacterAnnihilator C` in `V T` |
| `P` | `corootAnnihilator i D J ⊓ X` |
| `Q` | `rootAnnihilator T J ⊓ N` |

The original source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The passage is V.3.14–V.3.16, printed pp.113–114 / PDF pp.119–120. The statement
pair `ParabolicChamberStatements` gives the source comparison and definitions.
The arbitrary-field scope and supplied reflection data belong to the published
statement; Renard works over a nonarchimedean local field. No existence theorem
for `D`, nor identification with a separately supplied geometric split component,
is asserted here. The latter is the sibling
`ParabolicSplitComponentChamberStatement`.

The proof below is derived finite-dimensional linear algebra from the two named
prerequisite theorems, the published theorem `relativeCharacterRootComplement`,
and the compatibility lemmas in `ParabolicChamberStatements`. It does not follow
a separate unformalized proof from the literature. The corrected standard-Levi
statement supplies annihilator complements; this proof makes no claim about the
unprojected difference-root spans in the source issue I4 of V.3.13.

## Projections and their separation

The standard-Levi statement, applied with both index sets equal to `J`, gives
complements of the coroot annihilator by the real span of `J` and of the root
annihilator by the span of its coroots. The helper `projection_unique` in
`ParabolicChamberBasis` converts a complement into the unique vector `y` in the
first submodule for which `x - y` lies in the second. Applying it to an actual
root vector and its actual coroot proves `projections_exist_unique`. The
coroot-set definition is unpacked to identify its singleton generator.

For `projected_roots_distinct`, take the fundamental coweight of a simple root
`α` outside `J`. The published subset lemma places it in `rootAnnihilator T J`.
Pairing a projected root with this coweight equals evaluating the original root,
by `pair_eq_of_mem_projectedRoots`. If the projections of `α` and a distinct
simple root `α'` were equal, their evaluations would therefore be both `1` and
`0`. This argument uses fundamental coweights directly.

## Parabolic bases and coefficient formulas

`weight_pair` and `coweight_eval` express the defining Kronecker equations for
fundamental weights and coweights. The helper `repr_eq` identifies basis
coordinates with these biorthogonal functionals.

The fundamental-weight basis of `X` restricts to the simple indices outside `J`.
Each selected vector lies in `P` by `parabolicFundamentalWeights_subset`. For a
vector of `P`, its coordinate at an index in `J` is its pairing with that simple
coroot and hence vanishes. The general `restrict_submodule_basis` lemma gives
the basis of `P` and identifies each of its vectors with the corresponding
ambient fundamental weight. The same proof uses root evaluations and
`parabolicFundamentalCoweights_subset` to restrict the fundamental-coweight basis
of `N` to a basis of `Q`.

The ambient real character space is finite dimensional because `T` is a split
torus. A basis of its subspace `X` therefore has a finite index type, so both
`Δ` and its subset of indices outside `J` are finite. The sums in the target are
finite `finsum` expressions, including when the index set is empty.

`face_coordinate_set` rewrites the vanishing conditions on `J` as membership in
`P` and the remaining simple-coroot conditions as coordinate conditions. Applying
`coordinate_set` with `p r := 0 < r` and `p r := 0 ≤ r` gives exactly the open
and closed face formulas in the target.

## Chambers, central summands and projected coroots

The published character/root complement decomposes every `y : Vstar T` as
`x + μ`, with `x ∈ X` and `μ ∈ C`. The standard-Levi statement identifies `C`
with the coroot annihilator of all simple roots. Thus adding `μ` does not change
any simple-coroot pairing. In `chamber_central_set`, this proves both directions
of chamber = face + `C`, for an arbitrary predicate on the complementary
simple-coroot pairings. Its strict and nonnegative specializations give the two
set-addition identities. Rewriting each face by its coefficient formula and
using `coefficient_set_add` gives the chamber formulas with a central summand.

On the coroot annihilator of `J`, the published
`pair_eq_of_mem_projectedCoroots` identifies pairing with a projected coroot
with pairing with its original coroot. Conversely, existence of both
projections of every simple root outside `J` permits testing each original
simple-coroot condition through `IsParabolicCorootOf`.
`chamber_projected_set` carries out these two implications for an arbitrary
predicate. The two inequality specializations give the remaining chamber
characterizations.

## Topology and assembly

Equip `Vstar T` with `moduleTopology ℝ`. The helper `moduleTopology_t2` proves
Hausdorffness using its continuous injective basis-coordinate map into a finite
product of copies of `ℝ`. Addition, negation and scalar multiplication are
continuous for this topology.

In the basis of `P`, `orthant_topology` realizes the open face as the image of
the strictly positive coordinate orthant. The coordinate equivalence is a
homeomorphism, and inclusion of `P` in `Vstar T` is a closed embedding because
`P` is finite dimensional and the ambient topology is Hausdorff. The positive
orthant is open in the coordinate space, and its closure is the nonnegative
orthant, by the finite product closure formula and `closure_Ioi`. The closed
embedding transports that closure to the ambient space. Rewriting the two face
formulas therefore proves relative openness and the exact ambient closure
identity in the target.

`parabolicChamberLinearAlgebra_of_statements` assembles these results into all
nine conjuncts of the published target from the fundamental-weight and
standard-Levi statements. The final theorem `parabolicChamberLinearAlgebra`
discharges both premises with `relativeFundamentalWeight` and
`standardLeviRealDecomposition`. Empty simple-root sets and `J = Δ` require no
extra assumptions or separate cases.
