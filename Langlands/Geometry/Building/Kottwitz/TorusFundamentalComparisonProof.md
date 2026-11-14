# Fundamental groups of tori

This module proves
`Langlands.Geometry.Building.Kottwitz.TorusFundamentalComparisonStatement`
for the original torus and the chosen fundamental-group presentation in the
Library. The theorem is `torusFundamentalComparison_proof`. No comparison
isomorphism or existence assertion is assumed.

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Construction 11.3.1 and Fact 11.3.5, printed p. 427 / PDF p. 458 in the
registered copy, source ID `kaletha-prasad-2023-bruhat-tits-new-approach`,
SHA256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The authors' corrections of 1 November 2024, Chapter 11, concern §11.7 and
do not change this fact. The task's p. 428 / PDF p. 459 locator is the
following page in this copy.

The implemented proof uses the existing maximal-torus theorem to show that
the chosen inclusion into the ambient torus is an isomorphism. The derived
inclusion is trivial, since the identity morphism to the separated
commutative torus annihilates its actual derived subgroup. The pullback
identity then shows that the map from the preimage torus is zero. Its
cocharacter-image submodule is therefore zero over every field extension.
Composition with the chosen inclusion is bijective on actual cocharacters.

The presentation map descends through the quotient by its zero coroot
image. The quotient projection is surjective, so the representative law
determines this linear map uniquely and the epsilon-selected comparison
satisfies it. Injectivity and surjectivity follow from the corresponding
properties of the presentation map. Naturality of actual cocharacter
transport for the inclusion gives equivariance on representatives; quotient
surjectivity gives equivariance everywhere.

The named specification, bijectivity and equivariance lemmas hold over
every field extension `E/k`. The final theorem specializes them to the
separable closures quantified in the unchanged target. The intermediate
lemmas are internal consequences of the Library's actual derived subgroup,
pullback and Galois-transport constructions, rather than separately
numbered assertions in KP.
