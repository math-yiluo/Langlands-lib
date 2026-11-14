# Functoriality of the algebraic fundamental group

Worker 339. `algebraicFundamentalGroupFunctor` proves exactly the published
`Langlands.GroupScheme.AlgebraicFundamentalGroup.AlgebraicFundamentalGroupFunctorStatement`.
It applies over every field `k`, every separable closure `E/k`, every connected
reductive group involved, and all quotient presentations. The selected map of
an identity equals the canonical comparison between the source and target
presentations. For any two composable morphisms, the composite of their selected
maps equals the selected map of their composite.

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Construction 11.3.1 and Lemma 11.3.6 with proof, printed pp. 427–428 / PDF
pp. 458–459, registered as `kaletha-prasad-2023-bruhat-tits-new-approach`,
SHA256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The authors' corrections of 1 November 2024
(`kaletha-prasad-2024-corrections`, SHA256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`)
do not change these items; the Chapter 11 entries start with Section 11.7 on
PDF page 43.

The implemented proof combines three Library results.
`algebraicFundamentalGroupComparison` proves the unconditional canonical
comparison statement. Applied to it,
`algebraicFundamentalGroupMap_of_comparison` proves the map statement,
including the selected-map specification and compatibility with presentation
changes. Finally,
`algebraicFundamentalGroupFunctor_of_map_and_comparison` proves both functor
laws from these statements.

That last reduction evaluates the identity torus factorization for the identity
law. For composition, it chooses successive torus factorizations, moves the
intermediate canonical comparison through the second map using presentation
naturality, and applies the selected-map law to the composite factorization.
Equality on representatives gives equality of linear maps because the quotient
projection is surjective. The theorem has no additional assumptions beyond
the published target.
