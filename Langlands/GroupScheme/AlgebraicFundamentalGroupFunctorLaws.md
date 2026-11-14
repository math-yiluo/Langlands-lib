# Identity and composition from geometric induced-map laws

Worker 339. This internal reduction proves the functor laws from the two
published proposition definitions `AlgebraicFundamentalGroupMapStatement` and
`AlgebraicFundamentalGroupComparisonStatement`. The reduction takes proofs of
those propositions as arguments; it does not prove their unconditional
existence assertions.

The mathematical source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), Construction 11.3.1 and Lemma 11.3.6, printed pp. 427–428 / PDF
pp. 458–459, registered as `kaletha-prasad-2023-bruhat-tits-new-approach`,
SHA256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The authors' corrections of 1 November 2024, registered as
`kaletha-prasad-2024-corrections`, SHA256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
have no changes to these items; their Chapter 11 entries begin with Section
11.7 on PDF page 43. This module supplies the
formal identity and composition calculations left implicit in the proof of
Lemma 11.3.6, using the actual selected maps in the Library.

`Choice.isTorusFactorization_id` proves that the identity of the chosen
geometric torus is a factorization of the ambient identity.
`Choice.IsTorusFactorization.comp` composes two actual torus restrictions:
functoriality of base change and associativity turn their two equations into
the required equation for the composite.

`mapTo_id_of_mapStatement` evaluates the selected-map specification on the
identity factorization. It gives the canonical comparison on every source
quotient representative. Surjectivity of the quotient projection proves
equality of linear maps. This works for every pair of presentations of the
same group, rather than only a fixed presentation.

For composition, the proof chooses a factorization of `f` through a maximal
torus `d` in the middle group, then a factorization of `g` from `d` through a
maximal torus `t` in the final group. The source-presentation naturality clause
of the map statement moves the intermediate comparison past the map of `g`;
the comparison statement identifies the final self-comparison with the
identity. Applying the two representative formulas then gives the formula
for the composed torus factorization. Associativity of torus morphisms and
surjectivity of the source quotient projection finish the equality.

The result quantifies over every field, separable closure, connected reductive
groups and all three presentations exactly as the published functor statement.
It introduces no additional geometric hypotheses. Its only theorem inputs
are the complete map and comparison statements named above.
