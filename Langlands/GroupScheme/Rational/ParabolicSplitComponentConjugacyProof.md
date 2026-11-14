# Unipotent conjugacy of parabolic split components

The module proves `Langlands.GroupScheme.parabolicSplitComponentConjugacy`
with exact type
`Langlands.GroupScheme.ParabolicSplitComponentConjugacyStatement.{u}`.
It imports the published statement without modifying it or its dependencies.

Over every field, two maximal split tori of the supplied geometric solvable
radical of a rational parabolic are conjugate in the parabolic by a rational
point of its supplied geometric unipotent radical. The conclusion includes
an isomorphism of the source group schemes and the equality of their
homomorphisms after conjugation. It asserts transitivity, with no uniqueness
claim.

## Provenance

The target records the transitivity assertion of Renard, *Représentations des
groupes réductifs p-adiques*, edition of 9 July 2026, V.3.1, printed page 110
(PDF page 116). Split components of a parabolic mean maximal split tori of its
solvable radical, as in V.2.1, printed page 104 (PDF page 110). The registered
source is `renard-2026-representations-groupes-reductifs-padiques`.
The proof below is an assembly of published Library results using a Levi
projection and torus cocycle vanishing.

## Implemented proof

Write `r : R ⟶ P` for the solvable radical and `u : U ⟶ P` for the unipotent
radical. Their defining predicates provide smoothness and connectedness.
Affineness follows from their closed embeddings in the parabolic, which is
closed in the affine ambient reductive group.

The published dynamic presentation of a rational parabolic identifies the
image of `u ≫ j` with the contracting subgroup of a cocharacter. The published
splitness theorem for a representative of a contracting subgroup therefore
proves that this very `U` is split unipotent.

The published initial radical torus theorem supplies a rational Levi
`l : L ⟶ P`. Its multiplication decomposition supplies a group-scheme
retraction `q : P ⟶ L` whose kernel is its geometric unipotent radical.
Uniqueness of represented unipotent radicals identifies that kernel with
the specified image of `u`. The normal solvable subgroup centrality theorem
shows that `r ≫ q` is central in the reductive group `L`.

The published `smoothMaximalSplitTorusConjugacy` conjugates the two supplied
maximal split tori inside `R`. Postcomposing with `r` gives a conjugacy in
`P`, with a source isomorphism `e`. Applying `q` to this equation gives equal
quotient homomorphisms: inner conjugation fixes the central map through
`r ≫ q`.

Finally, `QuotientHomCocycle.splitUnipotentTorusConjugator` gives a rational
point of the specified `U` conjugating these two torus homomorphisms with
equal quotient maps. Its correctness theorem gives exactly the target
equation, with the same source isomorphism `e`. The three structural inputs
to the cocycle construction are supplied by the published stable vector
subgroup, torus action linearization and split unipotent affine torsor proofs.
No sibling split-component statement is assumed.
