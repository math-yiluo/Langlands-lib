# Noetherian models of reductive quasi-finite flat surjections

The theorem `Langlands.GroupScheme.reductiveQuasiFiniteNoetherianModel` proves
the unchanged published proposition
`Langlands.GroupScheme.ReductiveQuasiFiniteNoetherianModelStatement` in every
universe. Given an arbitrary commutative ring `A`, reductive group schemes
`G` and `H` over its spectrum, and the supplied locally quasi-finite flat
surjective homomorphism `f`, it constructs the exact
`NoetherianQuasiFiniteModel f`.

The initial coefficient ring is the integers lifted to the universe of `A`.
The ring equivalence with the integers makes this ring noetherian. The finite
coefficient construction `exists_quasiFiniteSmoothAffineHomModel`, applied
to the published proof `homGeneral`, gives a finitely generated coefficient
subalgebra, two smooth affine group models, and a locally quasi-finite flat
surjective model homomorphism. Its two group-scheme isomorphisms and recovery
equation retain the specified original map.

The finitely generated coefficient subalgebras form a directed system with
colimit `A`: adjoining any singleton supplies coverage. The two original
reductivity hypotheses transfer through the model isomorphisms to the two
groups over this colimit. The published unconditional theorem
`isReductive_baseChange_iff_eventually` then gives eventual reductivity for
each model group. A common upper bound of the two witness stages makes both
groups reductive. Enlargement to that stage preserves all three properties
of the model homomorphism and the recovery square.

Finally, `QuasiFiniteSmoothAffineHomModel.toNoetherian` passes from the finite
type coefficient subalgebra to its underlying subring of `A`. The finite type
form of the Hilbert basis theorem makes it noetherian. The two reductive
groups, homomorphism, morphism properties, base-change isomorphisms and exact
recovery equation give every field of the required model.

This proof is an internal composition of the named coefficient-model,
homomorphism-descent and directed-limit results. It uses the unconditional
whole-group reductivity equivalence; the remaining semisimple clauses of the
separate direct-limit statement are unnecessary. All rings and group schemes
remain in the arbitrary original universe, and the theorem has no premises
beyond its published target.
