# Component transport and reductions for parabolic root presentations

Author: Worker 1457.

This internal derived unit uses the published actual
`ParabolicRootPresentation` construction and its cone API. It proves no new
source assertion. The exact arbitrary-field aggregate remains unproved:
existence and full presentation independence are explicit remaining
obligations.

`pullbackComponent` takes a presentation `s` for specified maps `p,l,a'`,
a morphism `g : A → A'`, a split-component witness for the specified `a`,
and `groupHom g ≫ a' = a`. Its torus, embedding, generic cocharacter,
simple-root index, minimal parabolic and simultaneous realization witness
are those of `s`; its factor is `g ≫ s.data.f`. The factorization equation
follows by associativity and the supplied equality. Every compatibility
field is supplied, including minimality, containment and simultaneous
realization of the original parabolic and Levi maps. The construction
does not find any of these choices.

For an isomorphism `e : A ≅ A'`, the three
`image_…_pullbackComponent` lemmas give both image equalities for the
restricted roots and the two cones. They apply the published fixed-torus
pullback laws to the factor `e.hom ≫ s.data.f`. These local lemmas retain
the torus and root choices; full independence is not assumed for them.

`cones_eq_of_restrictedRoots_eq` applies the published congruence laws for
finite positive and nonnegative combinations. It allows all presentation
choices to differ and requires only equality of their restricted-root
sets. Locally finite type supplies the already-proved finiteness witnesses.

`parabolicRootPresentationIsoStatement_of_independence` proves the exact
published universal component-isomorphism proposition from the exact
published universal independence proposition. Given arbitrary compatible
presentations `r` and `s` of the two component maps, it pulls `s` back to
the component map of `r`. Independence compares `r` with this new
presentation. The local two-direction image equalities then give all six
required equalities, in the order of the published target. Smoothness and
affineness come from connected reductivity. No presentation-existence
premise is used: the theorem starts with the two presentations quantified
by the target.

`parabolicRootPresentationStatement_iff_existence_independence` extracts
the first two aggregate conjuncts in one direction and supplies the third
by the preceding theorem in the other direction. Its right side still
requires the full arbitrary-field existence and independence
propositions. The equivalence does not prove the aggregate.

All results retain arbitrary characteristic, nonsplit ambient connected
reductive groups and rank zero. The cones remain the actual finite sums
in the full real character space. There is no new root-convention,
central-direction or representation-theoretic assertion.
