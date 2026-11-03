# Assembly reductions for semisimplicity of the actual derived subgroup

This internal module assembles published elementary results for the proof of
`DerivedSubgroupSemisimpleStatement`. Its inputs are actual morphisms and
their full subgroup functors on all test schemes, over arbitrary fields
and in arbitrary universe `u`.

## Comparing representatives after base change

Let `d : D ⟶ G` exhibit the full derived subgroup of an affine group over
a field, and let `b : S' ⟶ Spec k` be any affine base change. Suppose
`e : E ⟶ G_S'` independently exhibits the full derived subgroup after base
change. `IsDerivedSubgroup.baseChangeIso b hd he` constructs an isomorphism
`D_S' ≅ E`. The published equality
`derivedSubgroup_baseChange_eq_of_field` makes the base change of `d` a
derived-subgroup inclusion. The published comparison
`IsDerivedSubgroup.iso` then compares the two representatives.
`baseChangeIso_hom_comp` proves that the isomorphism commutes with their
inclusions. No local finite type, smoothness or reductivity hypothesis is
needed for this comparison.

## Full centre

Suppose `i : Z ⟶ G` is central, `e : E ⟶ G` exhibits the derived subgroup,
`G` is affine and `subgroupProductMap i e` is an epimorphism. If a closed
map `c : C ⟶ E` represents the inverse image of the full ambient centre
and `C` is finite over the field, then
`hasFiniteCenter_of_centralProduct` proves `HasFiniteCenter D` for every
other exhibiting inclusion `d : D ⟶ G`. The published centre comparison
first identifies `c` as a finite full centre of `E`; the isomorphism of
the two derived representatives transports this property to `D`.
The scheme-theoretic centre retains its nonreduced structure.

## Geometric unipotent radical and reductivity

Let `G` be connected reductive over `k`. Choose an actual derived
subgroup `e : E ⟶ G_kbar` and a central morphism `i : Z ⟶ G_kbar` whose
product with `e` is epimorphic. The theorem
`hasTrivialGeometricUnipotentRadical_of_centralProduct` proves that the
unipotent radical of `D_kbar` is trivial for any supplied actual
derived-subgroup inclusion `d : D ⟶ G`.

Affineness of `G_kbar` follows by pullback. The published normality-transfer
result transfers triviality of the unipotent radical from `G_kbar`,
which is a field of the given reductivity proof, to `E`. The comparison
`baseChangeIso` and invariance under isomorphism transfer it to `D_kbar`.
This argument uses a central product chosen over the algebraic closure;
it does not need to base change an epimorphic product morphism.

With an additional proof `Smooth D.X.hom`,
`isConnectedReductive_of_geometricCentralProduct` constructs
`IsConnectedReductive D`. Its other fields are affineness of a closed
subgroup, the published connectedness theorem for the derived subgroup
of a connected affine group, and the preceding geometric radical theorem.
Smoothness of `G` supplies the local finite type instance needed by the
connectedness theorem.

## Provenance and remaining obligations

These constructions are derived directly from the imported Library
definitions and proved results; no external structural result is introduced.
The comparison isomorphism is the published represented-subgroup
construction specialized using the published field-base-change theorem.
The other proofs compose published normality, centre and connectedness
results with transport along that isomorphism.

This module does not prove `DerivedSubgroupSemisimpleStatement`.
Existence of the central products, finiteness of the full ambient-centre
preimage and smoothness of the actual derived subgroup remain proof
obligations for their independent proof tasks. No unproved Library
statement is invoked as a theorem here.
