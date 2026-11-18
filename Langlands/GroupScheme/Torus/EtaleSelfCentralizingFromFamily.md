# Etale self-centralizing maximal tori from a supplied universal family

This internal construction combines published torus lifting, field maximal-torus
existence, closed-centralizer representability and open spreading. It applies to
every scheme `S` in every universe, with a group scheme `G/S` whose structure map
is locally of finite type and separated, and whose actual residue-field fibres
are connected reductive. It also requires an actual supplied universal family
of closed relative-torus subgroups, with smooth parameter scheme over `S`.

`TorusSubgroupModuli.etaleSelfCentralizingTorusNeighbourhood` constructs, for each
`s : S`, the data `EtaleSelfCentralizingTorusNeighbourhood G s`:

- an actual scheme `U`, an etale map `q : U ⟶ S`, and a point `u` with `q u = s`;
- a commutative group scheme `T/U` which is a relative torus;
- a closed inclusion `i : T ⟶ G_U` into the literal pullback along `q`;
- maximality of the literal inclusion on every actual residue-field fibre;
- representation of the full centralizer of `i` by `i` itself.

The last clause is the all-test `IsRepresentedBy` property, including every
relative test scheme and every further refinement. No global affineness of `G`
or smoothness of its centralizer is assumed. The supplied family's existence
remains an explicit input. This construction does not prove
`ReductiveFiberAffinenessStatement`.

## Implemented proof

At `s`, connected reductivity makes the actual residue fibre smooth and affine.
`TorusExistence.exists_isMaximalTorus` supplies a closed maximal torus over that
residue field. `IsTorus.isRelativeTorus` makes it eligible for `pointedTorusLift`.
The latter gives an actual pointed etale neighbourhood, a closed relative torus,
and a fibre isomorphism with the exact original inclusion square.

`RelativeTorus.IsTorus.commGroupScheme` installs the descended commutative law
on the same actual lifted group. The recovered square transports the original
maximality to the lifted field-valued point, using the source and ambient
isomorphism transport lemmas. The published
`isMaximalTorus_residueFibre_of_fieldPoint` then reflects maximality to the actual
residue fibre at its image. This reflection requires only the closed inclusion;
no smoothness or affineness of the ambient group over the neighbourhood is used.

Connected reductive residue fibres persist under the etale base change by
`connectedReductive_residueFibers_baseChange`. The actual closed centralizer is
supplied by `separatedRelativeTorusCentralizerModel`. The published
`selfCentralizingTorusOpen` produces an open containing the chosen point on
which the torus represents its whole centralizer and is fibrewise maximal.

Restrict the torus to that open and compose the open inclusion with the original
etale projection. The inverse of `baseChangeCompIso` identifies the iterated
ambient pullback with the literal pullback along this composite. Closedness and
fibrewise maximality transport across that ambient isomorphism. The full
centralizer representative transports by
`SubgroupFunctor.IsRepresentedBy.torusCentralizer_of_iso_square`, with identity
source isomorphism. Evaluation of the original pointed-section equation proves
that the resulting etale neighbourhood contains a point over `s`.

This is a derived application of the imported Library constructions, rather than
an additional external-source theorem. General smooth torus-family existence
and the Weyl-affineness argument remain separate inputs to the host task.
