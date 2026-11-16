# Fppf descent of relative tori

For every universe, an actual group scheme over an arbitrary base scheme is
a relative torus whenever its pullback to each member of an fppf cover is a
relative torus. Here a relative torus means an étale form of a finite split
torus, with rank allowed to vary across the splitting cover.
`FppfRelativeTorusDescentStatement` records this proposition, and
`fppfRelativeTorusDescent` proves it by the method
`RelativeTorus.IsTorus.of_fppfCover`.

This is an internal consequence of published Library results, needed for the
fppf descent of the largest subtorus. It does not assume that the original base
or any member of the cover is nonempty, affine, reduced, or noetherian.

The helper `isCommMonObj_of_fppfCover` descends commutativity by comparing the
two products on every relative scheme test. Pull back the given cover to that
test, use the base-change equivalence of group-valued points, and descend
equality of scheme morphisms using subcanonicity of the fppf topology.
This follows the implemented proof of `isCommMonObj_of_etaleCover`.

For `RelativeTorus.IsTorus.of_fppfCover`, smoothness and relative affineness
descend because these properties are local at the target for the fppf topology.
At each point of the base, lift the point to a member of the cover. Its residue
field extends the residue field downstairs, and the two successive pullbacks
agree by the residue-field square and the base-change composition isomorphism.
The upstairs fibre is a field torus. Field-extension reflection of the torus
predicate makes the downstairs residue-field fibre a field torus too.
Its geometric fibre is therefore connected reductive. These facts give
reductivity of the original group scheme.

Finally, package the descended commutative group law on the same actual group
scheme and apply `relativeTorus_of_commutative_reductive`. This recovers an
étale splitting cover without requiring the given fppf cover to be étale.
The proof uses the published commutative-reductive criterion, field/relative
torus comparison, arbitrary field-extension reflection and fppf locality;
it is not asserted as a direct transcription of a literature proof.
