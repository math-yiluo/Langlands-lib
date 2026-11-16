# Finite coefficient models of quasi-finite flat surjections

This internal auxiliary combines the simultaneous smooth affine homomorphism
model with finite coefficient descent of local quasi-finiteness, flatness and
surjectivity. The exact recovery square transfers each isomorphism invariant
scheme property from the supplied map to the base change of the model.
The three properties then descend together to a finitely generated coefficient
subalgebra. Both groups remain smooth and affine after this enlargement.

`QuasiFiniteSmoothAffineHomModel` stores this data and the three properties of
its actual model homomorphism. Its `enlargeTo` construction preserves those
properties using the cartesian square of group base change.

If the original supplied groups `G` and `H` are reductive, then
`DirectLimitReductiveStatement` as an explicit premise implies that both model
groups are eventually reductive in the directed system of all finitely generated
coefficient subalgebras. A common upper bound of the two eventual stages gives
one model with both groups reductive. No finiteness assertion about the map is
used.

The provenance is internal composition of the Library's smooth affine
simultaneous model, structural property descent, subalgebra colimit and
direct-limit reductivity interfaces. Homomorphism descent and direct-limit
reductivity remain explicit premises.
