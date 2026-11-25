# Generic closure closedness from the connected-fibre theorem

This internal conditional construction uses the actual generic-image closure
of `SmoothTargetGenericClosure`. The base is any Dedekind domain `R` with a
chosen fraction field `K`, the source `M` is reductive, the target `G` is
smooth and affine over `Spec R`, and the homomorphism `f : M → G` is monic
on underlying schemes. All objects lie in an arbitrary universe `u`.

The key additional premise is the unchanged Library proposition
`ConnectedFibreLocusClosedStatement`. This module does not prove that premise.
The generic closure module supplies smoothness of the closure and reductivity
of all its geometric identity components without using this premise.

The generic fibre of the closure is isomorphic to the generic fibre of `M`,
which is connected reductive. The actual fraction-field-to-generic-residue-field
comparison transfers connectedness to the generic residue fibre. Applying the
supplied connected-fibre theorem then shows that every actual residue fibre of
the closure is connected.

In each residue fibre the canonical factor is open by base change and closed
by the field closed-embedding theorem. Its source is nonempty and its target is
connected, so its clopen range is the entire target. The fibre factor is
therefore an isomorphism. The published fibrewise isomorphism criterion makes
the global factor an isomorphism on underlying schemes.
`factorIsoOfConnectedFibreLocusClosed` retains the resulting actual group-scheme
isomorphism, and its composite with the closure inclusion is the original `f`.
The closed inclusion of the closure now proves closedness of `f`.

The last theorem specializes this conditional result to matrix representations
over discrete valuation rings and proves
`ConnectedFibreLocusClosedStatement → ReductiveDvrMatrixMonomorphismStatement`.
It retains the entire connected-fibre premise and does not prove either
statement unconditionally or `ReductiveMonomorphismClosedImmersionStatement` for
arbitrary separated targets.

The provenance is internal composition of the named Library interfaces,
group-scheme base change, and elementary topology of connected spaces.
