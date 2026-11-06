# Coherent linear coordinates on actual Galois root orbits

This internal construction extends stabilizer-compatible coordinates to an
entire actual Galois root orbit. It uses the existing actual coefficient
action, all-test weight transport, and the proved split maximal-torus
root-line coordinate. Its fields and group schemes have arbitrary
universe `u`.

The auxiliary `Langlands.LinearAlgebra.OrbitLines` construction starts
with a group acting on an index set and a vector fixed by the stabilizer
of one index. Choose a transporter for each point of its orbit and apply
it to that vector. Two transporters differ by an element of the original
stabilizer. Consequently `basisVector_eq_smul` proves independence of this
choice, and `basisVector_smul` proves equivariance of the entire family.
For a semilinear coefficient action preserving a family of vector lines,
a nonzero base vector in the original line therefore yields a linear
equivalence from the coefficient field to each line. The theorem
`linearEquiv_smul` proves equivariance for the same family, including maps
between distinct lines. The auxiliary vector and index universes are
independent.

For the actual application, let `G/k` be affine connected reductive and
`j : T.toGrp ⟶ G` a maximal torus. Let `L/k` be finite and suppose `T_L`
is split. Fix an actual root `beta` of `j_L`. The image of `1` under
`splitRootWeightEquivariantLinearEquiv` is a nonzero vector in its actual
adjoint weight space fixed by the ordinary character stabilizer. The
actual Lie coefficient action transports this weight space to each
Galois conjugate weight space; this follows from the intrinsic all-test
action-weight transport and its conjugation comparison. The proved
`finrank_splitRootWeight_eq_one` supplies the dimension of every orbit
line.

The definition `rootOrbitLineEquiv` gives one `L`-linear coordinate on each
actual weight space indexed by the orbit of `beta`. Its `_galois` theorem
states that canonical coefficient transport by any `sigma` takes the
coordinate `x` in the `gamma` line to the coordinate `sigma(x)` in the
`sigma • gamma` line. No dimension, action on the weight spaces, or
coherent basis is supplied as an input. The finite extension need not
be Galois.

The orbit is the ordinary character Galois orbit. No claim that it equals
a relative-root restriction fiber is made here. These are coordinates
on actual Lie spaces; the module does not identify rational root groups
with field points or construct root valuations or an apartment.
