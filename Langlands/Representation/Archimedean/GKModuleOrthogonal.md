# Orthogonal complements and scalar commutants for algebraic GK modules

This is an internal algebraic support module for Task 7158. It does not prove
irreducibility of any particular standard module.

The orthogonal-complement construction is extracted from the proved abstract
section of the Library module `ComplexTemperedComplement`, with its purely
algebraic prerequisites imported from `ComplexPermutationEndomorphism`.
The new module imports neither a Langlands quotient statement nor a proof of one.
It leaves all existing modules unchanged.

For a complex representation in which every vector has finite-dimensional orbit
span, assume a linear functional separates vectors along their group orbits.
Its composition with equivariant maps from a finite-dimensional invariant
subspace gives an injection into that subspace's dual. Consequently the sum of
all equivariant images of a vector's orbit span is finite-dimensional.

Let `B` be sesquilinear, linear in its first argument, invariant under the group,
and diagonally anisotropic (`B v v = 0` implies `v = 0`). A positive definite
Hermitian form satisfies this last condition; the proof uses no stronger
positivity or symmetry hypothesis. Finite-dimensional Gram projections exist
by injectivity and dimension comparison. Projecting inside the saturation,
and then onto the orbit spans of arbitrary vectors in an invariant subspace,
shows that the subspace and its orthogonal sum to the whole space. Diagonal
anisotropy makes their intersection zero.

`EndomorphismsAreScalar` and `HasInvariantComplements` are proposition-valued
properties of actual simultaneous group and Lie actions. The main algebraic
criterion proves that a nonzero module satisfying both properties is
irreducible: its projection onto an invariant subspace commutes with both
actions, so it is scalar; a zero scalar forces the subspace to be zero and a
nonzero scalar makes the projection surjective.

The additional adjoint lemma proves Lie invariance of orthogonals whenever
each Lie operator has an adjoint from the same action up to a scalar. Combining
this with the group complement construction proves
`hasInvariantComplements_of_form`. These are internal derived results with
the implemented projection proof described above, not statements quoted from
an external source.

The shared orthogonal-complement implementation retains its existing
`Langlands.Archimedean.ComplexTemperedComplement` declaration namespace.
`ComplexTemperedComplement` imports this module instead of duplicating its
abstract section. The new generic irreducibility interfaces retain the
`Langlands.Archimedean.GKModuleOrthogonal` namespace.
