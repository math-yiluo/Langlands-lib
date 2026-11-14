# Affine extensions of actual integral Cartan matrices

`transitiveIntegralCartanExtension` chooses an affine extension of
the exact integer Cartan matrix of a supplied base `b` of an actual integral
root datum. The group is over an arbitrary field, the torus is split and
included, and the actual relative-root set is finite. The supplied root datum
is reduced and has an `IsRootDatumOf` witness on the actual torus lattices.

The affine root system is supplied on a torsor for the actual reduced real
cocharacter space. Its full derivative set must equal the range of the actual
root forms. The theorem assumes a regular chamber point, nonempty roots,
irreducibility, vertex transitivity of the chamber Cartan matrix, indivisible
affine lifts of all full derivatives, and transitivity of the simple affine
roots under root-preserving affine pullbacks. These are premises, not new
existence results for actual buildings or Galois actions.

The resulting integer matrix is indexed by `Option b.support`. Its block on
`some` is literally `b.cartanMatrix`, its diagonal is two, its off-diagonal
entries are nonpositive, and its zero pattern is symmetric. A strictly positive
integer vector belongs to its left kernel, and entry-preserving permutations
act transitively on its indices.
`transitiveIntegralCartanExtension_spec` proves all these properties for the
chosen matrix. The supporting existence theorem is
`exists_transitive_integralCartanExtension`; the definition chooses its witness
by classical choice, and the specification is the corresponding choice
specification.

The implemented proof chooses any simple affine root using nonemptiness.
The imported indivisible-lift and transitivity results show that deleting it
leaves an independent integral generating family and the support of a base of
the full rational derivative pairing. The actual integral-to-derivative base
comparison identifies the supplied integral base with that derivative base,
preserving the exact integer Cartan entries. Finally,
`exists_transitive_cartanExtension_of_simpleDerivativeBase` reindexes the actual
chamber matrix by this identification and the deleted node. Its existing
proof transports the generalized Cartan inequalities, positive marks and
matrix transitivity.

This is an internal composition of the imported constructions. It does not
supply the affine system, actual irreducibility, lifts, chamber transitivity,
splitting, or the identification of an absolute Tits-index base after field
extension. Those remain obligations of the host local anisotropic theorem.
