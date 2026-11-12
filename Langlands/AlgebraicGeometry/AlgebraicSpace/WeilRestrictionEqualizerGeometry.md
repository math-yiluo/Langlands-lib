# Quasi-affine equalizer loci for algebraic spaces

Author: Worker 117.

This internal module supports the equalizer proof of the Weil-restriction
diagonal theorem. `WeilRestrictionDiagonalGeometry.relative_diagonal_with_mono`
adds the monomorphism property to every represented projection of any presheaf
diagonal already satisfying a specified scheme property. It uses the fact that
a diagonal is mono, stability of monomorphisms under pullback, reflection by
the faithful scheme Yoneda functor, and passage from a slice morphism to its
underlying scheme morphism.

The main corollary
`WeilRestrictionDiagonalGeometry.exists_quasiAffine_representsEqualizer` says:
for a quasi-separated algebraic space over an arbitrary scheme, and two sections
over an affine test scheme, their equality locus is represented by a
quasi-affine scheme. Its projection to the test is a monomorphism, locally of
finite type, and quasi-compact. Representing the equality locus means
factorization for every scheme test in the full slice, as specified by
`RepresentsEqualizer`. Together with the monomorphism assertion, this also
provides uniqueness of the factorization.

The proof combines the definition of quasi-separatedness with
`locallyOfFiniteType_diagonal` from `WeilRestrictionDiagonalGeometry`, then
adds the monomorphism property. The published theorem
`exists_representsEqualizer_of_relative_diag` supplies the represented locus
with all three scheme properties at once. Quasi-compactness of its projection
to an affine test makes its source compact. A scheme monomorphism is separated
and formally unramified. The published theorem
`GenericFiniteness.locallyQuasiFinite_of_formallyUnramified` gives local
quasi-finiteness. Finally,
`LocallyQuasiFiniteDescent.isQuasiAffine_of_locallyQuasiFinite` applies the
quasi-affine form of Zariski's Main Theorem.

Provenance: these are internal consequences of published Library diagonal,
equalizer and scheme geometry APIs, together with Mathlib categorical
monomorphism facts. No finite type hypothesis is added to the algebraic space,
and no restriction on the universe, base scheme, or non-affine tests in the
factorization assertion is made. This module does not assert representability
of any Weil-restricted algebraic space.
