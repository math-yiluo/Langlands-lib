# Symmetric adelic test kernels invariant under a compact subgroup at infinity

`Langlands.Global.AdelicGroupPoints.adelicSymmetricCompactInvariantKernel`
proves `AdelicSymmetricCompactInvariantKernelStatement`. Let `G` be a smooth
affine group over a number field, and fix a compact subgroup of its infinite
adelic points. Every identity neighborhood in the adelic group contains the
topological support of a real nonnegative test kernel of Haar integral one.
The kernel is invariant under inversion and under conjugation by the compact
subgroup.

Compactness gives an identity neighborhood at infinity whose conjugates all
lie in the prescribed infinite neighborhood. The proof symmetrizes a smooth
bump in that smaller neighborhood by adding its pullback under inversion,
then averages its conjugates with Haar probability. Smoothness follows by
differentiation under a compact parameter integral. The topological support
lies in the compact image of the product of the subgroup and the symmetric
support bound. On finite adeles the indicator of a compact open subgroup is
inversion invariant and gives both finite translation invariances of the
adelic product. The product is positive at the identity, so its integral
can be normalized to one.

This is an adelic approximate-identity construction. Compact conjugation
averaging gives commuting integrated operators, and inversion symmetry gives
symmetric integrated operators for unitary actions with unimodular Haar measure.
