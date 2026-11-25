# The two strict-Henselian fibral branches from clopen lifting

These internal constructions take
`MultiplicativeTypeStrictHenselianLiftStatement` as an explicit input. The
commutative construction also takes
`MultiplicativeTypeTorsionDeterminationStatement` explicitly. Neither
proposition is asserted or supplied here; the Library proves them in
`MultiplicativeTypeStrictHenselianLiftProof` and
`MultiplicativeTypeTorsionDeterminationProof`.

Let `A` be any strictly Henselian local ring, and let `H` be a flat, locally
finitely presented affine group scheme over `Spec A` with every geometric
fibre of multiplicative type. Fix a finitely generated abelian character
group `M` and an actual diagonalization of the special fibre from
`(D_A(M))_k` to `H_k`, using the ring-theoretic residue-field quotient.

`StrictHenselianFibral.connectedDiagonalization` returns an actual
isomorphism `D_A(M) ≅ H`, retaining that exact prescribed special-fibre
homomorphism, if every residue fibre of `H` is connected. The lifting
proposition supplies a clopen embedding, and `clopenConnectedFibersIso`
makes it invertible. No commutativity or smoothness premise on `H` is used.

`commutativeDiagonalization` supplies the same actual isomorphism when `H`
is commutative and each positive geometric torsion coordinate order is
locally constant. The given special-fibre isomorphism remains invertible
on the chosen closed geometric fibre by `LocalSpecialGeometricFiber`.
Its induced torsion isomorphisms identify coordinate dimensions at that
point: both torsion schemes there are finite flat, so their coordinate
dimensions are their native ranks, which are invariant under isomorphism.
Local constancy propagates these equalities over the local spectrum.
`FibralClopen.isoOfLocallyConstantTorsionOrders`, with the explicitly
supplied torsion-determination proposition, then makes the clopen embedding
an isomorphism.

Both outputs are noncomputable choices of actual diagonalizations together
with proof of the exact special-fibre equality. The character group may
have torsion, and `A` need not be Noetherian, complete or reduced. Neither
construction asserts uniqueness. The special-fibre diagonalization remains
input data; its existence is not established by this module.

This is a derived internal assembly of the local lifting proposition,
actual special/geometric comparison, finite-flat torsion geometry and the
two clopen-isomorphism constructions. It does not prove either explicit
prerequisite proposition, strict-Henselian-to-general-base locality or the
full fibral criterion.
