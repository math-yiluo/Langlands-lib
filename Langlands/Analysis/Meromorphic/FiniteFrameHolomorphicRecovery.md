# Holomorphic recovery in a finite frame

`recoverFromFrameTests` applies the frame to the adjugate of the square matrix of tests
applied to the prescribed vector of test values, with the coefficients divided by the
determinant. Its recovery property is used where the determinant is nonzero.

`exists_isHolomorphicOn_smul_of_frame_tests` recovers a weakly holomorphic extension of a
scalar multiple of a family of vectors. On the set where agreement is required, the vectors
lie in a weakly holomorphic finite frame. The tests are continuous scalar linear forms that
may depend on the parameter. Their evaluations on the frame columns are holomorphic, they
separate the frame coefficients at the center, and each test of the scaled family has a
holomorphic extension on its own neighborhood of the center.

The lemma is derived from the scalarization in Bernstein–Lapid, *On the meromorphic
continuation of Eisenstein series*, Appendix A, pp. 230–231
(`bernstein-lapid-2024-meromorphic-continuation-eisenstein`). It uses the matrix lemmas
in `LocalScalarization`. The proof chooses a square matrix of tests whose determinant is
nonzero at the center. It intersects the determinant's nonvanishing locus, the frame
neighborhood and the neighborhoods for the finitely many selected tests. The recovery
formula gives holomorphic coefficients there. Applying any continuous linear form to
the recovered vector expresses its value as a finite sum of products of holomorphic
functions. The matrix identity for the adjugate proves agreement on the required set.
The same open neighborhood works for all continuous linear forms.

For pole detection, the tests can include both the defining equations of an analytic
system and scalar evaluations of its cuspidal components. Multiplying the system's
right-hand sides by a holomorphic clearing factor gives extensions for the equation
rows. The cuspidal tests then need to separate vectors in the frame satisfying the
homogeneous equations at the center.
