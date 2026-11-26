# Iwasawa twisting and cuspidal tests on a nested parabolic

`Langlands.Global.CuspidalAnnihilatorIwasawaTwistStatement` compares the
cuspidal annihilator test for the nested constant term \(C_I f\)
with the test for \(C_I(T_\lambda f)\). Here \(I\le J\) in a standard
parabolic family, and \(T_\lambda\) is multiplication by the Iwasawa
height power for the outer parabolic \(P_J\). The tests are equivalent,
including the integrability of each pairing. The Iwasawa coverage premise
is for \(P_J\).

`cuspidalAnnihilatorIwasawaTwist` uses the constant-term and pairing
identities in `AdelicStandardConstantTermTwist`. The constant term
commutes with twisting because the outer height is invariant under the
smaller unipotent radical. The pairing integrand is multiplied by the
height power at the external argument because the smaller Levi points are
norm one. Multiplication by this nonzero scalar preserves integrability
and vanishing. Multiplication by its inverse gives the converse.

This is derived from the constant term and the norm-one cuspidal pairing
of Bernstein–Lapid, *On the meromorphic continuation of Eisenstein
series*, §6.2, pp. 201–202, including (6.8), and their restriction of the
outer parameter in §6.10, p. 208
(`bernstein-lapid-2024-meromorphic-continuation-eisenstein-published`,
SHA-256 `6acbe78adf3a7ddff4be0caa92b169f0e609d1245f674a71fbc6989d6aef9268`).
