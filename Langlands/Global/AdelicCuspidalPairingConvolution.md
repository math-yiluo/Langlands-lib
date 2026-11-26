# Compact convolution and norm-one cuspidal pairings

`Langlands.Global.StandardParabolicFamily.HasCompactLeviPairingMajorant`
requires one integrable function on the norm-one rational Levi quotient that
bounds the absolute value of the pairing integrand. For almost every Levi
class, the bound must hold at every right translate \(gt\) with \(t\) in
the specified set.

For continuous input and test functions that are left invariant under the
rational Levi, `leviPairingIntegrand_mk_of_leviInvariant` computes the
integrand on any norm-one representative. The proof uses this equality
and the open quotient map to obtain joint continuity in the Levi class
and the right translation variable.

In `leviPairing_rightConvolution_of_compactMajorant` the second Haar
measure is restricted to the compact support of the kernel. The joint
integrand is bounded there by the product of the majorant and a bound
for the kernel. The restricted measure is finite, so the product bound
gives absolute integrability. Fubini proves both integrability of the
convolved pairing and the equality with the right convolution of the
scalar pairings. `InCuspidalAnnihilator.rightConvolution_of_compactMajorants`
then applies the identity to every Levi cusp test, assuming the stated
majorant for each test and each base point.

The construction uses the norm-one pairings of Bernstein–Lapid, *On the
meromorphic continuation of Eisenstein series*, (6.8), pp. 201–202, and
the convolution step of Mœglin–Waldspurger, *Spectral Decomposition and
Eisenstein Series*, I.4.5, printed pp. 60–62
(`bernstein-lapid-2024-meromorphic-continuation-eisenstein-published`,
SHA-256 `6acbe78adf3a7ddff4be0caa92b169f0e609d1245f674a71fbc6989d6aef9268`,
and `moeglin-waldspurger-1995-spectral-decomposition`, collection
fingerprint `1ba99fb90916a687503e88c7191dad43b9c4865b68e6b4221a4f2126f2d2f141`).
