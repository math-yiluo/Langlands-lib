# Weak base change of one unitary cuspidal class over a totally complex base

`Langlands.Automorphic.Unramified.CyclicPrimeCuspidalBaseChangeExistenceTCStatement`
is a proposition definition over number fields `F : Type uF` and `E : Type uE`
with compact adelic quotients. The base `F` is totally complex and `E/F` is
Galois of prime degree. For each `c : PositiveRankCuspidalClass F` whose
singleton `IsobaricData.ofCuspidal c` is unitary, it asks for unitary
`DE : IsobaricData E` with
`IsobaricData.IsWeakBaseChangeOf.{uF,uE,uV,uW} DE (IsobaricData.ofCuspidal c)`.
The upper datum comes first. The relation includes equality of total ranks
and spectral systems attached to the actual classes, with independent
presentation-carrier universes `uV` over `F` and `uW` over `E`. It compares
the unramified data away from finitely many places.

This is a derived existence target from Arthur–Clozel, *Simple Algebras,
Base Change, and the Advanced Theory of the Trace Formula* (1989),
III.4.2(a)–(b), printed p. 202, and their proofs on pp. 203–206. For a
character with kernel the idele class norm image, the proof route applies
the two branches of the joint rank induction to the determinant self-twist
dichotomy. The witnesses are the attached upper cusp in (a) and the
attached full Galois orbit of upper cusps in (b), encoded by
`IsobaricData.ofCuspidal` and `IsobaricData.galoisOrbit`, respectively.
The proposition leaves the shape of the witness implicit. It leaves
constituentwise assembly and Euler-comparison uniqueness to the full totally
complex form of III.4.2(c), `CyclicPrimeIsobaricBaseChangeTCStatement`, whose
assembly from singleton lifts is `CyclicPrimeIsobaricBaseChangeTCAssembly`.

The registered source is `arthur-clozel-1989-base-change`, SHA-256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
