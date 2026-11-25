# Uniqueness of isobaric weak base change from Euler constituent recovery

`Langlands.Automorphic.Unramified.IsobaricWeakBaseChangeUniquenessTCStatement`
says that totally complex Euler constituent recovery implies uniqueness of
actual isobaric weak base change. For an extension of number fields `E/F`
with compact adelic quotients and `E` totally complex, any two weak base
changes to `E` of the same datum over `F` are equal. Equality is equality of
multisets of cuspidal classes and retains multiplicities. The proposition has
two independent field universes and two independent presentation-carrier
universes. `isobaricWeakBaseChangeUniquenessTC` proves this reduction using
`IsobaricData.IsWeakBaseChangeOf.unique_of_eulerConstituentRecoveryTC`.

This is the uniqueness step of the Library's isobaric formulation of
Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the
Trace Formula* (1989), Theorem III.4.2(c), printed p. 202 (PDF p. 216).
The proof of (c) on printed p. 206 uses irreducibility of unitary parabolic
induction and the earlier comparison (2.4) on printed p. 200. The conditional
proposition isolates the comparison on constituent data as the Library's
Euler constituent recovery premise.
The registered source is `arthur-clozel-1989-base-change` with SHA256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
The argument serves prime cyclic unitary isobaric base change over totally
complex fields (module
`Langlands.Automorphic.Unramified.CyclicPrimeIsobaricBaseChangeTCAssembly`).

`IsobaricData.IsWeakBaseChangeOf.unique_of_eulerConstituentRecoveryTC`
uses `IsobaricData.HasSpectralSystem.sameEulerPolynomials` to compare the
two attachments of the base-field datum. That theorem compares the
products of the constituent Euler factors with their multiplicities.
The resulting cofinite agreement puts both lifts over one base-field
spectrum via `IsArithmeticWeakBaseChangeOf.of_sameEulerPolynomials`. The
map sending an upper finite place to its place below preserves the cofinite
filters. At every upper place in the resulting cofinite set, both
attachments have the same spectrum, given by the residue-degree power at
the place below. Rank transport preserves the corresponding Euler
polynomials. Applying the supplied `CuspidalEulerConstituentRecoveryTCStatement`
over the totally complex upper field identifies the upper constituent
enumerations up to a bijection, which gives equality of their multisets.
