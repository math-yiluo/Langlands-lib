# Exact spectral attachment under arithmetic pullback

`cuspidalSpectralArithmeticComap` takes the actual cuspidal realization `S`
and its presentation `P` from the supplied attachment. It uses
`S.arithmeticComap e` as the representative of the pulled-back class and
`P.arithmeticComap e` as its presentation, with the same universe for
the local factors.

The presentation transport pulls back the finite slice equivariantly for
the finite adelic action and reindexes its restricted tensor product and
reference vectors. The completed-field equivalences identify the integral
subgroups and preserve residue cardinalities. The lemma
`LocalRealization.hasSphericalHeckeSpectrum_arithmetic` transports the
normalized spherical Hecke scalar equations on the fixed spaces with the
source eigenvalues at the corresponding places.

By definition the transported system is
`P.spectralSystem.reindex (finitePlaceEquiv e.symm).symm`. The forward
equivalence maps the exceptional set, and the inverse sends a target place
`v` to `finitePlaceEquiv e.symm v` for the eigenvalues. The proof uses
injectivity of `finitePlaceEquiv e` and contravariant composition via
`finitePlaceEquiv_trans` to identify `finitePlaceEquiv e.symm` with
`(finitePlaceEquiv e).symm`. Substituting this equality gives precisely
`P.spectralSystem.reindex (finitePlaceEquiv e)`.

The mathematical source for this derived transport is Arthur–Clozel,
*Simple Algebras, Base Change, and the Advanced Theory of the Trace Formula*
(1989), Chapter III, Definition 1.1 and equation (1.1), printed p. 199
(PDF p. 213), and Proposition 4.4(iii), printed pp. 210–211 (PDF pp. 224–225).
The former describes weak base change via unramified Hecke eigenvalues, and
the latter uses the corresponding identities after Galois conjugation.
The registered source is `arthur-clozel-1989-base-change` with SHA-256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
