# Rigidity of cuspidal inducing data from Euler constituent recovery

Authors — Worker 3657 and Worker 288.

`Langlands.Global.CuspidalInducingDataRigidityReductionStatement.{u, uQ}` is the
implication from `Automorphic.Unramified.CuspidalEulerConstituentRecoveryStatement.{u, uQ}`
to `Langlands.Global.CuspidalInducingDataRigidityStatement.{u, uQ}`. The theorem
`Langlands.Global.cuspidalInducingDataRigidity_of_constituentRecovery` proves the
implication with Euler constituent recovery as its sole premise. The consequent
is the published target of Task 6447 with all its hypotheses. The universe `u`
covers the number field and local carriers, and `uQ` covers the factors in the
spectral presentations.

## Proof

1. Form the two lists of full positive-rank classes `c i = ⟨m i, (T i).isoClass⟩`
   and `d j = ⟨m' j, (T' j).isoClass⟩`. The given presentations witness the
   attachment of their spectral systems to these classes through
   `CuspidalOperatorRealization.IsoClass.hasSpectralSystem_iff`.
2. Work at a finite place outside `S` where both finite sums of spectral systems
   are defined. Each sum has the union of its summands' exceptional sets as its
   exceptional set. `hasSphericalSpectrum_padicObject` identifies the eigenvalues
   there with spherical spectra of the canonical p-adic objects. On this domain
   the spectral attachments supply the sphericity of each block.
3. Apply `exists_hasSphericalSpectrum_of_isSubquotientOf_productInduced` to the
   common `A` on each side. Each application identifies a spectrum of `A` with
   the concatenation of the block spectra on that side. By
   `sphericalSpectrumUniqueness`, the spectra of `A` agree. Taking the product of
   the factors `1 - z X` over either concatenated multiset gives the same Euler
   polynomial. Cofiniteness of the complement of `S` gives `SameEulerPolynomials`.
4. Apply the Euler recovery premise to the lists with their supplied attachments.
   The resulting equivalence of the two index types matches the ranks and full
   cuspidal classes, including repeated classes with their multiplicities.

## Provenance

The implication follows the passage from the common spherical subquotient to
constituent recovery in Jacquet–Shalika II, Theorem (4.4). The proof of their
display (1) is the local spectrum comparison. The Lean argument passes from
that equality to Euler polynomials, the numerical input used in place of the
positive power traces in display (2). The recovery premise packages the step
from the numerical equality to a permutation of the original lists, represented
by displays (3) and (4) and the closing argument on p. 809. Getz–Hahn present the
rigidity theorem for normalized inductions in Theorem 10.7.2 and explain the
passage to cuspidal blocks with determinant twists absorbed on the next page.

- H. Jacquet and J. A. Shalika, *On Euler products and the classification of
  automorphic forms II*, Amer. J. Math. 103 (1981), proof of Theorem (4.4),
  displays (1)–(4), printed p. 809 (registered `jacquet-shalika-1981-euler-ii`, PDF p. 34).
- J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations*,
  Springer (2024), Theorem 10.7.2, printed p. 287, and the formula expressing
  `π_i` as a determinant twist of `π_i^1` on printed p. 288
  (registered `getz-hahn-2024-automorphic-representations`, PDF pp. 299–300).
