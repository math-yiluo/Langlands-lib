# Poles and vertical-strip bounds over totally complex number fields

`Langlands.Global.CuspidalPairPoles.cuspidalPairPoleTC` proves
`Langlands.Global.CuspidalPairPoleTCStatement.{u, uQ}`. The theorem gives the
existence of the finite factor data and the archimedean parameters. For every
choice of the prescribed factors it gives a completed L-function that is
holomorphic away from \(0\) and \(1\) and bounded on vertical strips outside
discs about the two points. It has at most a simple pole at each of the two
points, with poles exactly for an equal-rank contragredient pair.
[Target statement](CuspidalPairPoleTCStatement.md)

## Proof

At a totally complex field the type of real places is empty. The unequal-rank
argument uses `infiniteWhittakerSliceModelAt_of_isTotallyComplex` for the two
cuspidal presentations, with the adelic character and its inverse.
`complexUnequalPlaceTests_of_ordinary` combines the complex ordinary tests with
the complex local functional equation to obtain ordinary and dual integrals
that are holomorphic and not identically zero on a right half-plane.
`unequalInfiniteWhittakerTest_of_placeData` assembles these
complex-place tests into a product test for the two slices. The finite
separation step `unequalPointwiseOfInfiniteTestsAt` then gives the pointwise
factorization at the same field.

`unequalArchimedeanFactorizationAtReduction` integrates the pointwise
factorization. `UnequalSemilocalArchimedeanReduction.factorization_of_at`
combines it with the local functional equations and the central sign to supply
the factorization premise of `unequalSemilocalEquationTC_of_factorizationTC`.
For equal ranks, `equalSemilocalEquationTC_of_ordinaryGeneration` supplies the
semi-local equation from `complexOrdinaryNormalizedGeneration`.

The two semi-local equations and the global analytic, unfolding, and ordinary
and dual Euler factorization theorems give the partial functional equation by
`cuspidalPairPartialGammaGlobalTCReduction`. The reduction
`cuspidalPairPartialGammaTCReduction` restores the missing finite factors and
gives the completed equation.

`cuspidalPairPoleTCRemainingInputs` uses this equation, complex ordinary
generation, the slice model at each totally complex field, and complex
restriction surjectivity. It supplies complex normalized continuation and strip
growth through `complexOrdinaryNormalizedAllGrowth`. The ordinary tests provide
local normalized values covering every spectral point, and the equal-rank
tests include the residue witness. The pole reduction uses the Euler product
on the right, the completed equation on the left, and the growth of a matching
normalized test to apply Phragmén–Lindelöf after clearing the possible poles.
[Local-test reduction](CuspidalPairPoleFromLocalTests.md)
[Strip argument](CuspidalPairPoleTCReduction.md)

## Provenance

- J. Getz and H. Hahn, *An Introduction to Automorphic Representations* (2024),
  `getz-hahn-2024-automorphic-representations`, SHA-256
  `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
  The product is (11.23), printed p. 308 (PDF p. 319). The pole profile under the
  split-centre hypothesis is in Theorem 11.7.1, printed p. 309 (PDF p. 320).
  The split component is defined at (2.20), printed p. 68 (PDF p. 85).
- J. W. Cogdell, *Analytic theory of L-functions for GL_n* (2004),
  `cogdell-2004-analytic-theory-gln`, SHA-256
  `8117f145869274324b12344dc83fa3289e3bd27c515b8d0d4a0211cd64174944`.
  The ordinary global integrals, their local ratios, and the product of the
  local equations follow the proof of Theorem 4.1, printed pp. 219–220
  (PDF pp. 222–223). The pole argument is in §4.2, printed pp. 221–222
  (PDF pp. 224–225). The strip conclusion is item 2 of Theorem 4.1, with the
  discussion on printed pp. 220–221 (PDF pp. 223–224). The Library obtains that
  conclusion by the Phragmén–Lindelöf argument described above.
- H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009),
  `jacquet-2009-archimedean-rankin-selberg`, SHA-256
  `7a11766eadf25fb7452ce7faa193469791796f572fc654c8fe90a8608bb46afe`.
  The complex local analytic and generation inputs come from Theorems 2.1,
  2.3, 2.6 and 2.7, author-posted pp. 6, 8, 9 and 10.
