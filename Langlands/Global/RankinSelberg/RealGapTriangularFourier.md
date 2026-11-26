# The real triangular column Fourier identity

This module is the real counterpart of the Library's `ComplexGapTriangularFourier`; its
declarations lie in the namespace `Langlands.Global.RankinSelbergGlobal.RealGapColumnFourier`.

Let the ambient column have `k + q + 1` entries, with a leading block of size `k` and a tail of size
`q + 1`. On the ordinary side `directColumn k q X Z j` is the column `j + 1` of the tail of the upper
block matrix with identity leading block, upper right block `(0 | X)` for a free `k × q` rectangle
`X`, and upper unipotent lower right block `Z`. On the Fourier side `transposeColumn k q Z j` is the
column `j` of the transposed tail block, with zeros in the leading rows.

* `triangularOrdinary a g Φ (X, Z) = (∏_j Φ_j (g · directColumn X Z j)) · ψ_a(Z)`, where `ψ_a(Z)` is the
  standard character `Whittaker.standardCharacter (realScaledCharacter a) q Z` (the character of the
  sum of the simple-root entries).
* `triangularFourier a g Φ Z = (∏_j 𝓕_a Φ_j (g^{-T} · transposeColumn Z^{-1} j)) · ψ_a(Z)`, where `𝓕_a`
  is the Library's positive real Fourier transform `realFourierTransform a`.

`measurePreserving_entryHaar_inv` proves that the entry Haar measure `entryHaar μ (q + 1)` on
`N_{q+1}(ℝ)` is invariant under inversion: transpose followed by conjugation by the long Weyl element
(`transposeReflection`) preserves it and exchanges left and right translations, so the measure is
right invariant and hence inversion invariant.

`RealGapTriangularFourierStatement` (proved by `realGapTriangularFourier`): for `a : ℝˣ`,
`g ∈ GL_{k+q+1}(ℝ)` and Schwartz column tests `Φ_j` (`j < q`), with `μ = realSelfDualMeasure a`,
`triangularOrdinary` is integrable for the product of the rectangular measure and
`entryHaar μ (q + 1)`, `triangularFourier` is integrable for `entryHaar μ (q + 1)`, and

`∫ triangularOrdinary = (|det g|^{-1})^q · ∫ triangularFourier`.

The proof applies `realGapColumnFourierProduct` with the partitions `beforePivot k q j`, the fixed
frequency the unit vector at the preceding pivot and the fixed position the unit vector at the pivot,
and transports both sides by `realGapColumnCoordinates`. Each pairing extracts one simple-root entry
of the tail, so the product of the column characters is the standard character. The Fourier side
first carries the transposed tail and `ψ_{-a}`; the substitution `Z ↦ Z^{-1}`, which preserves the entry
Haar measure, negates the simple-root sum and restores `ψ_a` (`psi_neg`).
[Jacquet, *Archimedean Rankin–Selberg integrals*, Section 10.2, Lemma 10.2](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
