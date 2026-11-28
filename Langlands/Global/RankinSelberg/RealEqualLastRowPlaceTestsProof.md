# Ordinary nonvanishing for equal ranks at a real place

`Langlands.Global.RankinSelbergGlobal.realEqualOrdinaryPlaceTests` proves
`RealEqualOrdinaryPlaceTestsPositiveRankStatement.{u}`. For two cuspidal realizations
of `GL_(r+1)` with `0 < r` and the given real-place parameters, it produces actual
Whittaker restrictions for opposite characters, a last-row Schwartz function, and
compatible quotient measure data. These fixed data give a nonzero ordinary integral
at some spectral point in every right half-plane.

The real branch of `archimedeanActualWhittakerIntertwiners` gives an intertwiner `B`
whose coefficients are actual restrictions, and a compact-finite vector `f` with
`B f (1) = 1`. Applying `cuspidalWhittakerIdentityNonzero` to the inverse adelic
character gives an actual restriction `W'` with `W'(1) ≠ 0`. The proof uses
`realPlaceUniformWhittakerModel`, `realUniformWhittakerRegularity`, and
`RealWhittakerTranslatedMellin.hasGaugeBound_of_mem_model` to obtain the opposite
left-character relations, continuity, and gauge bounds for the descent.

Suppose the equal-rank integrals against `W'` vanish on right half-planes for
every coefficient `B p` and every Schwartz test. For each `B p`,
`realEqualLastRowDescent` gives vanishing for the integral of ranks `r+1` and `r`
against the padded restriction of `W'`, with the spectral parameter decreased by
`1/2`. The measure data at each rank are `realQuotientMeasureData`.
`RealUnequalPositiveRank.descent_to_rankZero` iterates the smaller-rank restriction
down to `GL₁`, and `UnequalAnalytic.padGL_padGL` identifies the result with the
direct restriction `V₀` of `W'` to `GL₁`.

`Langlands.Archimedean.rightDerivative_mem_kFiniteFunctions_realStandardModule`
keeps the derivative of `f` along the first simple root in the compact-finite
module. The intertwiner sends this derivative to the right derivative of `B f`.
Two applications of `exists_integrable` give a common right half-plane of
integrability for both ordinary `GL₁` integrands. Their vanishing and
`RealUnequalRankZero.value_eq_zero_of_integrals_eq_zero` force
`B f (1) · V₀(1) = 0`, contradicting `B f (1) = 1` and `V₀(1) = W'(1) ≠ 0`.

The equal-rank step uses the last-row coordinates and determinant power in
Jacquet's *Archimedean Rankin–Selberg Integrals* (2009), equations (2.4) and (2.6)
and the equal-rank part of Lemma 14.1.
[Equal-rank last-row descent](RealEqualLastRowDescent.md) ·
[Unequal-rank nonvanishing](RealUnequalOrdinaryPlaceTestsProof.md)
