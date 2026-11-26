# Proof of ordinary nonvanishing at a complex place in unequal ranks

`Langlands.Global.RankinSelbergGlobal.complexUnequalOrdinaryPlaceTests` proves the
published `ComplexUnequalOrdinaryPlaceTestsStatement.{u}` with the field universe
free, for every pair of ranks \(t<r\).

## The local nonvanishing theorem

`exists_complexUnequalIntegral_ne_zero_above` takes a Whittaker intertwiner \(B\)
of the compact-finite standard module for the parameter `d` and the character
\(\psi_a\), a vector \(v\) with \(Bv(1)\ne0\), and a function \(V\) of the
compact-finite model for `e` and \(\psi_{-a}\) with \(V(1)\ne0\). For any
compatible quotient measure it gives a function \(U\) of the compact-finite model
for `d` and \(\psi_a\) whose ordinary integral against \(V\) is nonzero somewhere
in every right half-plane.

Suppose instead that every such \(U\) has ordinary integral vanishing on some
right half-plane. Fix \(\gamma\in\mathrm{GL}_{r+1}(\mathbb C)\).
`complexUnequalTranslatedNormalization`, with the entire normalizations supplied
by `complexUnequalNormalizedGrowth`, gives compact-finite tests whose entire
normalizations converge locally uniformly to an entire function equal, on a right
half-plane, to the reciprocal pair L-factor denominator times the ordinary
integral of \(\rho(\gamma)Bv\) against \(V\). Each approximating normalization
vanishes on a right half-plane, hence identically, so the limit is zero. The
denominator is nonzero far to the right (`complexLFactor_ne_zero`), so the
integral of every right translate vanishes on a right half-plane.
`ComplexUnequalOrdinaryDescent.eq_zero_of_translates_vanish`, applied to the model
functions \(Bv\) and \(V\), gives \(Bv(1)V(1)=0\), a contradiction.

## Assembly

`archimedeanActualWhittakerIntertwiners` gives, at the complex place, an
intertwiner \(B\) for the parameter of \(T\) and a vector \(v\) with
\(Bv(1)=1\). `ArchimedeanWhittakerEvaluation.exists_complexPlaceWhittaker_one_ne_zero`
gives an actual restriction \(V\) of \(T'\) for \(\psi^{-1}\) with \(V(1)\ne0\),
and the place-model comparison `complexPlaceWhittakerModelReduction` puts it in
the compact-finite model for the inverse character. With the compatible quotient
measure `complexQuotientMeasureData t`, the local theorem gives \(U\), and
`complexPlaceWhittakerRange` realizes \(U\) as an actual restriction of \(T\)
with finite coordinate one. The pair \((U,V)\) and the measure are fixed as the
half-plane varies, as the statement requires.

## Source

H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009), registered source
`jacquet-2009-archimedean-rankin-selberg`, SHA-256
`7a11766eadf25fb7452ce7faa193469791796f572fc654c8fe90a8608bb46afe`, defines the
integral in (2.4), author p. 6. Theorem 2.3(i), author p. 8, asserts continuity of
the integrals as maps into the space of meromorphic functions, and Theorem 2.6(i),
author p. 9, asserts generation for the smooth completed tensor product with
ordered inducing parameters. The nonvanishing for an individual pair of
compact-finite coefficients used here is the conclusion of the implemented
argument: the compact-finite approximation of right translates combined with the
last-row modulation of §6.2, Propositions 6.1–6.2, author pp. 41–42, carried out
by Fourier inversion of the last-row density.
