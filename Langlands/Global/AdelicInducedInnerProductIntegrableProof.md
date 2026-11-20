# Proof of `InducedInnerProductIntegrableStatement`

Module `Langlands.Global.AdelicInducedInnerProductIntegrableProof`.

`Langlands.Global.inducedInnerProductIntegrable : InducedInnerProductIntegrableStatement`.

For the data of one member of `WavePacketIsometryStatement`, and `φ, ψ` with
`IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l`, the integrand of
`inducedInnerProduct K hK.isCompact p l μM e β φ ψ` is integrable on
`K × RationalQuotient F M` for `(compactHaarProbability F G K hK.isCompact).prod
(discreteQuotientMeasure (rationalSubgroup F M) _ μM)`.

## Proof

The proof introduces the binders of the statement and recovers the instance
`LocallyOfFiniteType P.X.hom` from the closed immersion `p`, as the statement does. It then
applies `InducedInnerProductIntegrable.integrable_inducedInnerProduct_integrand` from
`Langlands.Global.AdelicInducedInnerProductIntegrable`. The Levi `M` is connected reductive by
`r.isCompatible.levi.isConnectedReductive`, and `a` is a split component by
`r.isCompatible.splitComponent`. The remaining arguments are the split torus `A`, the
retraction `l ≫ π = 𝟙 M`, the Haar measure `μM`, continuity and compact support of `β`, and the
two square-integrability hypotheses. The hypotheses of the statement on `G`, `iU`, `K`
(maximality and Iwasawa factorization beyond compactness), `rho`, the compatibility of `μM`
and the torus `r.data.T` are not used.
