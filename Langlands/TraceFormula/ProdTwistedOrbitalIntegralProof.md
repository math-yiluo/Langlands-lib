# Twisted orbital integrals on a product of two groups

`Langlands.TraceFormula.prodTwistedOrbitalIntegral` proves
`ProdTwistedOrbitalIntegralStatement.{u}` from
`Langlands.TraceFormula.ProductTwistedOrbitalStatement` for Hausdorff, locally
compact, second-countable groups with their Borel σ-algebras. The product
twist acts componentwise by the continuous endomorphisms `θ₁` and `θ₂`. The
ambient measures are the left Haar measures `μ₁` and `μ₂` on the factors and
`μ₁.prod μ₂` on the product. The centralizer measures `μC₁`, `μC₂`, and `μC`
are right invariant, finite on compact sets, and positive on nonempty open
sets. The measure on each Borel left quotient is compatible with its ambient
and centralizer measures in the sense of `QuotientIntegration.IsCompatible`
from `Langlands.Analysis.Local.QuotientMeasure`.

The normalization hypothesis is the equality
`μC.map Subtype.val = (μC₁.map Subtype.val).prod (μC₂.map Subtype.val)` of measures
on the ambient product group. For continuous complex test functions with
integrable factor orbit functions, the theorem gives integrability of the
product orbit function and identifies its integral with the product of the
factor integrals.

The centralizers are closed by `isClosed_twistedCentralizer` from
`Langlands.BaseChange.RegularTransferMeasures`. The factor centralizers
inherit local compactness and second countability from their ambient groups.
For the factor quotients, `leftQuotient_locallyCompactSpace` from
`Langlands.Group.LeftQuotient` gives local compactness, and
`leftQuotient_isOpenQuotientMap` in the same module gives second countability
via Mathlib's `IsOpenQuotientMap.secondCountableTopology`. Finiteness on
compact sets for the factor centralizer measures and `IsCompatible.regular`
for the factor quotient measures supply the sigma finiteness used for
product measures.

At the identity isomorphism of `G₁ × G₂`, the maps in
`twistedCentralizerProductMeasure` from `Langlands.TraceFormula.TwistedOrbitalProduct`
send a pair of centralizer elements to that pair in the product centralizer.
They use `twistedCentralizerProductEquiv` from the same module and
`productSubgroupMeasure` from `Langlands.Analysis.Local.ProductQuotientMeasures`,
which transports the factor measures along the inverse of
`prodSubgroupHomeomorph` from `Langlands.Analysis.Local.LeftQuotientProduct`.
Mathlib's `Measure.map_map` and `Measure.map_prod_map` give the
product of the factor pushforwards as the pushforward of the constructed measure
to the ambient product. The normalization hypothesis makes this equal to the
pushforward of `μC`. The product centralizer is closed, so its inclusion is a
measurable embedding and Mathlib's `MeasurableEmbedding.map_injective` gives
equality with `μC` on the centralizer itself.

The proof then applies `twistedOrbitProductMeasure_isCompatible` from
`Langlands.TraceFormula.TwistedOrbitalProduct` with the same identity
isomorphism. Mathlib's `Measure.map_id` recovers the ambient measure
`μ₁.prod μ₂`. Both quotient measures are now compatible for the same ambient
and centralizer measures, so `IsCompatible.unique` from
`Langlands.Analysis.Local.QuotientCompatibleScaling` identifies them.

The orbit function, pulled back by `twistedOrbitProductHomeomorph`, is the
product of the factor orbit functions. The proof checks this on representatives
using `twistedOrbitProductHomeomorph_mk` from
`Langlands.TraceFormula.TwistedOrbitalProduct` and `twistedOrbitFunction_mk`
from `Langlands.TraceFormula.TwistedOrbital` with the componentwise twist.
Mathlib's `Integrable.mul_prod` gives integrability on the product of the
factor quotients, and `integrable_map_equiv` transports it. The integral
identity is `twistedOrbitalIntegral_product` from
`Langlands.TraceFormula.TwistedOrbitalProduct`.

The factorization is the two-factor form of the finite splitting in Getz–Hahn,
*An Introduction to Automorphic Representations* (2024), Lemma 17.8.3 and
(17.55), printed pp. 463–464. The integrand and left-quotient convention come
from (18.32), printed p. 487. The retained source
`getz-hahn-2024-automorphic-representations` has SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
[Getz–Hahn (2024)](https://doi.org/10.1007/978-3-031-41153-3)
