# Global continuous spectrum action for rational spectral operators

This derived construction starts with a complete ultrametric normed field `K`,
an actual presented strict affinoid algebra `P`, and a topological group `G` in
an independent universe. Its input `RationalSpectralAction G P` consists of
actual bounded algebra automorphisms with continuity for the published
restricted rational spectral topology. No continuity of quotient norm orbits
is assumed.

The goal is the actual inverse-pullback action on `BanachSpectrum P`. For `g`
and a spectrum point `x`, its value at `a : P` is `x ((ρ g).inv a)`.

`RationalData.wholeSpectrumHomeomorph` uses the published bounded equivalence
`RationalIdentity.emptyEquiv`. Its forward map is the actual structural
spectrum map of the rational quotient with denominator one and no numerators.
This quotient has the whole spectrum as its locus. Every group element
therefore belongs to its locus stabilizer; `wholeStabilizerHom` is the
continuous inclusion of `G` into this stabilizer, with unchanged underlying
group elements.

The equation `wholeSpectrumHomeomorph_smul` identifies the original action
with the quotient action through this homeomorphism. The proof applies the
published section-action structural equation at the inverse group element
and evaluates it with the actual multiplicative seminorm. This preserves the
inverse-pullback convention.

`continuous_globalSpectrumAction` then composes the published local joint
continuity theorem with the continuous map sending `(g,x)` to the whole
stabilizer element and the inverse image of `x` under the structural
homeomorphism. Postcomposition by the homeomorphism is continuous, and the
proved conjugacy identifies this function with the original global action.
This proof does not infer quotient-norm continuity from spectral bounds.

`globalSpectrumAction` packages the original bounded inverse maps as a
Mathlib `Action TopCat G`. The existing algebraic left-action identities prove
its unit and multiplication laws. `globalSpectrum` equips it with the joint
continuity just established. `globalSpectrum_apply` records the exact
seminorm evaluation formula. The identity forgetful functor on `TopCat` is
selected locally through the published helper in `NormContinuousAction`;
that import adds no norm-orbit continuity assumption.

The empty quotient, nonreduced algebras, empty spectra and trivial scalar
valuations remain allowed. The construction uses no nonzero or nonempty
hypothesis.

The motivating original is Berkovich's unfinished 1995–1996 manuscript
*Etale equivariant sheaves on p-adic analytic spaces*, section 1.1, pp.1–2,
registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`.
It defines finite compact-domain function tests and continuous analytic group
actions. The current global topological action is derived internally from the
restricted rational spectral tests; it does not identify that topology with
the full analytic automorphism topology of the manuscript. Berkovich's
*Non-archimedean analytic spaces* (Trieste lectures, 2009), Definition 2.2.1
and Exercise 2.2.2(ii), p.9, provide the rational quotient and affinoid-domain
context. The empty rational quotient equivalence and this categorical
packaging are internal consequences of the published Library constructions.

This unit establishes the global topological action. Analytic gluing,
structure sheaves, arbitrary-radius domains, full analytic atlases,
etale/quasi-etale sites and the Harris tower specialization remain separate
construction obligations.
