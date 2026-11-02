# Haar measures on actual rational adelic quotients

Let `F` be any number field and `G` an affine group scheme over `Spec F`
whose structure morphism is locally of finite type. This internal specialization
uses the existing full adelic point group, its norm-one subgroup defined by
all actual rational algebraic character norms, and their actual left rational
homogeneous quotients. It imposes no splitting, connectedness, smoothness,
reductivity or rational-subgroup normality hypothesis.

The measurable structure on the full point group is the Borel sigma algebra of
its existing regular-function evaluation topology. The norm-one group inherits
the subgroup measurable structure. Each homogeneous quotient retains the
quotient sigma algebra; the proved discreteness of its principal subgroup,
Polishness of its ambient group and the generic quotient theorem show that
this sigma algebra is precisely Borel for its existing quotient topology.

`rationalQuotientHaarMeasure` and `normOneRationalQuotientHaarMeasure` apply
`LeftCosetSpace.haarQuotientMeasure` to these actual groups and principal
subgroups. They are the pushforwards of the respective ambient `Measure.haar`
restricted to the chosen Borel fundamental domain. The norm-one ambient Haar
measure is Haar measure on that subgroup, not a restriction of full ambient
Haar measure. Both quotient measures are nonzero, locally finite and regular.
For any other fundamental domain for the respective ambient Haar measure, the
two `_eq` theorems identify the quotient measure with its restricted
pushforward. There is no additional measure choice or rescaling.

The two real averaging formulas use subgroup counting measure, assigning mass
one to each principal subgroup point. They specialize the existing real
Weil formula for compactly supported continuous functions.

The right-translation results explicitly assume that the respective actual
ambient `Measure.haar` is right invariant. They preserve the positive convention
`[x] ↦ [x * g]`. Under precisely this additional assumption, each
`_isCompatible` theorem identifies the same explicit measure with the existing
`QuotientIntegration.IsCompatible` API: nonvanishing, regularity,
positive right invariance, integrability of the complex orbital average, and
the complex Weil integral formula for continuous compactly supported complex
functions. `compatibleNormOneRationalQuotientHaarMeasure` bundles the exact
norm-one quotient measure with this proved property; its value theorem is
definitional equality.

Provenance is internal. The point-group topology, rational discreteness and
norm-one inclusion are established by `AdelicGroupPolish` and its imported
actual scheme-point constructions. The Borel, Haar, fundamental-domain and
Weil arguments are direct specializations of `LeftCosetHaarMeasure` and
`LeftCosetWeilMeasure`; their hypotheses are discharged by those actual
topological results. No new reduction-theory or analytic modulus theorem is
used in this specialization.

Right invariance of the ambient Haar measures remains an explicit obligation,
including for reductive groups. The algebraic determinant of the adjoint
action has not been identified here with the analytic Haar modulus.
Finite volume, probability normalization, reduction theory, the split-centre
quotient and transport of measure through its comparison with the norm-one
quotient remain separate obligations.
