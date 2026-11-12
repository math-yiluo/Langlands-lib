# Existence of the almost-everywhere integral Iwasawa family

Worker 4256.

`Langlands.Global.IntegralIwasawaFamily.existenceStatement` proves exactly the
published proposition
`Langlands.Global.IntegralIwasawaFamily.ExistenceStatement.{u}` at every
universe `u`. The original statement and its imports are unchanged.

The implemented proof applies the published
`IntegralIwasawaFamily.existenceStatement_of_maximalCompact` to the published
unconditional theorem `IntegralModel.maximalCompactStatement`. Both inputs
are imported by Lean module name. No structural premise remains.

The reduction constructs simultaneous good reductive and parabolic models
over a ring of integers with finitely many primes inverted. It constructs
the proper relative parabolic quotient using the published dynamic and
ambient quotient proofs. The quotient and integral torsor lifting argument
give the parabolic-left covering on the actual completion points.
At each good place the canonical completion model has connected reductive
generic and special fibres. `IntegralModel.maximalCompactStatement` applies
to precisely this supplied model and proves maximality among all compact
overgroups of its integral-point image in the existing rational-point
topology. The reduction transports this result to the existing
coefficient-point carrier and evaluation topology.

The resulting witness is the single fixed family
`FiniteTypeIntegralFamily.subgroup F G`. The imported reduction already
establishes all three original conclusions for this same family: cofinite
compactness, maximality and literal parabolic-left covering; cofinite
membership of the actual projection of every finite adelic point; and
cofinite integrality of each regular function, uniformly over every member
of the local subgroup. The family is chosen before those adelic points and
regular functions. Their exceptional sets retain exactly the dependencies
allowed by the statement.

All original fields, groups and actual parabolic morphisms are retained,
including non-split and anisotropic groups and the improper parabolic.
The completion is `FiniteCompletion F v`, and the integral subring is the
original `v.adicCompletionIntegers F`. The theorem adds no model,
representation, covering, building or maximality hypothesis.

The provenance is internal composition of the two named published proofs.
This module introduces no additional external mathematical assertion; the
source correspondence and detailed constructions are explained in the
companions to `IntegralIwasawaFamilyReduction` and `IntegralModel.MaximalCompact`.
The full adelic `AdelicGroupPoints.ParabolicIwasawaStatement` is a separate
consumer target.
