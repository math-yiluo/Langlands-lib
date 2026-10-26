# Proof of mixed principal-idele approximation

Authors: Worker 555 and Worker 226. Worker 555 supplies the exact-target
bridge; Worker 226 authored the published theorem reused by the proof.

`Langlands.Global.AdelicFunctoriality.mixedPrincipalIdeleApproximation.{u}`
proves exactly
`Langlands.Global.AdelicFunctoriality.MixedPrincipalIdeleApproximation.{u}`
from [MixedWeakApproximationStatement](MixedWeakApproximationStatement.md).
The universe `u` is arbitrary.

For any number field `K : Type u`, finite set `S` of finite places, and
idele `a`, the statement takes neighborhoods `U p` of `1` in the units
of the actual finite completions for `p ∈ S`, and neighborhoods `V w`
of `1` in the units of the actual infinite completions at every infinite
place. It produces one `α : Kˣ` whose inverse principal idele times `a`
has all those coordinates in their respective neighborhoods. The family
`U` is defined at all finite places, with hypotheses and conclusions only
at places in `S`; `S` may be empty.

The implemented proof introduces the field, its instances, and all the
data and hypotheses of the proposition, then applies
`exists_principal_inv_mul_mem S a U hU V hV` from
[MixedWeakApproximation](MixedWeakApproximation.md). Its conclusion is
the required existential statement with the same actual idele coordinate
maps and canonical completion topologies. This application preserves all
quantifiers and adds no assumptions.

This is a derived interface proof: the arithmetic and topological argument
is entirely Worker 226's published theorem. That module proves weak
approximation for the mixed family of finite and infinite absolute values,
transfers it to the actual completions, and converts it to the required
unit neighborhoods. The present module only connects that result to the
named proposition. It makes no local norm or global norm assertion.
