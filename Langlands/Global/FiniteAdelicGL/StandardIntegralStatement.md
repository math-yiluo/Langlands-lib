# The standard integral finite adelic matrix subgroup

This module is derived internal infrastructure. It specializes Mathlib's
restricted-product construction and the published
`Langlands.GeneralLinearGroup.integralOpenSubgroup` to the actual number-field
finite adele ring used by `Langlands.Global.FiniteAdelicGL`. No external theorem
is quoted here.

The field `K : Type u` has `Field` and `NumberField` instances. Finite places are
`IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)`. At a place
`v`, the local integer ring is `v.adicCompletionIntegers K`, the valuation
subring of the actual adic completion. The imported
[`Langlands.Global.IntegralFiniteAdeles`](../IntegralFiniteAdeles.md) module
houses `integralAdeles K`, `mem_integralAdeles`, and `isOpen_integralAdeles`
in their existing `Langlands.Global.FiniteAdelicGL` namespace.
The subring consists of finite adeles whose value belongs to the local integer
ring at every place; its ring operations are inherited from finite adeles.
The membership theorem gives this exact formula. The openness theorem uses
`RestrictedProduct.isOpen_forall_mem` and `Valued.isOpen_valuationSubring`, in
the actual restricted-product topology.

For every natural number `n`, `integralMatrices K n` is
`((integralAdeles K).matrix (n := Fin n)).toSubmonoid`.
`mem_integralMatrices` expresses entrywise membership in `integralAdeles K`;
`mem_integralMatrices_iff` expands it to all matrix coordinates and finite
places. `integralMatrices_eq_pi` identifies its carrier with two nested finite
`Set.pi Set.univ` products of the integral-adele carrier.
`mem_integralMatrices_pi` gives the corresponding membership equivalence.
These product descriptions are intended for the subsequent compactness proof.

`standardIntegral K n` uses the published `integralOpenSubgroup` constructor
with `isOpen_integralAdeles`. Its underlying subgroup is definitionally
`(integralMatrices K n).units`, as recorded by
`standardIntegral_toSubgroup`. The constructor proves openness using
`IsOpen.matrix` and `Submonoid.isOpen_units`; the topology remains the actual
matrix-units topology. `mem_standardIntegral_iff` requires membership of both
the value matrix and its inverse in `integralMatrices`. `mem_standardIntegral`
expands both requirements to all entries at all finite places. In particular,
the definition imposes integrality on the inverse as well as the forward matrix.

`standardIntegral_zero` proves equality to the top open subgroup at rank zero:
both coordinate conditions are vacuous because `Fin 0` is empty. No positive
rank or local compactness assumption occurs.

`StandardIntegralCompactStatement : Prop` universally quantifies over
`K : Type u`, its `Field` and `NumberField` instances, and `n : Nat`, and states
that the carrier of `standardIntegral K n` is compact in
`Langlands.Global.FiniteAdelicGL K n`. This module defines that proposition
without proving it. The matrix-subgroup compactness proof is separate from this statement.
Compactness of the integral finite adeles is supplied by the imported
`Langlands.Global.IntegralFiniteAdeles` module.
