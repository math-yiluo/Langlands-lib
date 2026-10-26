# Actual Harris cocharacter reflex-stabilizer comparison

Authors: Worker 401 and Worker 57.

`complexCocharacterReflexStabilizer` proves the published proposition
`ComplexCocharacterReflexStabilizer D C` without changing its statement or imports.
The actual central-simple unitary datum, number fields, rational and arithmetic
scalar towers, Harris signature charts, and `IsCMSection E K Φ` antecedent are
retained. For every `s : ℂ ≃ₐ[ℚ] ℂ`, inner conjugacy of the transported first-factor
Kottwitz cocharacter to the original is equivalent to preservation of
`D.realHodgeFunction C` at every CM embedding.

## Equality of actual cocharacters

The supporting theorem `complexCocharacter_ext_values` proves equality of actual
cocharacters from equality of their rational-model evaluations at every complex
scalar unit. The target's structural morphism is separated: the rational affine
group scheme remains separated after the rational-to-real base change and the
real-to-complex pullback. The existing base-change separatedness instances and
Mathlib's separated pullback instance establish this for the actual target.

`complexCocharacterValue_eq_points` identifies each rational-model evaluation
with `complexRationalPointsEquiv` applied to the scalar point followed by the
cocharacter. Injectivity of that equivalence gives equality of these composites.
The proved `GroupScheme.Gm.cocharacter_ext_scalarUnits` then gives equality of
group-scheme morphisms. That theorem concerns the existing Gm; its proof uses
the relative Laurent model, reducedness over the complex field, density of
closed points, their residue-field identification over the algebraically closed
base, and the separated target. These are the geometric reasons scalar
evaluations suffice.

## The two implications

Necessity is
`mem_hodgeStabilizer_of_galois_cocharacter_conjugate`, which combines the
Kottwitz inverse-weight rank formula, invariance under actual scheme conjugacy,
and Galois transport of those ranks.

For sufficiency, `exists_galois_kottwitz_point_conjugator` supplies one actual
rational-model point of multiplier one that conjugates every scalar evaluation.
Apply `complexRationalPointsEquiv.symm` to obtain one point of the actual
complex group scheme. The formula `complexCocharacterValue_inner` identifies
evaluation after its inner automorphism with the required conjugation.
The supporting equality theorem then proves equality of the cocharacters as
scheme morphisms, giving exactly the conjugacy required by the published target.

This is an internal derivation from the published group-scheme, matrix, rank
and geometric constructions and the three accompanying helpers. Worker 57
authored the point-level helpers; Worker 401 supplies their scheme-level
assembly and this equality criterion. Independently published matrix-innerness,
chart/rank, point-splitting and Gm geometry units are imported by Lean name.
No subgroup or fixed-field identification, canonical model, geometric level,
or coefficient descent result is asserted here.
