# Two-axis extension over arbitrary valuation rings

`Langlands.AbelianScheme.valuationRingTwoAxisExtension` proves exactly the
published proposition
`Langlands.AbelianScheme.ValuationRingTwoAxisExtensionStatement.{u}`.
Its entire type is that proposition.

The universe `u` is arbitrary. The proposition retains every valuation
domain `R`, including fields and valuation domains of arbitrary rank,
the supplied fraction field `K` with its supplied `R`-algebra structure,
and every Library abelian scheme `A / Spec R`. Given an actual line
bundle `D` on the self-product of the actual base change to `K`, with
both unit-axis restrictions trivial, the conclusion supplies an actual
line bundle `E` on the total self-product and an actual module-sheaf
isomorphism from its restriction to `D.obj`. Restriction uses precisely
the canonical `pullback.map` called `q` in the target proposition.

The proof applies the published theorem
`valuationRingTwoAxisExtension_of_integralFibreProjectivity` from
`MumfordProductGenericExtension` to the published theorem
`Langlands.CommutativeAlgebra.integralFibreProjectivity` from
`IntegralFibreProjectivityProof`, both at universe `u`.
The latter proves `IntegralFibreProjectivityStatement.{u}`.
It supplies the projectivity input of the former, which then returns
the complete target proposition.

The conditional assembly obtains projectivity of the actual affine
section algebras meeting the closed fibre, normalizes generic frames,
lifts their transition units, and glues an actual total bundle.
Its restriction isomorphism uses the canonical self-product
base-change map, which agrees with the target's `q`. This construction
applies to every generic line bundle, so the target's two axis-triviality
premises need no further use.

The provenance of this final proof is an internal composition of the
two published results. The geometric construction is explained in
`MumfordProductGenericExtension.md` and `ProjectiveGenericExtension.md`.
The projectivity proof by Workers 281 and 928 is explained in
`IntegralFibreProjectivityProof.md`. This module imports those results
without changing the target or their hypotheses.
