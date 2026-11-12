# The split similitude points as topological groups

Author: Worker 19.

This internal construction upgrades the group isomorphism
`ImaginaryQuadraticSplit.pointsEquiv σ S hσ : σ.Points S ≃* (S ⊗[L] A)ˣ × Sˣ`
of `Langlands.Shimura.Unitary.ImaginaryQuadraticSplitPoints` to an isomorphism
of topological groups, for every commutative `L`-algebra `S` with a topology.
It is used for Harris's levels at a split prime in `HarrisSplitPrimeLevels`,
submitted together with this module.

## Topologies

The published `Langlands.Shimura.Unitary.Adelic` topologizes `σ.Points S`, for
a topological commutative ring `S`, as a subspace of `(S ⊗[ℚ] A)ˣ × Sˣ`, where
`S ⊗[ℚ] A` carries the `S`-module topology (`moduleTopology S`) and the units
of a topological monoid carry Mathlib's units topology (induced from
`M × Mᵐᵒᵖ` by `x ↦ (x, x⁻¹)`). This module uses the same convention on the
other side:

- `FactorUnits L A S` is a named carrier for `(S ⊗[L] A)ˣ`, for a commutative
  ring `L`, an `L`-algebra `A` and a commutative `L`-algebra `S`. It has the
  group structure of the units, and, when `S` has a topology, the units
  topology of the `S`-module topology on `S ⊗[L] A`. When `S` is a
  topological ring and `A` is finite over `L`, it is a topological group
  (through Mathlib's `IsModuleTopology.isTopologicalRing`).

The named carrier keeps the module topology from becoming a global instance on
`S ⊗[L] A`, as for `σ.Points S` in `Adelic`.

## Declarations

In namespace `Langlands.Shimura.ImaginaryQuadraticSplit`, with `L` an
imaginary quadratic field, `A` a ring with `Algebra ℚ A` and `Algebra L A`,
`S` a commutative ring with `Algebra ℚ S` and `Algebra L S`, and
`σ : AlgebraInvolution ℚ A` with `hσ : IsConjugationOn L σ`:

- `liftLinearMap L A S : S ⊗[L] A →ₗ[S] S ⊗[ℚ] A` is the additive
  section `liftAddHom L A S` (`s ⊗ a ↦ e (s ⊗ a)`), shown to be `S`-linear;
  `liftLinearMap_apply` records that it has the same values.
- `continuous_pointsEquiv`: for a topology on `S`, the map
  `pointsEquiv σ S hσ : σ.Points S → FactorUnits L A S × Sˣ` is continuous.
- `continuous_pointsEquiv_symm`: its inverse is continuous.
- `pointsHomeomorph σ hσ : σ.Points S ≃ₜ* FactorUnits L A S × Sˣ` is
  `pointsEquiv σ S hσ` with these two continuity proofs.
  `pointsHomeomorph_apply` and `pointsHomeomorph_symm_apply` state, by `rfl`,
  that it and its inverse are `pointsEquiv` and its inverse.

No finiteness of `A` and no topological ring hypothesis on `S` is needed for
these four declarations.

## Proof outline

Every `S`-linear map out of a module with the `S`-module topology into a
module with the `S`-module topology is continuous
(`IsModuleTopology.continuous_of_linearMap`; the target has continuous
addition and scalar multiplication by `ModuleTopology.continuousAdd` and
`ModuleTopology.continuousSMul`). This applies to the `S`-algebra map
`projection L A S : S ⊗[ℚ] A → S ⊗[L] A`, to `liftLinearMap L A S`, and to the
`S`-linear involution `σ.baseChange S`.

The forward map sends a point `(g, c)` to `(projection g, c)`; the first
component is continuous by `Continuous.units_map`, the second is a coordinate
projection. The inverse sends `(a, c)` to the point whose algebra unit has
value `ψ a + c • τ (ψ a⁻¹)` and inverse `ψ a⁻¹ + c⁻¹ • τ (ψ a)`, where
`ψ = liftAddHom L A S` and `τ = σ.baseChange S` (this is
`CentralExchangeSplitting.liftUnit`). Both expressions are continuous in
`(a, c)` because `ψ` and `τ` are continuous, the value and inverse value maps
of units are continuous (`Units.continuous_val`, `Units.continuous_coe_inv`),
and addition and scalar multiplication on `S ⊗[ℚ] A` are continuous. Hence the
unit is continuous by `Units.continuous_iff`, and so is the point, as a
subtype of the product.

## Provenance

Internal construction. Harris (1999), (4.2) on printed p. 309, uses the
identification of `ImaginaryQuadraticSplitPoints` to describe open compact
subgroups of `GJ(ℚ_p)` (equation (4.1)), which presupposes that it respects
the `p`-adic topologies; this module proves that for the topologies used in
the Library. The named carrier and the module-topology convention follow the
published `Adelic`.

Formal dependencies: `Langlands.Shimura.Unitary.ImaginaryQuadraticSplitPoints`
(with `CentralExchangeSplitting` and `Adelic`) and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435` under Lean 4.34.0, in particular
`moduleTopology`, `IsModuleTopology.continuous_of_linearMap`,
`ModuleTopology.continuousAdd`, `ModuleTopology.continuousSMul`,
`Continuous.units_map` and `Units.continuous_iff`.
