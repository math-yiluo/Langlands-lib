# Contracting elements for an idempotent torus

Module `Langlands.GroupScheme.FiniteAlgebraIdempotentDynamic`, namespace
`Langlands.GroupScheme.FiniteAlgebraUnits`.

## Setting

* `A` is a `K`-algebra with a basis `b : Module.Basis (Fin d) K A`.
* `FiniteAlgebraUnits.groupScheme b` is its unit group scheme.
* `p, q ∈ A` are orthogonal idempotents: `p² = p`, `q² = q`, `pq = qp = 0`.
* `μ = idempotentScalingHom p q hp hq hpq hqp b` is the Library's cocharacter
  `t ↦ 1 + (t - 1) p + (t⁻¹ - 1) q`.

## Definitions

* `IsContracting p q N₁ N₂` (a `Prop`) collects the relations
  - `N₁ p = 0`, `q N₁ = 0`, `p N₁ q = 0`, `p N₁ + N₁ q = N₁`;
  - `N₂ p = 0`, `q N₂ = 0`, `N₂ q = N₂`, `p N₂ = N₂`.

  Writing `r = 1 - p - q`, they say `N₁ = p N₁ r + r N₁ q` and `N₂ = p N₂ q`, so `N₁` has
  weight `1` and `N₂` has weight `2` for conjugation by `μ`.
* `contractingValue R N₁ N₂ s = 1 + s ⊗ N₁ + s² ⊗ N₂` and
  `contractingInvValue R N₁ N₂ s = 1 - s ⊗ N₁ + (s ⊗ N₁)² - s² ⊗ N₂` in `R ⊗[K] A`, for a
  commutative `K`-algebra `R` and `s ∈ R`.
* `contractingUnit h s`: these two elements packaged as a unit (`h : IsContracting p q N₁ N₂`).
* `contractingPoint h b T`: the point of `groupScheme b` over a test scheme `T` whose unit is
  `1 + N₁ + N₂`.
* `contractingCurve h b T`: the morphism `T × 𝔸¹ ⟶ groupScheme b` whose unit is
  `1 + s N₁ + s² N₂`, where `s` is the coordinate of `𝔸¹`.

## Results

* `IsContracting.one_mul_two`, `two_mul_one`, `two_mul_two`, `one_mul_one_mul_one`:
  `N₁N₂ = N₂N₁ = N₂² = N₁³ = 0`. Hence `contractingInvValue` inverts `contractingValue`.
* `contractingUnit_zero`: the unit is `1` at `s = 0`.
* `contractingUnit_map`: the unit is natural in `R`.
* **`idempotentScalingUnits_conj`**: `μ(t) (1 + N₁ + N₂) μ(t)⁻¹ = 1 + t N₁ + t² N₂` over every
  `R` and every unit `t`.
* `comp_contractingPoint`: the contracting points are compatible with pullback.
* **`contractingPoint_mem_unipotent`**: on every test scheme `T`, the point `1 + N₁ + N₂` lies
  in `Dynamic.unipotent μ`.
  *Proof.* `contractingCurve` is an orbit extension of it: on `T × 𝔾_m` it agrees with
  `t ↦ μ(t) g μ(t)⁻¹` by the conjugation formula. Its value at `s = 0` is `1`. The structure
  follows the Library's `FiniteAlgebraBinaryDynamic.elementary_range_le_dynamicUnipotent`.

## Provenance

Internal. This is the standard fact that elements of positive weight for a cocharacter
contract to the identity (the dynamic description of `U(λ)`, Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, §2.1), proved directly for unit groups of finite algebras and the
Library's idempotent tori. It is used in Task 5398 to show that Eichler transformations of a
hyperbolic pair are rational points of the unipotent subgroup of the hyperbolic torus.
