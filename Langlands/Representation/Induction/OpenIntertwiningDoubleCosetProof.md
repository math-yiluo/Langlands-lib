# Double-coset parametrization of compact-induction intertwining kernels: proof

Author: Worker 70.

`Langlands.Induction.compactInductionDoubleCoset` proves the published
`Langlands.Induction.CompactInductionDoubleCosetStatement.{uR,uG,uV,uW}` from
`Langlands.Representation.Induction.OpenIntertwiningStatement`. Its type is exactly
that proposition, at arbitrary universes `uR uG uV uW`, with no additional
parameters, typeclasses or hypotheses. Neither the statement pair nor any pair it
imports is changed. The module imports only the statement module and
`Mathlib.Tactic.Group`.

## What is proved

Let `R` be a commutative ring, `G` a topological group, `H` a subgroup that is open
and compact, `σ` a smooth representation of `H` on `V`, `τ` any representation of
`H` on `W`, and `s : DoubleCoset.Quotient H H → G` with
`DoubleCoset.mk H H (s q) = q` for every `q`.

1. If `Φ : G → (V →ₗ[R] W)` is an intertwining kernel
   (`IsIntertwiningKernel H σ τ Φ`), then `q ↦ Φ (s q)` is a local intertwiner
   family (`IsLocalIntertwinerFamily H σ τ s`).
2. Every local intertwiner family `φ` is `q ↦ Φ (s q)` for exactly one
   intertwining kernel `Φ`.

This is the double-coset form of Vignéras 1996, I.8.5 with `K = H`; the statement's
Markdown records the source comparison. The implemented proof below is elementary
and does not use the Mackey decomposition or Frobenius reciprocity.

## Auxiliary results in the module

The module states four lemmas in the namespace `Langlands.Induction` before the
main theorem.

- `finite_range_quotientMap_mul hHo hHc x`: for an open and compact subgroup `H`
  and any `x : G`, the set of right cosets `H (x b)` with `b ∈ H`, that is
  `Set.range fun b : H => quotientMap H (x * b)`, is finite. These are the right
  cosets contained in the double coset `H x H`. Proof: `H \ G` (`LeftQuotient H`)
  is discrete by the published
  `Langlands.Induction.discreteTopology_leftQuotient` (from
  `Langlands.Representation.Induction.OpenAdjunction`), `H` is a compact space by
  `isCompact_iff_compactSpace`, the map `b ↦ quotientMap H (x * b)` is continuous
  (`continuous_quotient_mk'` composed with left multiplication by `x` on the
  subtype), so its range is compact (`isCompact_range`), hence finite
  (`IsCompact.finite_of_discrete`).
- `finite_range_apply_of_isSmooth hHc hσ v`: for a compact subgroup `H` and a
  smooth representation `σ` of `H`, each orbit `Set.range fun b : H => σ b v` is
  finite. Proof: smoothness gives an open subgroup `K` of `H` with `v` in
  `fixedVectors σ K` (unfolded with `Representation.mem_invariants`). The map
  `b ↦ σ b v` is constant on left cosets `b K`
  (`σ (a (a⁻¹ b)) v = σ a (σ (a⁻¹ b) v) = σ a v`), so it factors through
  `H ⧸ K` by `Quotient.lift` (with `QuotientGroup.leftRel_apply`). The quotient
  `H ⧸ K` is finite by Mathlib's instance for open subgroups of a compact group
  (`Subgroup.quotient_finite_of_isOpen`), and the orbit is contained in the range
  of the factored map (`Set.finite_range`).
- `comp_eq_comp_of_covariant hcov x h hx`: if `Φ` has the covariance
  `Φ (h * g * h') = τ h ∘ₗ Φ g ∘ₗ σ h'`, then for every `x : G` and every
  `h ∈ H` with `x h x⁻¹ ∈ H`,
  `Φ x ∘ₗ σ h = τ ⟨x h x⁻¹, hx⟩ ∘ₗ Φ x`. Proof: the elements `1 · x · h` and
  `(x h x⁻¹) · x · 1` of `G` are equal, so covariance gives
  `τ 1 ∘ Φ x ∘ σ h = τ (x h x⁻¹) ∘ Φ x ∘ σ 1`; `τ 1` and `σ 1` are the identity
  (`map_one`).
- `comp_comp_eq_of_mul_eq hψ he`: if `ψ : V →ₗ[R] W` satisfies the local
  intertwining identity at `x` (for all `h ∈ H` with `x h x⁻¹ ∈ H`,
  `ψ ∘ₗ σ h = τ ⟨x h x⁻¹, _⟩ ∘ₗ ψ`), and `a₁ x b₁ = a₂ x b₂` in `G` with
  `a₁, b₁, a₂, b₂ ∈ H`, then `τ a₁ ∘ₗ ψ ∘ₗ σ b₁ = τ a₂ ∘ₗ ψ ∘ₗ σ b₂`.
  Proof: put `k = b₂ b₁⁻¹ ∈ H`. From the equation,
  `x k x⁻¹ = a₂⁻¹ (a₂ x b₂) b₁⁻¹ x⁻¹ = a₂⁻¹ (a₁ x b₁) b₁⁻¹ x⁻¹ = a₂⁻¹ a₁`
  (the `group` tactic), which lies in `H`. The local identity for `k` reads
  `ψ ∘ σ k = τ (a₂⁻¹ a₁) ∘ ψ`. Since `b₂ = k b₁`, evaluating at `v` gives
  `τ a₂ (ψ (σ b₂ v)) = τ a₂ (ψ (σ k (σ b₁ v))) = τ a₂ (τ (a₂⁻¹ a₁) (ψ (σ b₁ v)))
  = τ a₁ (ψ (σ b₁ v))` by `map_mul`.

## Proof of the main theorem

Introduce all data and hypotheses: `hHo : IsOpen H`, `hHc : IsCompact H`,
`hσ : IsSmooth σ` and `hs : ∀ q, DoubleCoset.mk H H (s q) = q`.

**Injectivity of `q ↦ H (s q)`.** If `quotientMap H (s q) = quotientMap H (s q')`,
then `s q' (s q)⁻¹ ∈ H` (the published `quotientMap_eq_iff`), so
`s q' = (s q' (s q)⁻¹) · s q · 1` and `DoubleCoset.eq` gives
`DoubleCoset.mk H H (s q) = DoubleCoset.mk H H (s q')`; by `hs`, `q = q'`.

**Part 1 (restriction).** Let `Φ` be an intertwining kernel with covariance `hcov`
and finiteness `hfin`. The local identity at each `s q` is
`comp_eq_comp_of_covariant hcov (s q)`. For a vector `v`, the image of
`{q | Φ (s q) v ≠ 0}` under `q ↦ quotientMap H (s q)` lies in
`quotientSupport H (fun g => Φ g v)`, which is finite by `hfin v`; the map is
injective, so the set is finite (`Set.Finite.of_finite_image`).

**Part 2 (extension).** Let `φ` be a local intertwiner family with local identities
`hloc` and finiteness `hfinφ`.

- *Decomposition.* For every `g`, `hs (DoubleCoset.mk H H g)` and `DoubleCoset.eq`
  give `a, b ∈ H` with `g = a · s (DoubleCoset.mk H H g) · b`. `choose` fixes
  functions `a b : G → H` with this property (`hab`).
- *Definition.* `Φ g := τ (a g) ∘ₗ φ (DoubleCoset.mk H H g) ∘ₗ σ (b g)`.
- *Independence of the decomposition* (`hΦ`): if `g = a' · s q · b'` with
  `a', b' ∈ H`, then `Φ g = τ a' ∘ₗ φ q ∘ₗ σ b'`. Indeed
  `DoubleCoset.mk H H g = q` (by `DoubleCoset.mk_mul_mem`,
  `DoubleCoset.mk_mem_mul` and `hs`), so both `a g · s q · b g` and `a' · s q · b'`
  equal `g`, and `comp_comp_eq_of_mul_eq (hloc q)` applies.
- *Values at the representatives.* `s q = 1 · s q · 1`, so by `hΦ`,
  `Φ (s q) = τ 1 ∘ φ q ∘ σ 1 = φ q`.
- *Covariance.* For `h, h' ∈ H` and `g`, `h g h' = (h · a g) · s q · (b g · h')`
  with `q = DoubleCoset.mk H H g`, so by `hΦ`,
  `Φ (h g h') = τ (h · a g) ∘ φ q ∘ σ (b g · h') = τ h ∘ Φ g ∘ σ h'`
  (`map_mul`).
- *Finiteness.* Fix `v`. The orbit `σ(H) v` is finite
  (`finite_range_apply_of_isSmooth hHc hσ v`), so the set `S` of `q` with
  `φ q w ≠ 0` for some `w` in the orbit is a finite union of finite sets
  (`hfinφ`, `Set.Finite.biUnion`). The union over `q ∈ S` of the finite sets
  `Set.range fun b : H => quotientMap H (s q * b)`
  (`finite_range_quotientMap_mul hHo hHc (s q)`) is finite and contains
  `quotientSupport H (fun g => Φ g v)`: if `Φ g v ≠ 0`, then
  `τ (a g) (φ q (σ (b g) v)) ≠ 0` with `q = DoubleCoset.mk H H g`, so
  `φ q (σ (b g) v) ≠ 0` and `q ∈ S`; and `H g = H (s q · b g)` because
  `g (s q · b g)⁻¹ = a g ∈ H` (`quotientMap_eq_iff`).
- *Uniqueness.* If `Ψ` is an intertwining kernel with `Ψ (s q) = φ q` for every
  `q`, then for every `g`, covariance of `Ψ` at `a g`, `b g` and
  `s (DoubleCoset.mk H H g)`, rewritten with `hab g` and the values of `Ψ` at the
  representatives, gives `Ψ g = τ (a g) ∘ φ (DoubleCoset.mk H H g) ∘ σ (b g) = Φ g`.
  Uniqueness uses only covariance.

## Library and Mathlib results used

- From `Langlands.Representation.Induction.OpenAdjunction` (imported through the
  statement module): `Langlands.Induction.discreteTopology_leftQuotient` and
  `Langlands.Induction.quotientMap_eq_iff`.
- From `Langlands.Representation.Induction.Definitions`: `quotientMap`,
  `quotientSupport` (definitions only).
- From `Langlands.Representation.Smooth.Definitions`: `IsSmooth`,
  `fixedVectors` (definitions only).
- Mathlib: `DoubleCoset.eq`, `DoubleCoset.mk_mul_mem`, `DoubleCoset.mk_mem_mul`,
  `isCompact_iff_compactSpace`, `isCompact_range`, `IsCompact.finite_of_discrete`,
  `continuous_quotient_mk'`, `Representation.mem_invariants`,
  `QuotientGroup.leftRel_apply`, the instance `Finite (H ⧸ K)` for an open
  subgroup `K` of a compact group, `Set.finite_range`, `Set.Finite.biUnion`,
  `Set.Finite.of_finite_image`, `Set.mem_biUnion`, `map_one`, `map_mul`,
  `map_zero`, `Module.End.mul_apply` and the `group` tactic.

No axioms beyond Lean's standard `propext`, `Classical.choice` and `Quot.sound`
are used; there is no `sorry`.
