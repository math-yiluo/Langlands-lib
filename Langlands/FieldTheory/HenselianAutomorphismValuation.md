# Automorphism invariance of Henselian discrete valuations

This module contains two general facts about valuations. They are used to show
that the normalized valuation on a finite Galois extension of the maximal
unramified field is preserved by ring automorphisms that do not fix the base
(see `Langlands/Geometry/Building/Kottwitz/ValuationAutomorphismInvariance.md`).
All declarations are internal helper results. They formalize standard
arguments and do not correspond to a numbered result of a cited source.

## Ring automorphisms of a Henselian discretely valued field

Let `K` be a field.

- `HasUnboundedRoots x` (definition) means that `x ≠ 0` and that for every
  natural number `N` there are `n ≥ N` and `y : K` with `y ^ n = x`. It uses only
  the field structure of `K`.
- `hasUnboundedRoots_map`: for every ring automorphism `σ` of `K`,
  `HasUnboundedRoots (σ x) ↔ HasUnboundedRoots x`. The forward direction applies
  `σ.symm` to roots of `σ x`, and the reverse direction applies `σ` to roots of `x`.

Let `v : Valuation K ℤᵐ⁰` (written `WithZero (Multiplicative ℤ)` in Lean).

- `val_eq_one_of_hasUnboundedRoots`: if `HasUnboundedRoots x`, then `v x = 1`.
  Write `v x` as the integer `m` and suppose `m ≠ 0`. Take an `n`-th root `y` of `x`
  with `n ≥ |m| + 1`. Then `n` divides `m`, so `n ≤ |m|`, a contradiction.
- `hasUnboundedRoots_of_val_eq_one`: assume that the valuation ring
  `v.valuationSubring` is a Henselian local ring and that its residue field is
  algebraically closed. If `v x = 1`, then `HasUnboundedRoots x`. Given `N`, the
  proof picks `n ≥ N` with `n ≠ 0` in the residue field: `n = N + 1` in residue
  characteristic zero, and `n = N p + 1` in residue characteristic `p > 0`. The
  element `x` is a unit `u` of the valuation ring. Its residue has an `n`-th root
  `z ≠ 0` in the algebraically closed residue field. Let `a₀` be a lift of `z`.
  Then `X ^ n - C u` is monic and vanishes at `a₀` modulo the maximal ideal. Its
  derivative at `a₀` has residue `n z ^ (n - 1) ≠ 0`. Henselianity
  (`HenselianLocalRing.is_henselian`) gives an exact root `a` in the valuation ring,
  so `a ^ n = x`.
- `val_eq_one_iff_hasUnboundedRoots`: under the same two assumptions,
  `v x = 1 ↔ HasUnboundedRoots x`. So the units of the valuation ring are
  determined by the field structure alone.
- `val_le_one_iff_eq_one_or_add_eq_one`: for every valuation `w` with values in a
  linearly ordered commutative group with zero, `w x ≤ 1 ↔ w x = 1 ∨ w (1 + x) = 1`.
  If `w x < 1` then `w (1 + x) = 1`. Conversely, if `w x > 1` then
  `w (1 + x) = w x ≠ 1`.
- `isEquiv_comap_ringEquiv`: under the two assumptions on `v`, every ring
  automorphism `σ` of `K` satisfies `(v.comap σ).IsEquiv v`. By
  `Valuation.isEquiv_iff_val_le_one` it suffices to compare `v (σ x) ≤ 1` with
  `v x ≤ 1`. The previous lemma turns both conditions into statements about
  `v`-units. These become `HasUnboundedRoots` statements, using
  `1 + σ x = σ (1 + x)`, and `hasUnboundedRoots_map` shows they agree.

## Prolongations to a finite Galois extension

Let `Ω/K` be a finite Galois extension of fields.

- `realValuation_le_one_iff_norm`: let `w : Valuation Ω ℝ≥0` be invariant under
  every `σ : Gal(Ω/K)`. Then `w a ≤ 1` iff `w (algebraMap K Ω (Algebra.norm K a)) ≤ 1`.
  The norm is the product of the Galois conjugates of `a`
  (`Algebra.norm_eq_prod_automorphisms`), so its value is `w a ^ [Ω : K]`. For
  nonnegative reals, a nonzero power is at most one iff the base is.
- `realValuation_isEquiv_of_comap_isEquiv`: let `w₁ w₂ : Valuation Ω ℝ≥0`. Assume
  the restriction `w₁.comap (algebraMap K Ω)` is nontrivial, its valuation ring is
  a Henselian local ring, and it is equivalent to `w₂.comap (algebraMap K Ω)`.
  Then `w₁.IsEquiv w₂`. Equivalent valuations have the same valuation ring
  (`Valuation.isEquiv_iff_valuationSubring`), so the restriction of `w₂` is also
  nontrivial with a Henselian valuation ring. The published
  `realValuation_invariant_of_finiteGalois` therefore makes both `w₁` and `w₂`
  invariant under `Gal(Ω/K)`. By the previous lemma, `wᵢ a ≤ 1` is then
  equivalent to a condition on the norm of `a` for the restriction of `wᵢ`. The
  two restrictions are equivalent, so `w₁ a ≤ 1 ↔ w₂ a ≤ 1` for every `a`, which
  is `w₁.IsEquiv w₂`.
