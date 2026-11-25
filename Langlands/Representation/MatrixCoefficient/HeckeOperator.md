# Hecke operators on the twisted `ℓ²` space of a coset space

## Statements

`G` is a group with a topology, `K` an open subgroup, `J` a subgroup and `ψ : J →* ℂ` a
group homomorphism into the multiplicative monoid of `ℂ`. `lift`, `L2 J`, `translate`,
`translates` and `xi` are from `TwistedCosetSpace.lean`. `q.out` is the representative that
Mathlib chooses for `q ∈ K ⧸ heckeSub K g`.

### The Hecke average

* `heckeSub K g`: the subgroup of `k ∈ K` with `g⁻¹ * k * g ∈ K`, that is, `K ∩ g K g⁻¹`
  as a subgroup of `K`. `mem_heckeSub_iff` unfolds membership.
* `sum_mul_out_mul`: if `f : G → M` (with `M` an additive commutative monoid) is right
  `K`-invariant, `K ⧸ heckeSub K g` is finite and `k ∈ K`, then
  `∑_q f (x * k * q.out * g) = ∑_q f (x * q.out * g)`.
* `mul_mul_center_mul_mul`: for central `z`, `x * (k * z) * a * g = x * k * a * g * z`.
* `heckeFun K J ψ g F x = n⁻¹ * ∑_q lift F (x * q.out * g)` for `F : G ⧸ J → ℂ`, where
  `n` is the number of cosets `q ∈ K ⧸ heckeSub K g`.

From here on the following hypotheses are used where named:
`hKJ : K ⊆ J`; `hψK`: `ψ k = 1` for `k ∈ K`; `hZJ : Z(G) ≤ J`; and `hJKZ`: every
`j ∈ J` is `k * z` with `k ∈ K` and `z ∈ Z(G)`.

* `lift_mul_of_mem` (`hψK`): `lift F (y * k) = lift F y` for `k ∈ K`.
* `heckeFun_mul` (`hψK`, `hZJ`, `hJKZ`): `heckeFun g F (x * j) = heckeFun g F x * ψ j` for
  `j ∈ J`.
* `lift_heckeFun` (same hypotheses): `lift (α ↦ heckeFun g F α.out) = heckeFun g F`.
* `enorm_mean_sq_le`: for a nonempty finite index type,
  `‖n⁻¹ * ∑ i, a i‖ₑ ^ 2 ≤ n⁻¹ * ∑ i, ‖a i‖ₑ ^ 2`.

### The norm bound

Now `G` is a topological group, `‖ψ j‖ = 1` for all `j` (`hψ`), `J` is open (`hJ`), and `μ`
is a Haar measure on `G ⧸ Z(G)` that is also right invariant.

* `tsum_enorm_heckeFun_le`: if `μ (CentralCoset.centralImage J) ≠ ∞` and
  `K ⧸ heckeSub K g` is finite, then for all `F : L2 J`,
  `∑' α : G ⧸ J, ‖heckeFun g F α.out‖ₑ ^ 2 ≤ ‖F‖ₑ ^ 2`.

### The operator

The next declarations take the conclusion of `tsum_enorm_heckeFun_le` as a hypothesis `hb`
for the fixed `g`; no measure is needed for them.

* `memℓp_heckeFun`: `α ↦ heckeFun g F α.out` is in `ℓ²`.
* `heckeₗ g hb`: the linear map `F ↦ (α ↦ heckeFun g F α.out)` on `L2 J`.
* `hecke g hb : L2 J →L[ℂ] L2 J`: the same map as a bounded operator of norm at most `1`.
  `hecke_apply`: `hecke g hb F α = heckeFun g F α.out`.
* `lift_hecke` (`hψK`, `hZJ`, `hJKZ`): `lift (hecke g hb F) = heckeFun g F`.
* `hecke_mem_centralizer` (`hψ`, `hψK`, `hZJ`, `hJKZ`): `hecke g hb` lies in the commutant
  `StarSubalgebra.centralizer ℂ (translates hψ)` of the left translations.

## Provenance

These are internal helpers for the proof of the Remark of Renard IV.3.2
(`Langlands.Renard.CompactRepresentation.SingleCoefficientSquareIntegrabilityStatement`).
There `K` is a small compact open subgroup and `J = K · Z(G)`. For a `K`-fixed vector `v`
the coefficient `x ↦ ℓ(π(x) v)` lies in `L2 J` (through `lift`), and the Hecke operator
`hecke g` sends it to the coefficient of `e_K π(g) v`, where `e_K` is the average over `K`.
So the Hecke operators realize, inside the commutant of the left translations, the action
of the Hecke algebra on the `K`-fixed vectors. This is the standard Hecke algebra action;
the statements and proofs are internal.

## Lean proof

* `heckeSub`: closure under products and inverses from
  `g⁻¹ (a b) g = (g⁻¹ a g)(g⁻¹ b g)` and `g⁻¹ a⁻¹ g = (g⁻¹ a g)⁻¹`.
* `sum_mul_out_mul`: with `k' = ⟨k, hk⟩ : K`, `(k' • q).out = k' * q.out * l` for some
  `l ∈ heckeSub K g` (`MulAction.Quotient.mk_smul_out`, `QuotientGroup.mk_out_eq_mul`).
  Then `x * (k' • q).out * g = x * k * q.out * g * (g⁻¹ l g)` with `g⁻¹ l g ∈ K`, so the
  summands agree by right `K`-invariance. The sum is reindexed by the permutation
  `q ↦ k' • q` (`Equiv.sum_comp`).
* `heckeFun_mul`: write `j = k * z`. Move `z` to the right end
  (`mul_mul_center_mul_mul`) and pull out `ψ z` by `lift_mul`; remove `k` by
  `sum_mul_out_mul`, using `lift_mul_of_mem`. Finally `ψ (k z) = ψ z` by `hψK`.
* `lift_heckeFun`: `lift_restrict` applied to `heckeFun_mul`.
* `enorm_mean_sq_le`: the triangle inequality and the Cauchy–Schwarz inequality
  `(∑ |a i|)² ≤ n ∑ |a i|²` (Mathlib `sq_sum_le_card_mul_sum_sq`).
* `tsum_enorm_heckeFun_le`: let `Ψ x = ‖lift F x‖ₑ ^ 2`, which is right `J`-invariant, and
  `Φ x = ∑_q Ψ (x * q.out * g)`, which is right `J`-invariant by the same argument as for
  `heckeFun_mul`. By `CentralCoset.lintegral_out_eq_mul_tsum` (from
  `CentralCosetSum.lean`), `μ(image of J) * ∑' α, Φ α.out = ∫⁻ Φ (q.out) dμ`. The integral
  splits into the `n` integrals of `q' ↦ Ψ (q'.out * q.out * g)`, and each equals
  `∫⁻ Ψ (q'.out) dμ` by right invariance (`CentralCoset.lintegral_out_mul_eq`); measurability
  comes from `CentralCoset.measurable_out` and continuity of right multiplication. The same
  lemma turns this back into `μ(image of J) * n * ∑' α, Ψ α.out`. Dividing by the measure,
  which is nonzero (`CentralCoset.centralImage_measure_ne_zero`) and finite (hypothesis),
  gives `∑' α, Φ α.out = n * ∑' α, Ψ α.out`. With `enorm_mean_sq_le` termwise,
  `∑' α, ‖heckeFun g F α.out‖ₑ ^ 2 ≤ n⁻¹ * n * ∑' α, Ψ α.out = ‖F‖ₑ ^ 2`
  (`lift_out`, `Langlands.Analysis.lp_two_enorm_sq_eq_tsum`).
* `memℓp_heckeFun`: `Langlands.Analysis.memℓp_two_of_tsum_enorm_ne_top` with `hb`.
* `heckeₗ`: additivity and homogeneity from `lift_add`, `lift_smul` and linearity of the
  finite sum.
* `hecke`: `LinearMap.mkContinuous` with bound `1`; `‖hecke F‖ ≤ ‖F‖` follows from the
  squared extended norm inequality `hb`.
* `lift_hecke`: `lift_heckeFun`.
* `hecke_mem_centralizer`: by `mem_centralizer_translates_iff` it suffices that
  `translate h (hecke F) = hecke (translate h F)`. At a class `α` both sides are
  `n⁻¹ * ∑_q lift F (h⁻¹ * α.out * q.out * g)`, by `lift_hecke` and `lift_translateₗ`.
