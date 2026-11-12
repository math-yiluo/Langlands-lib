# Similitudes split by a central idempotent exchanged by the involution

Author: Worker 19.

This internal algebraic construction computes the similitude group of an
involution when the algebra has a central idempotent that the involution
exchanges with its complement. It is the algebraic core of the identification
of Harris's similitude group at a prime split in the imaginary quadratic
field (`ImaginaryQuadraticSplitPoints` and `HarrisSplitPrimePoints`, submitted
together with this module).

## Setting

All declarations are in namespace `Langlands.Shimura.AlgebraInvolution`. Let
`S` be a commutative ring, `B` an `S`-algebra and `τ : AlgebraInvolution S B`
an involution. The published `Langlands.Shimura.Unitary.Similitude` defines
the similitude group `τ.similitudes`: the pairs `(g, c)` of a unit `g` of `B`
and a unit `c` of `S` with `g * τ g = c` (`mem_similitudes_iff`), with
multiplier `τ.multiplier (g, c) = c`.

## The splitting data

`CentralExchangeSplitting τ Q`, for a ring `Q`, consists of

- an element `e = idempotent` of `B` with `e * e = e`, central
  (`e * x = x * e` for all `x`), and with `τ e = 1 - e`;
- a ring homomorphism `π = projection : B →+* Q`;
- a map `ψ = lift : Q → B` with `ψ (x * y) = ψ x * ψ y`, `π (ψ x) = x` and
  `ψ (π x) = e * x`.

So `ψ` identifies `Q` with the corner `e B` (as a multiplicative monoid with
identity `e`), and `π` is multiplication by `e` followed by this
identification. The data do not require `ψ` to be additive.

## Elementary consequences

For `P : CentralExchangeSplitting τ Q`:

- `lift_one`: `ψ 1 = e`; `projection_idempotent`: `π e = 1`;
  `projection_one_sub_idempotent`: `π (1 - e) = 0`.
- `idempotent_mul_lift`, `lift_mul_idempotent`: `e * ψ x = ψ x = ψ x * e`;
  `idempotent_mul_one_sub`: `e * (1 - e) = 0`.
- `involution_lift_mul_one_sub`, `one_sub_mul_involution_lift`: since
  `τ e = 1 - e`, the element `τ (ψ x)` lies in `(1 - e) B` on both sides.
- `lift_mul_involution_lift`, `involution_lift_mul_lift`:
  `ψ x * τ (ψ y) = 0` and `τ (ψ y) * ψ x = 0`.
- `involution_lift_mul_involution_lift`: `τ (ψ x) * τ (ψ y) = τ (ψ (y * x))`.
- `lift_units_mul_inv`: `ψ a * ψ a⁻¹ = e`, and
  `involution_lift_units_inv_mul`: `τ (ψ a⁻¹) * τ (ψ a) = 1 - e`, for a unit
  `a` of `Q`.
- `projection_involution_lift`: `π (τ (ψ x)) = 0`.

## The similitude group

- `liftValue a c = ψ a + c • τ (ψ a⁻¹)` for a unit `a` of `Q` and a unit `c`
  of `S`. `liftValue_mul_liftValue_inv` shows that `liftValue a⁻¹ c⁻¹` is its
  inverse, and `liftUnit a c` is the resulting unit of `B`.
- `liftValue_mem`: `liftValue a c * τ (liftValue a c) = algebraMap S B c`, so
  `(liftUnit a c, c)` is a similitude with multiplier `c`.
- `projection_liftValue`: `π (liftValue a c) = a`.
- `liftValue_projection`: for a similitude `(g, c)`,
  `liftValue (π g) c = g`.
- `similitudesEquiv P : τ.similitudes ≃* Qˣ × Sˣ` sends `(g, c)` to
  `(π g, c)` (the unit of `Q` obtained by applying `π` to `g`, and the
  multiplier). Its inverse sends `(a, c)` to `(liftUnit a c, c)`.
- `similitudesEquiv_fst_val`, `similitudesEquiv_snd`,
  `similitudesEquiv_symm_val` and `similitudesEquiv_symm_multiplier` record
  these formulas; all hold by `rfl`.

## Proof outline

All products are expanded in `B`. The cross terms vanish because `e B` and
`(1 - e) B` multiply to zero. For `liftValue_mem`, the two remaining terms
are `c • (ψ a * ψ a⁻¹) = c • e` and `c • τ (ψ (a⁻¹ * a)) = c • τ e =
c • (1 - e)`, which add up to `c`. For `liftValue_projection`, write
`g * τ g = c`; then `c • τ (g⁻¹) = g`, so
`ψ (π g) + c • τ (ψ (π g⁻¹)) = e * g + c • τ (g⁻¹) * τ e = e * g + g * (1 - e) = g`,
using that `e` is central. The two composites of `similitudesEquiv` are the
identity by `liftValue_projection` and `projection_liftValue`, and
multiplicativity holds because `π` is a ring homomorphism.

## Provenance

This is an internal construction. The splitting of a similitude group by a
central idempotent exchanged by the involution is the standard computation
behind Harris (1998), Appendix, equation (A.1) on printed p. 206, and
Harris (1999), equation (4.2) on printed p. 309, at a prime split in the
imaginary quadratic field; neither source states it in this abstract form.
The packaging as `CentralExchangeSplitting`, with a multiplicative section
instead of a corner ring, is an implementation choice.

Formal dependencies: `Langlands.Shimura.Unitary.Similitude` and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435` under Lean 4.34.0.
