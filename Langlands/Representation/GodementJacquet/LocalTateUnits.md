# Principal-unit levels and the rank-one conductor

This helper module is internal infrastructure for the proof of
`Langlands.GodementJacquet.LocalTateConductorStatement`. It identifies the
target's matrix-level conductor condition with the classical principal-unit
condition. It also proves two vanishing principles that later modules use
for character integrals.

## Vanishing from twisted invariance

`setIntegral_eq_zero_of_mul_left` covers a left-invariant measure on a group
together with an element `w`. Suppose left translation by `w` preserves a
measurable set `S` and multiplies `f` by a constant `c ≠ 1` on `S`. Invariance
of the integral gives `I = c I`, so `∫_S f = 0`.
`setIntegral_eq_zero_of_add_right` is the additive analogue for a
right-translation-invariant measure. Neither lemma needs an integrability
hypothesis: both sides are Bochner integrals of the same function, and
rewriting under translation invariance holds without one.

## Unit levels

- `mem_integralUnits_iff`: a unit lies in the Library's
  `integralUnits (valuation F).integer` exactly when its valuation is one.
- `unitLevel m` is the subgroup
  `{u ∈ Fˣ | v(u) = 1 and u - 1 ∈ ϖ^m O}`, which is `1 + ϖ^m O` for `m ≥ 1`
  (`mem_unitLevel_iff_of_pos`). `unitLevel 0` is the group of integral units
  (`unitLevel_zero`). Closure under products and inverses uses
  `uw - 1 = u(w - 1) + (u - 1)` and `u⁻¹ - 1 = -u⁻¹(u - 1)`.

## Matrix levels versus unit levels

The target states the conductor through `Conductor.levelSubgroup F 0 m`, the
image in `GL₁(F)` of the integral congruence subgroup modulo `m^m`.

- `mem_maximalIdeal_pow_iff`: an integer lies in `m^m` exactly when it lies in
  `ϖ^m O`. This uses the published
  `Conductor.maximalIdeal_pow_eq_span_jacquetUniformizer`.
- `determinant_mem_unitLevel` and `exists_determinant_eq`: the determinant
  maps `levelSubgroup F 0 m` onto `unitLevel m`. In rank one the determinant is
  the unique matrix entry (`det_glOne`), and `Conductor.mem_integralCongruence_rankOne`
  reads the congruence condition off that entry. A unit `u` of the level
  is the determinant of the scalar matrix of the integral unit `u`.
- `level_trivial_iff`: `χ ∘ det` is trivial on `levelSubgroup F 0 m` exactly
  when `χ` is trivial on `unitLevel m`.

`IsUnitConductor η a` says that `η` is trivial on `unitLevel a` and nontrivial
on `unitLevel b` for every `b < a`. `isUnitConductor_iff` rewrites both
clauses in the target's matrix-level form. `IsUnitConductor.inv` shows that
`η⁻¹` has the same conductor.

## Provenance

The principal-unit conductor is Tate's (source
`tate-1979-number-theoretic-background`, (3.2.6), as already cited in
`LocalTateConductorStatement.md`). These lemmas only translate between the
Library's matrix level subgroups and unit levels, and they are derived
internally.
