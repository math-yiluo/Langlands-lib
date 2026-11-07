# Rapid decay of the vectors of a cuspidal operator realization along maximal blocks

Provenance: internal. This module discharges the explicit hypotheses of the abstract
block-decay theorem `blockDecay_of_cuspidal` (module
`Langlands.Automorphic.CuspidalL2.Decay`) for the vectors of an actual cuspidal
`OperatorRealization F n`, and concludes that each such vector decays rapidly along every
maximal block, in the form used to prove square integrability on Siegel-type sets. It is
the classical rapid decay of cusp forms (along one maximal block parabolic at a time),
obtained here only from the Library's definitions of automorphic forms, enveloping
actions and constant terms. All declarations live in the namespace
`Langlands.Automorphic.OperatorRealization`; `S : OperatorRealization F n` throughout, and
`ev` stands for `evaluate F n (S.toContinuous ·)`.

## Definitions

- `basisGenerator F n k`: the enveloping-algebra element
  `envelopingGenerator (complexify (lieDirection F n k))` attached to the `k`-th real basis
  direction `ArchimedeanGL.lieDirection F n k` of the archimedean Lie algebra (the basis of
  `Decay`). It is the element whose action is the derivative in that direction.
- `S.ambient f` (abbreviation): the finite-smooth ambient function `f.val.val` underlying a
  realized vector `f : S.Space`.

## Bookkeeping lemmas

- `evaluate_toContinuous`, `ambient_envelopingAction` (both `rfl`): evaluation of a
  realized vector is evaluation of its ambient function, and the enveloping action on
  `S.Space` is the finite-smooth enveloping action on ambient functions.
- `isAutomorphicForm_ambient`: the ambient function of every realized vector is an
  automorphic form (`operatorCore_le` and `mem_automorphicSubrepresentation`).
- `pair_eq_ofInfinite_mul_ofFinite`: `pair a b = ofInfinite a * ofFinite b`, checked on the
  infinite and finite projections.
- `finiteSmoothSlice_ambient_apply`: the archimedean slice of `S.ambient f` at the finite
  adelic point `y` is `g ↦ ev f (ofInfinite g * ofFinite y)`.
- `finiteSmoothSlice_eq_smoothInfiniteSlice` (`rfl`): this slice is the slice of the
  automorphic form used in the Library's growth and finiteness conditions.

## Hypotheses of the abstract theorem

The family is indexed by the enveloping algebra: `φ u = ev (S.envelopingAction u f)`,
with `der k u = basisGenerator F n k * u`.

- `exists_level f`: one open subgroup `L` of the finite adelic group fixes every
  enveloping derivative `S.envelopingAction u f` under right translation by `ofFinite l`.
  It is the level of the automorphic form `S.ambient f` (its finite-level condition),
  which is preserved by the enveloping action
  (`finiteSmoothEnvelopingAction_preserves_level`).
- `slice_data f u y`: the slice `g ↦ ev (S.envelopingAction u f) (ofInfinite g * ofFinite y)`
  is the value of a smooth function `s` (the Library slice `finiteSmoothSlice`), and the
  derivative of `s` in direction `lieDirection k` is the slice of
  `S.envelopingAction (basisGenerator F n k * u) f`. Proof: slices commute with the
  enveloping action (`finiteSmoothSlice_envelopingAction`), the generator of a real
  direction acts as the derivative in that direction (`envelopingAction_real_generator`),
  and the action is multiplicative (`map_mul`).
- `norm_le_of_cuspidal hS h ha hb f g M hM` (needs `CompactSpace (AdeleQuotient F)`): if
  `‖ev f (blockUnipotent h Y * g) - ev f g‖ ≤ M` for every adelic block matrix `Y`, then
  `‖ev f g‖ ≤ M`. Proof: for a cuspidal realization the constant term along the block
  vanishes (`S.constantTerm_eq_zero`), so `ev f g` equals the integral of
  `ev f g - constantTermIntegrand` over the probability space `matrixQuotientHaar F a b`;
  the integrand is `ev f g - ev f (blockUnipotent h (matrixLift X) * g)`, bounded by `M`, and
  `norm_integral_le_of_norm_le_const` gives the bound.
- Growth (`slice_properties`, `slice_derivative_growth`,
  `exists_uniform_slice_exponent`, `exists_finite_level_cover`, `exists_uniform_growth`):
  - `slice_properties f y`: each slice of `S.ambient f` is `K`-finite for the standard
    archimedean maximal compact subgroup, center-finite (both from
    `SliceFinitenessProof.sliceFiniteness` applied to the automorphic-form conditions) and
    has polynomial growth `‖s g‖ ≤ C * matrixHeight g ^ d` (the moderate-growth condition).
  - `slice_derivative_growth`: every enveloping derivative of such a slice keeps the same
    exponent `d` (the proved statement `ArchimedeanGL.finiteUniformDifferentialGrowth`).
  - `exists_uniform_slice_exponent f t`: for a finite set `t` of finite adelic points one
    exponent (the maximum) serves all slices at points of `t`.
  - `exists_finite_level_cover L hLo Q hQ`: for an open subgroup `L` and compact `Q`,
    finitely many cosets `y L` cover the finite parts of `Q` (compactness of the image of
    `Q` under the finite projection).
  - `exists_uniform_growth f L hLo hlevel Q hQ`: there are one exponent `d` and a set `F₀`
    of finite adelic points containing the finite parts of `Q` such that for every `u` and
    every compact `Q'` with finite parts in `F₀`,
    `‖ev (S.envelopingAction u f) (ofInfinite (torInf x) * q)‖ ≤ C * matrixHeight (torInf x) ^ d`
    for all `x` and `q ∈ Q'`. Here `F₀` is the union of the finitely many covering cosets
    `y L`. Proof: write `ofInfinite (torInf x) * q` as
    `pair (torInf x * infinite q) y * ofFinite (y⁻¹ * finite q)` with
    `y⁻¹ * finite q ∈ L`, drop the last factor by the level, apply the slice bound at `y`,
    and use `matrixHeight_mul_le` together with a bound `M` for `matrixHeight (infinite q)`
    on the compact `Q'`; the constant is `(∑ y ∈ t, D y) * M ^ d`.

## Main theorem

`exists_blockDecay [CompactSpace (AdeleQuotient F)] hS f Q hQ`: for a cuspidal realization
`S` (`hS : S.IsCuspidal`), a realized vector `f` and a compact set `Q` of adelic points,
there is an exponent `d` such that for every maximal block `h : a + b = n` with `0 < a`,
`0 < b` and every `N : ℕ` there is `C` with

`‖ev f (ofInfinite (torInf F n x) * q)‖ ≤ C * exp (-(N * ℓ)) * matrixHeight (torInf F n x) ^ d`

for all real `x : Fin n → ℝ`, `ℓ ≥ 0` such that every across-the-block difference
`x (e (inr r)) - x (e (inl p))` is at most `-ℓ` (with `e = finSumFinEquiv.trans (finCongr h)`),
and all `q ∈ Q`. The exponent `d` depends on `f` and `Q` only, not on the block or on `N`.
Proof: take the level `L` from `exists_level`, the exponent and `F₀` from
`exists_uniform_growth`, and apply `blockDecay_of_cuspidal` to the family above with weight
`w x = matrixHeight (torInf x) ^ d`; rational invariance is `evaluate_rational`. The
abstract theorem is applied at the index `u = 1`, where `S.envelopingAction 1 f = f`.
