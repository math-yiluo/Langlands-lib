# Integrals over a window of a periodic level function

The module `Langlands.BaseChange.PeriodicWindowIntegral` (namespace
`Langlands.BaseChange.PeriodicWindow`) proves an elementary integration lemma that replaces, in
the Library's construction of pseudo-coefficients of supercuspidal representations, the
integral over the quotient of a group by a discrete central subgroup.

## Setting

`G` is a group with a measurable space structure such that multiplication is measurable
(`MeasurableMul G`), and `μ` is a left-invariant measure (`μ.IsMulLeftInvariant`). Functions
take values in a real Banach space `E`. A *level function* is a map `a : G → ℤ` with
`a (g * h) = a g + a h`; `z ∈ G` is an element with `a z = m` for a natural number `m`.

- `levelSet a j` is the set `{g | a g = j}`.
- `window a m k` is the set `{g | k ≤ a g ∧ a g < k + m}`.

## Results

- `window_indicator_eq_sum`: the indicator of `window a m k` applied to `Φ` is the sum over
  `i < m` of the indicators of the level sets `levelSet a (k + i)` (any map `a : G → ℤ`).
- `sum_range_shift_of_periodic`: if `c : ℤ → E` satisfies `c (j + m) = c j`, then
  `∑_{i < m} c (k + i) = ∑_{i < m} c i` for every `k : ℤ` (induction on `k`, both directions).
- `integral_levelSet_add`: if `Φ (z * g) = Φ g` for all `g`, then the integrals of `Φ` over
  `levelSet a (j + m)` and over `levelSet a j` agree. Left multiplication by `z` maps the second
  level set onto the first, `Φ` is unchanged, and `μ` is left invariant
  (`integral_mul_left_eq_self`). No integrability is needed.
- `integral_window_eq_sum`: if `Φ` is integrable on every level set, the integral over a
  window is the sum of the `m` level-set integrals it contains (`integral_finsetSum`).
- `integral_window_eq_integral_window_zero`: under both hypotheses, the window integral does
  not depend on the position `k` of the window.
- `integral_window_comp_mul_left` (the main result): if `Φ (z * g) = Φ g` for all `g` and `Φ`
  is integrable on every level set, then for every `h ∈ G`
  `∫ 1_{window a m 0}(g) Φ(h g) dμ(g) = ∫ 1_{window a m 0}(g) Φ(g) dμ(g)`.
  The substitution `g ↦ h g` (left invariance) turns the left side into the integral of `Φ`
  over `window a m (a h)`, which equals the integral over `window a m 0`.

## Use

For `G = GL_n(F)` over a nonarchimedean local field, `a = ord_F ∘ det` and `z` the scalar
matrix of a uniformizer (`a z = n`), the window `{0 ≤ ord_F det g < n}` contains exactly one
point of each orbit of `z^ℤ` acting by multiplication, and the window integral of a
`z`-periodic function plays the role of the integral over `z^ℤ \ GL_n(F)`. The lemma
`integral_window_comp_mul_left` is the left invariance of that integral. It is used in
`Langlands.BaseChange.SupercuspidalCutoffTraces` and
`Langlands.BaseChange.SupercuspidalCutoffPseudoCoefficient`.

## Provenance

Internal content. The argument is the standard identification of an integral over `Z \ G`
with an integral over a fundamental domain for a discrete central subgroup, written for an
integer-valued level function so that no quotient measure is needed.
