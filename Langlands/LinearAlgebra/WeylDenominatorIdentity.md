# Alternating elements of `ℤ[M]` and the Weyl denominator identity

Module `Langlands.LinearAlgebra.WeylDenominatorIdentity`, namespace
`Langlands.LinearAlgebra.WeylCharacter`.

Throughout, `P : RootPairing ι ℤ M N` is a root pairing over `ℤ` and `ℤ[M]` is
the group ring `AddMonoidAlgebra ℤ M`, with basis elements `e^μ = single μ 1`.
The reflection group `W` is the Library's
`DominantTriangular.reflectionGroup P` and the positive cone is the Library's
`DominantTriangular.positiveCone P b` for a base `b`. Strict dominance
(`IsStrictlyDominant`), the stabilizer result `eq_one_of_isDominant_apply`,
`det_reflection`, `det_mul`, `det_word` and `pairing_rho_eq_one` come from the
companion module `Langlands.LinearAlgebra.SimpleReflectionWords`.

The main result is the Weyl denominator identity
`e^ρ ∏_{α > 0} (1 - e^{-α}) = ∑_{w ∈ W} det(w) e^{w ρ}`. In the literature it is
Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9,
§24.3 (in the proof of the Weyl character formula), and Bourbaki, *Lie Groups
and Lie Algebras*, Ch. VI §3.3 (anti-invariant elements). The literature
states it with `det(w) = (-1)^{ℓ(w)}`. Here the sign is the determinant of `w`
acting on `M`, which matches the target statement
`Langlands.GroupScheme.WeylCharacterFormulaStatement`. The Lean proof is the
standard uniqueness argument: both sides are alternating, both are supported
below `ρ` with coefficient `1` at `ρ`, and `ρ` is the only strictly dominant
element below `ρ`.

## The action of `W` on `ℤ[M]`

- `act w`: for a linear automorphism `w` of `M`, the ring automorphism of
  `ℤ[M]` with `e^μ ↦ e^{w μ}`. It is Mathlib's
  `AddMonoidAlgebra.mapDomainRingEquiv`.
- `act_single`, `coeff_act` (`(w f)(μ) = f(w⁻¹ μ)`), `act_mul`
  (`act (v w) = act v ∘ act w`) and `act_one`.

## Alternating elements

- `IsAlternating P f`: `act w f = det(w) • f` for every `w ∈ W`. `IsAlternating.sub`
  shows that differences of alternating elements are alternating.
- `det_mul_self_eq_one`: `det(w)² = 1`, since the determinant of a linear
  automorphism over `ℤ` is a unit of `ℤ` (`Int.units_mul_self`). `det_one`:
  `det(1) = 1`.
- `IsAlternating.coeff_apply`: an alternating `f` satisfies
  `f(μ) = det(w) · f(w μ)` for `w ∈ W`. This is the coefficient of `act w f` at
  `w μ`.
- `isAlternating_of_simple` (finite, reduced, `M` free of finite rank): if
  `act s_a f = -f` for every simple reflection `s_a`, then `f` is alternating.
  Write `w` as a word in simple reflections (`exists_word_eq`). Its determinant
  is `(-1)^{length}` (`det_word`). Then induct on the word.

## The alternating sum `J`

- `alternant P ν` is `J(ν) = ∑ᶠ_{w ∈ W} det(w) e^{w ν}`. The expression is the
  same as the `J` in the target statement. `alternant_eq_sum` rewrites the
  `finsum` as a `Finset` sum when `W` is a `Fintype`.
- `isAlternating_alternant` (finite `ι`): `J(ν)` is alternating. The group `W` is
  finite (`Fintype.ofFinite`, through the Library's finiteness instance). Then
  `act v J(ν) = ∑_w det(w) e^{v w ν}`. Reindex by `w ↦ v w` and use
  `det(v w) = det(v) det(w)` and `det(v)² = 1`.

## Coefficients at strictly dominant elements and uniqueness

- `coeff_alternant_of_isStrictlyDominant`: if `ν₀` is strictly dominant and `ν`
  is dominant, the coefficient of `J(ν₀)` at `ν` is `1` if `ν = ν₀` and `0`
  otherwise. Only `w = 1` can contribute: if `w ν₀ = ν` is dominant, then
  `w = 1` by `eq_one_of_isDominant_apply`.
- `eq_zero_of_isAlternating` (`M` free of finite rank): an alternating `f` whose
  coefficients vanish at all strictly dominant elements is `0`. Each `μ` has a
  dominant element `w μ` in its `W`-orbit (the Library's
  `exists_dominant_mem_orbit`), and `f(μ) = det(w) f(w μ)`. If `w μ` is
  strictly dominant, the hypothesis applies. Otherwise some simple coroot
  vanishes on `w μ`, so the simple reflection `s_a` fixes `w μ`. Alternation
  with `det(s_a) = -1` then gives `f(w μ) = -f(w μ)`, so `f(w μ) = 0`.
- `eq_alternant`: an alternating `f` that has the coefficients of `J(ν₀)` at all
  strictly dominant elements equals `J(ν₀)`. Apply the previous lemma to
  `f - J(ν₀)`.

## Elements supported below a given element

- `IsBelow b f ν₀`: every `μ` with `f(μ) ≠ 0` has `ν₀ - μ` in the positive cone.
- `IsBelow.mul`: if `f` is below `ν₀` and `g` is below `ν₁`, then `f g` is below
  `ν₀ + ν₁`. The support of a product lies in the sum of the supports
  (`AddMonoidAlgebra.support_coeff_mul_subset`).
- `IsBelow.coeff_mul`: in that situation `(f g)(ν₀ + ν₁) = f(ν₀) g(ν₁)`. The pair
  `(ν₀, ν₁)` is the only decomposition of `ν₀ + ν₁` from the two supports. If
  `x + y = ν₀ + ν₁`, then `ν₀ - x` and `-(ν₀ - x) = ν₁ - y` both lie in the cone.
  So both are `0` by the Library's `eq_zero_of_mem_positiveCone_of_neg_mem`.
  Mathlib's `AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd` then applies.
- `isBelow_single`, `isBelow_one_sub` (`1 - e^{-α}` is below `0` for `α` in the
  cone), `coeff_one_sub_zero` (its coefficient at `0` is `1` for `α ≠ 0`), and
  `isBelow_prod` (a finite product of elements below `0` is below `0`, and its
  coefficient at `0` is the product of the coefficients at `0`).

## The Weyl denominator

Here `ι` is a `Fintype`.

- `posRoots b`: the finset of indices `i` with `α_i` in the positive cone, with
  `mem_posRoots`.
- `denominator b ρ` is `e^ρ ∏_{α > 0} (1 - e^{-α})`. `isBelow_denominator`:
  it is below `ρ` with coefficient `1` at `ρ`.

The remaining results assume that `P` is reduced and that
`2 • ρ = ∑ᶠ (i) (_ : α_i ∈ positiveCone P b), α_i`. This is the hypothesis on
`rho` in the target statement.

- `act_reflection_denominator`: for a simple `a`, `s_a` sends the denominator
  to its negative. Since `⟨ρ, α_a^∨⟩ = 1` (`pairing_rho_eq_one`),
  `s_a ρ = ρ - α_a`. The reflection permutation of `s_a` permutes the positive
  roots other than `α_a` (`root_reflectionPerm_mem_iff`), so that part of the
  product is unchanged (`Finset.prod_nbij'`). The factor of `α_a` becomes
  `1 - e^{α_a}`, and
  `e^{ρ - α_a} (1 - e^{α_a}) = -e^ρ (1 - e^{-α_a})`.
- `isStrictlyDominant_rho`: `ρ` is strictly dominant, since `⟨ρ, α_a^∨⟩ = 1`.
- `eq_rho_of_isStrictlyDominant`: a strictly dominant `ν` with `ρ - ν` in the
  cone equals `ρ`. By integrality `⟨ν, α_a^∨⟩ ≥ 1 = ⟨ρ, α_a^∨⟩`, so `ν - ρ` is
  dominant. The Library's `rootForm_nonneg_of_mem_positiveCone` gives
  `RootForm(ν - ρ, ρ - ν) ≥ 0`. If `ρ ≠ ν`, then
  `rootForm_self_pos_of_mem_positiveCone` gives `RootForm(ρ - ν, ρ - ν) > 0`,
  a contradiction.
- `isAlternating_denominator` (`M` free of finite rank): the denominator is
  alternating, by `isAlternating_of_simple`.
- `eq_alternant_of_isBelow`: an alternating `f` with `f(ν₀) = 1` at a strictly
  dominant `ν₀`, and with no other strictly dominant element in its support,
  equals `J(ν₀)`. This is `eq_alternant` in the form used below.
- `denominator_eq_alternant` (**Weyl denominator identity**):
  `e^ρ ∏_{α > 0} (1 - e^{-α}) = J(ρ)`. The previous lemmas show that the
  denominator satisfies the hypotheses of `eq_alternant_of_isBelow` with
  `ν₀ = ρ`.
