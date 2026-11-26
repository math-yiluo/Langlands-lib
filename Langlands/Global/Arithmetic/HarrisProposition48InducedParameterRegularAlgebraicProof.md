# Regular algebraicity from the induced complex-place parameters in Proposition 4.8

Module `Langlands.Global.Arithmetic.HarrisProposition48InducedParameterRegularAlgebraicProof`.
The helper lemmas are in namespace
`Langlands.Global.Harris.InducedParameterRegularAlgebraic`, and the main theorem is in
`Langlands.Global.Harris`.

The theorem `Langlands.Global.Harris.proposition48InducedParameterRegularAlgebraic.{uF}`
proves the published statement
`Langlands.Global.Harris.Proposition48InducedParameterRegularAlgebraicStatement.{uF}` from
module `HarrisProposition48MackeyTransportStatement`. The universe `uF` is arbitrary. No
hypothesis is added: the archimedean bridge `CuspidalComplexParameterBridgeTCStatement.{0}` stays
a premise, as in the statement, and no rank hypothesis is used. The proof uses only `propext`,
`Classical.choice` and `Quot.sound`.

## The statement

Assume the bridge. Let `Q : Proposition48Problem` have a character `ξ = Q.ξ` of `E' = Q.E'`
with three properties:

- `IsAlgebraicAfterTwist ([E' : E] - 1) ξ`;
- `IsRelativelyRegular E ξ`;
- `IsConjugateInverse ξ`.

Then every cuspidal class `c` of `GL_(r+1)` over `E = Q.E` with
`Q.HasInducedComplexPlaceParameters c` is regular algebraic.

## The proof

Write `n = [E' : E]` and `a = n - 1`. The fields `E` and `E'` are CM, so every infinite place is
complex.

### Two uniqueness lemmas for complex powers

- `eq_zero_of_forall_cpow_eq_one`: if `r ^ s = 1` for every real `r > 0`, then `s = 0`. Take
  `r = exp t` with `t = 1/(‖s‖ + 1)`. Then `exp (t s) = 1`, so `t s = 2πik` for an integer `k`.
  Since `‖t s‖ < 1 < 2π`, `k = 0`, and hence `s = 0`.
- `eq_zero_of_forall_norm_eq_one_zpow_eq_one`: if `z ^ m = 1` for every `z` of norm one, then
  `m = 0`. For `m ≠ 0`, the point `z = exp(iπ/m)` has `z ^ m = -1`.

### Character data of an algebraic conjugate-inverse character

`characterData_of_twist_conj`: let `d` be character data, so that
`d(z) = (z/|z|)^k |z|^(2s)` with `k = d.weight` and `s = d.exponent`. Assume that for all
`z ∈ ℂˣ`

- (B) `d(z) |z|^a = z^p z̄^q`, and
- (C) `d(z̄) = d(z)⁻¹`.

Then `s = 0`, `k = p - q` and `p + q = a`.

- *Exponent.* For real `r > 0`, (C) gives `d(r)² = 1`. Since `d(r) = r^(2s)`, we get
  `r^(4s) = 1`, so `s = 0` by the first uniqueness lemma.
- *Weight.* For `|z| = 1` we have `z̄ = z⁻¹`, and (B) reads `z^k = z^(p-q)`. So `k = p - q` by
  the second uniqueness lemma.
- *Sum.* At `z = 2`, now with `s = 0`, (B) reads `2^a = 2^(p+q)`.

### One infinite place of a Hecke character

- `exists_units_map_extensionEmbedding`: at a complex place `w`, every unit of `ℂ` is the
  coordinate of a unit of the completion `E'_w`. This uses Mathlib's
  `ringEquivComplexOfIsComplex`.
- `infiniteComponent_mul_norm_pow`: let `ξ_∞ · ∏_τ |x_τ|^a` be the character of the infinity
  type `t`. Evaluate this identity at the infinite idele equal to `y` at `w` and to `1`
  elsewhere. In the coordinate of `w` this gives `ξ_w(y) |y|^a = y^(t σ) ȳ^(t σ̄)`, where `σ`
  is the embedding of `w`.
- `infiniteComponent_of_coordinate_conj`: the CM involution acts on the idele concentrated at
  `w` by complex conjugation of its coordinate (`ideleComplexConj_infinite_coordinate`), and it
  fixes the other coordinates, which are `1`. So `IsConjugateInverse ξ` gives
  `ξ_w(y') = ξ_w(y)⁻¹` whenever `y'` has the conjugate coordinate of `y`.
- `infiniteComponent_completionMap`: let `d` be a parameter of `ξ` at `w | v`. On `E_vˣ`, read
  through the completion map, `ξ_w` has the character of `normParameter v w d`. This is `d` when
  the embedding of `w` restricts to that of `v`, and `d̄` otherwise. The proof uses
  `extensionEmbedding_completionMap_of_comp_eq` and `extensionEmbedding_completionMap_of_comp_ne`.
- `card_infinitePlacesAbove_eq_finrank`: exactly `[E' : E]` places lie above a complex place.
  The local degrees sum to the global degree (`infiniteLocalDegree_sum`), and each local degree
  is `1` (`isUnramified_of_isComplex`).
- `complexPlaceLanglandsSum_singleton`: the Langlands sum of the singletons `[dξ w]`, in the
  enumeration `e`, is `List.ofFn (fun i => normParameter v (e i) (dξ (e i)))`.

### Clozel regularity of the induced parameter

`isClozelRegularAlgebraic_complexPlaceLanglandsSum`: fix a complex place `v` of `E`, an
enumeration `e : Fin d ≃ InfinitePlacesAbove E' v` and actual parameters `dξ w` of `ξ`. Then
the Langlands sum is `ComplexPlaceParameter.IsClozelRegularAlgebraic d`.

1. `d = n`, by the place count.
2. For each `w`, (B) holds for `dξ w`, by the twisted algebraicity at `w` and surjectivity of
   the coordinate. Likewise (C) holds, by conjugate inversion at `w`. So `dξ w` has exponent
   `0`, weight `p - q` and `p + q = a`.
3. Let `T w = normParameter v w (dξ w)` be the transported parameter. Conjugation negates the
   weight and keeps the exponent. So `T w` has exponent `0` and weight `a - 2m` for an integer
   `m` (`m = q` or `m = p`).
4. Suppose `T w` and `T w'` have equal weights. Their exponents are both `0`, so they have the
   same character. Then `ξ_w` and `ξ_w'` agree on `E_vˣ` through the completion maps, and
   relative regularity forces `w = w'`.
5. The list is `List.ofFn (T ∘ e)`, of length `d`. Each entry has `z`-exponent `k/2` and
   `z̄`-exponent `-k/2`, where `k = a - 2m` is its weight. These lie in `(d - 1)/2 + ℤ` because
   `d - 1 = a`. Both exponent lists are injective in the index, by step 4 and injectivity of `e`.

### The main theorem

Choose a representative `S` of `c`, and choose for each complex place `v` the list `ds v` given
by `HasInducedComplexPlaceParameters`. The bridge's second conjunct provides a character `θ` of
the enveloping center that matches `ds`, and `S` has infinitesimal character `θ`. By the third
conjunct with rank `r + 1`, `θ` is regular algebraic once every `ds v` is Clozel regular
algebraic of rank `r + 1`.

Fix `v`. The list `ds v` is a permutation of the Langlands sum over an enumeration
`Fin d ≃ InfinitePlacesAbove E' v`. The length clause of `HasComplexPlaceParameter` gives
`length (ds v) = r + 1`, and the Langlands sum has length `d`, so `d = r + 1`. Transport along
the permutation (`isClozelRegularAlgebraic_iff_of_perm`), then apply the previous lemma. This
gives regularity, and `isoClass_isRegularAlgebraic_iff` turns it into
`c.IsRegularAlgebraic`. The first conjunct of the bridge (parameter existence) is not used.

## Relation to the source

The target is an internal interface for the exact-stabilizer form of the induction for Harris
(1998), Proposition 4.8. Its source is the plan note
`operator-external-inputs-plan-2026-11-16` (`external-inputs-plan.tex`), Section 4.8, the
infinity type (lines 910–912). The proof implements the argument recorded under "Why" in the
paired Markdown of the statement module:

- the length clause fixes the rank;
- conjugate inversion kills the polar exponents;
- the twist fixes the parity of the weights;
- relative regularity, read through the orientation of `complexPlaceParameterTransport`, makes
  the transported weights distinct;
- the bridge converts Clozel regularity of the lists into regular algebraicity.
