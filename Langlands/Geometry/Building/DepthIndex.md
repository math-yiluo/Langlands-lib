# The Kaletha–Prasad depth monoid of real, strict and infinite depths

Author: Worker 1238.

The module `Langlands.Geometry.Building.DepthIndex` constructs the totally ordered commutative monoid `ℝ̃ = (ℝ × {0, 1}) ∪ {∞}` of Kaletha–Prasad, Section 1.6, in the version that replaces the original section. The pair `(r, 0)` is the ordinary real depth `r`, the pair `(r, 1)` is the strict depth `r+`, and `∞` is a single greatest element. The module also constructs the operation `x ↦ x+`. It proves the computation laws that the source states, and the facts that rule out stronger algebraic structure.

## Source

Kaletha–Prasad, *Corrections and additions to Bruhat–Tits theory, a new approach*, version of 1 November 2024. It is registered as `kaletha-prasad-2024-corrections`, SHA-256 `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`. The item "Section 1.6. Replace the text of that section with the following" starts on PDF page 21. The definition of `ℝ̃` is on PDF page 22.

- PDF pages 21–22 explain `r+` as "larger than r, but smaller than any real number that is larger than r".
- PDF page 22 introduces "the set `R̃ = (R × {0, 1}) ∪ {∞}`" and writes `r` for `(r, 0)` and `r+` for `(r, 1)`. It makes `R̃` into "a totally ordered commutative monoid that contains R as an ordered submonoid" by four rules:
  1. `r + (s+) = (r+) + s = (r+) + (s+) = (r + s)+`;
  2. `r + ∞ = (r+) + ∞ = ∞`;
  3. `∞ > r+ > r` for every real `r`;
  4. `r+ > s+` if `r > s`.

  It then defines `r̃ ↦ r̃+` by `r ↦ r+`, `(r+)+ = r+` and `∞+ = ∞`.
- The same page gives the interval model: `r` is `[r, ∞)`, `r+` is `(r, ∞)` and `∞` is the empty interval. Addition is pointwise addition of intervals, `+` takes the interior, and the order is the opposite of inclusion.

The original book section is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (Cambridge, 2023), §1.6, printed pages 66–67 (PDF pages 97–98). It is registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`. The corrected text above replaces it.

The source does not spell out every rule, so a few are read off the source's own descriptions. Ordinary real addition and the order on ordinary reals come from "contains R as an ordered submonoid". `∞ + ∞ = ∞` comes from the interval model, where the sum of two empty intervals is empty. The comparison of `r+` with an ordinary `s` comes from the remark that `r+` is below every real number larger than `r`; the interval model gives the same comparison. Together, these determine the lexicographic order and the "or" rule for flags used below. Under ordinary Boolean-ring addition of flags, `(r+) + (s+)` would be the ordinary `r + s`. That contradicts rule (1), so the flags are combined by logical or.

## Representation

- `FiniteDepth` is a structure with a real part `re : ℝ` and a flag `strict : Bool`. Here `false` stands for `0` (ordinary) and `true` for `1` (strict).
  - Its `LinearOrder` is pulled back along the injective map `toLexPair x = toLex (x.re, x.strict)` into Mathlib's lexicographic product `ℝ ×ₗ Bool`, where `false < true`.
  - `FiniteDepth.le_iff` and `FiniteDepth.lt_iff` state the order: compare real parts first, and on equal real parts compare flags.
  - Addition is `⟨x.re + y.re, x.strict || y.strict⟩` (`add_re`, `add_strict`), and zero is `⟨0, false⟩`.
  - The instances are `AddCommMonoid` and `IsOrderedAddMonoid`. Monotonicity is proved by cases on the order and the three flags.
  - `FiniteDepth.plus x = ⟨x.re, true⟩`, with `monotone_plus` and `le_plus`.
- `DepthIndex` is a `def` equal to `WithTop FiniteDepth`, so `∞` is `⊤`. Its `AddCommMonoid`, `LinearOrder`, `OrderTop` and `IsOrderedAddMonoid` instances are Mathlib's `WithTop` instances, transported by `inferInstanceAs`. Mathlib's `WithTop` addition sends any sum with a `⊤` summand to `⊤`.

## Constructors and cases

- `ofFinite x`, `ord r = ofFinite ⟨r, false⟩` (the depth `r`) and `strict r = ofFinite ⟨r, true⟩` (the depth `r+`). These are defined for every real `r`, negative ones included.
- `ofFinite_mk` rewrites `ofFinite ⟨r, b⟩` as `strict r` or `ord r`, according to `b`.
- `exists_eq_ord_or_strict_or_top` says that every depth is `ord r`, `strict r` or `⊤`. The `@[elab_as_elim]` principle `DepthIndex.ind` packages this for `induction … using DepthIndex.ind`.
- Injectivity: `ofFinite_injective`, `ord_injective`, `strict_injective`, `ofFinite_inj`, `ord_inj`, `strict_inj`.
- Disjointness: `ord_ne_strict`, `strict_ne_ord`, `ord_ne_top`, `strict_ne_top`, `top_ne_ord`, `top_ne_strict`, `ofFinite_ne_top`.

## Order

The order is the lexicographic order on the finite part, with ordinary before strict, and `⊤` above everything. For real `r, s`:

- `ord_le_ord`, `ord_lt_ord`: `r ≤ s ↔ r ≤ s` and `r < s ↔ r < s`, for ordinary depths.
- `strict_le_strict`, `strict_lt_strict`: `r+ ≤ s+ ↔ r ≤ s` and `r+ < s+ ↔ r < s`.
- `ord_le_strict`, `ord_lt_strict`: `r ≤ s+ ↔ r ≤ s` and `r < s+ ↔ r ≤ s`.
- `strict_le_ord`, `strict_lt_ord`: `r+ ≤ s ↔ r < s` and `r+ < s ↔ r < s`.
- `ord_lt_strict_self r`: `r < r+`.
- Infinity: `ord_lt_top`, `strict_lt_top` and `ofFinite_lt_top` say every finite depth is below `∞`. `not_top_le_ord` and `not_top_le_strict` say `∞` is not below any finite depth. `le_top'`, `top_le_iff'` and `lt_top_iff` give the general statements for `⊤`.
- `ofFinite_le_ofFinite`, `ofFinite_lt_ofFinite`: `ofFinite` preserves and reflects the order.
- `ord_lt_strict_lt_ord_lt_strict`: if `r < s`, then `r < r+ < s < s+`.
- `strictMono_ord`, `strictMono_strict`. The order embeddings are `ordOrderEmbedding : ℝ ↪o DepthIndex` (`r ↦ r`) and `strictOrderEmbedding : ℝ ↪o DepthIndex` (`r ↦ r+`). Their `_apply` lemmas compute them, and `ord_le_ord` gives order reflection for the ordinary inclusion.

## Addition

- `ofFinite_add` says `ofFinite` is additive.
- `zero_def` and `ord_zero` identify the zero of the monoid with the ordinary depth `0`.
- `ord_add_ord`: `r + s` is the ordinary depth `r + s`.
- `ord_add_strict`, `strict_add_ord`, `strict_add_strict`: `r + s+ = r+ + s = r+ + s+ = (r + s)+`.
- `DepthIndex.top_add`, `DepthIndex.add_top`: `∞ + x = x + ∞ = ∞` for every `x`, including `x = ∞`.
- The commutative monoid laws are the `AddCommMonoid` instance.
- Monotonicity is the `IsOrderedAddMonoid` instance, restated per argument as `add_monotone_left` and `add_monotone_right`.
- `ordAddMonoidHom : ℝ →+ DepthIndex` is the ordinary real inclusion as an additive monoid homomorphism, with `ordAddMonoidHom_apply` and `ord_add`. Together with `ordOrderEmbedding`, it realizes `ℝ` as an ordered submonoid.

`top_add` and `add_top` are `protected`, because the root-level Mathlib lemmas of the same name need the class `LinearOrderedAddCommMonoidWithTop`, which is deliberately not instantiated (see the next section).

## The plus operation

`plus = WithTop.map FiniteDepth.plus`, defined on the whole carrier:

- `plus_ord`: `plus r = r+`.
- `plus_strict`: `plus (r+) = r+`.
- `plus_top`: `plus ∞ = ∞`.
- `monotone_plus`: `plus` is monotone.
- `le_plus`: `plus` is inflationary, `x ≤ plus x`.
- `plus_plus`: `plus` is idempotent.

Corrected Definition 1.6.3 introduces a separate convention, `X_(∞+) = ∅`, for filtration layers. That convention is not used here. The monoid operation fixes infinity, `plus ⊤ = ⊤`, as the source's rule `∞+ = ∞` requires.

## What does not hold

These facts are proved in `DepthIndex.Example`, so that no stronger structure is assumed by mistake:

- `not_forall_zero_le`: some depth (namely `-1`) is below `0`, so the order is not canonical for addition. The module provides no `CanonicallyOrderedAdd` instance.
- `strict_zero_add_ord`, `not_isAddLeftRegular_strict_zero`: `0+ + r = 0+ + r+`, so adding strict zero is not injective and addition is not cancellative.
  - In particular, the field `isAddLeftRegular_of_ne_top` of Mathlib's `LinearOrderedAddCommMonoidWithTop` fails at `x = strict 0 ≠ ⊤`. The module therefore provides no instance of that class.
- `not_strictMono_strict_zero_add`: translation by strict zero is monotone but not strictly monotone.
- `top_add_ord_eq_top_add_strict`: translation by `∞` sends every depth to `∞`.
- `plus_zero_ne_zero`: `plus` does not preserve zero.

## Regressions

All of these are in `DepthIndex.Example`:

- `ord_neg_one_lt_zero`: `-1 < 0`.
- `ord_lt_strict_lt_ord`: if `r < s`, then `r < r+ < s`. A concrete case is `ord_neg_one_lt_strict_neg_one_lt_zero`, which says `-1 < (-1)+ < 0`.
- `zero_ne_strict_zero` and `zero_lt_strict_zero`: `0 ≠ 0+` and `0 < 0+`.
- `strict_one_add_strict_neg_two`: `1+ + (-2)+ = (-1)+`.
- `strict_neg_one_add_top` and `top_add_ord_neg_one`: absorption by `∞`.
- `plus_plus_zero`: `plus (plus 0) = 0+`.

## Scope

This unit constructs no filtration, root group, valuation, root system, apartment or building. It also does not construct scalar multiplication on depths, the interval realization of `ℝ̃`, any completeness property, the convention `X_(∞+) = ∅`, or the source's correspondence between filtrations and functions (Fact 1.6.5).
