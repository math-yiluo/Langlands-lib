# Spanning compact induction by translated local sections: proof

The module
`Langlands.Representation.Induction.CompactLocalSectionSpanningProof`
proves `Langlands.Induction.compactLocalSectionSpanning.{uG,uV}`. Its type is
exactly
[`Langlands.Induction.CompactLocalSectionSpanning.{uG,uV}`](CompactLocalSectionSpanningStatement.md).
The module imports only that statement module. The statement pair and every
pair it imports, among them
[`CompactLocalSection`](CompactLocalSection.md),
[`CompactQuotientProof`](CompactQuotientProof.md) and
[`Definitions`](Definitions.md), are unchanged.

The theorem keeps the statement's quantifiers. The group universe `uG` and the
coefficient universe `uV` are independent, and the literal compact-open basis
hypothesis is used as stated. Every subgroup `H` and every algebraic complex
representation `sigma : Representation ℂ H V` is allowed. The proof adds no
hypothesis. It does not assume that `sigma` is smooth, that `H \ G` is
compact, that any subgroup is normal, or that a function has a finite
decomposition. It introduces no coefficient topology and no measure. The
statement's hypotheses `T2Space G` and `IsClosed (H : Set G)` are accepted
but not used.

## Notation

For `f : CompactFunctions H sigma` write `f(y)` for
`eval H sigma f.1 y`. The theorem uses the published right translation
`compactInduced H sigma g`, with `(compactInduced H sigma g s)(y) = s(y * g)`
(private lemma `eval_compactInduced`, true by definition). Pointwise
subtraction is `eval_sub`, also by definition. The private set
`localSectionGenerators H sigma` is literally the statement's generator set:
the right translates `compactInduced H sigma g (compactDoubleCosetSection H
sigma K hK 1 v hv)` over all `g`, compact open `K`, `v` and `hv`.

## Translated sections centered at a point

Fix a compact open subgroup `K`, a point `x` and a vector `v` fixed by
`conjOpenSubgroup H K x`, that is, by `H ∩ x K x⁻¹`.

`conjugateOpenSubgroup K x` is the open subgroup
`K.comap (MulAut.conj x⁻¹)`, whose members are the `y` with
`x⁻¹ * y * x ∈ K`. It represents `L = x K x⁻¹`. The lemma
`isCompact_conjugateOpenSubgroup` shows that `L` is compact: as a set it is the
image of `K` under `k ↦ x * k * x⁻¹`. By `mem_fixedVectors_conjugate`, `v` is
fixed by `conjOpenSubgroup H L 1`, since its members `p` satisfy
`x⁻¹ * p * x ∈ K`.

The private `translatedSection H sigma K hK x v hv` is defined as
```lean
compactInduced H sigma x⁻¹
  (compactDoubleCosetSection H sigma L hL 1 v hv')
```
By `translatedSection_mem` it belongs to the generator set, with translation
element `x⁻¹`, subgroup `L`, center `1` and vector `v`. The following
properties follow from the published `compactDoubleCosetSection_apply`,
`compactDoubleCosetSection_mul` and
`compactDoubleCosetSection_support_subset`.

- `translatedSection_apply`: its value at `p * x * k`, with `p ∈ H` and
  `k ∈ K`, is `sigma p v`. Indeed, `p * x * k * x⁻¹ = p * 1 * (x * k * x⁻¹)`
  and `x * k * x⁻¹ ∈ L`.
- `translatedSection_mul`: it is right `K`-invariant, because
  `y * k * x⁻¹ = (y * x⁻¹) * (x * k * x⁻¹)`.
- `exists_eq_of_translatedSection_ne_zero`: it vanishes off `H * x * K`.
  If its value at `y` is nonzero, the support lemma gives `l ∈ L` with
  `y * x⁻¹ * l⁻¹ ∈ H`. Then `y = p * x * k` with
  `p = y * x⁻¹ * l⁻¹` and `k = x⁻¹ * l * x ∈ K`.

The proof therefore never needs a separate identity between the section
centered at `x` and the translated section. It uses only these three
properties.

## The finite-support decomposition

The internal lemma `mem_span_of_doubleCoset_cover` carries the argument. Fix
a compact open subgroup `K` and a finite set `t ⊆ G`. Let `f` be a compact
function such that:

1. `f(y * k) = f(y)` for all `k ∈ K` and `y`;
2. every `y` with `f(y) ≠ 0` has the form `p * x * k` with `x ∈ t`, `p ∈ H`
   and `k ∈ K`.

Then `f` lies in the complex span of the generator set. The proof is by
induction on `t` (`Finset.induction_on`), for all such `f` at once.

- If `t` is empty, condition 2 forces `f(y) = 0` for every `y`, so `f = 0`.
- For `t ∪ {x}`, put `v = f(x)`. Covariance (`eval_covariant`) and
  condition 1 give `f(p * x * k) = sigma p v`. They also show that `v` is
  fixed by `H ∩ x K x⁻¹`: if `x⁻¹ * p * x ∈ K`, then
  `sigma p v = f(p * x) = f(x * (x⁻¹ * p * x)) = v`.
  Let `T` be `translatedSection H sigma K hK x v hv`, a generator. The
  difference `f - T` satisfies condition 1, since both terms are right
  `K`-invariant. It also satisfies condition 2 for the smaller set `t`. On
  `H * x * K` both terms equal `sigma p v`, so the difference vanishes. Off
  `H * x * K`, `T` vanishes, so a nonzero value of `f - T` is a nonzero value
  of `f`. Condition 2 for `f` then places the point in a double coset
  `H * x' * K` with `x' ∈ t ∪ {x}`, and `x' = x` is excluded. The induction
  hypothesis puts `f - T` in the span, hence `f = (f - T) + T` as well.

This argument does not select distinct double cosets. It does not need
disjointness of the cover, and it never forms a partition of the support.
Overlapping members of the cover are harmless: after a double coset has been
removed, the difference already vanishes there.

## The main theorem

`span_localSectionGenerators_eq_top` proves the span equality for fixed
`G`, `H` and `sigma` from the basis hypothesis. Let `f` be a compact function.

1. Membership of `f` in the smooth vectors gives an open subgroup `K₀` that
   fixes the whole function `f.1.1` under right translation. The basis
   hypothesis, applied to the open set `K₀` containing `1`, gives a compact
   open subgroup `K ⊆ K₀`. So `f(y * k) = f(y)` for all `k ∈ K`.
2. The projected nonzero support `quotientSupport H (eval H sigma f.1)` is
   compact, because `f` is in `CompactFunctions H sigma`. The sets
   `quotientMap H '' (i * K)` are open in `H \ G`, since `quotientMap H` is
   an open map (`MulAction.isOpenQuotientMap_quotientMk`) and `i * K` is
   open. They cover the support, because the coset of `y` lies in the set
   for `i = y`. `IsCompact.elim_finite_subcover` gives a finite `t`. Only the
   compactness of this projected support is used, not compactness of `H \ G`,
   so `exists_finset_doubleCoset_cover` is not needed.
3. If `f(y) ≠ 0`, then the coset of `y` equals the coset of some `i * k`
   with `i ∈ t` and `k ∈ K`. Hence `y * (i * k)⁻¹ ∈ H`, and
   `y = (y * (i * k)⁻¹) * i * k`. This is condition 2, and
   `mem_span_of_doubleCoset_cover` places `f` in the span.

Thus every compact function lies in the span, so the span is `⊤`. The public
theorem `compactLocalSectionSpanning` introduces the quantified data and
applies this lemma. All auxiliary declarations are `private`. The only
public declaration is `compactLocalSectionSpanning`.

## Provenance

The finite-support decomposition above is internal. It is derived from the
published actual-function definitions, the right-translation action and the
double-coset section construction. The task suggested a related route through
selected distinct double cosets. The implemented route is the induction
described above instead. Bernstein and Zelevinsky (1977), section 5.17, is
cited by the task as motivation only. That section is Case IV of the proof of
their Theorem 5.2, where an averaging map on induced functions is defined. It
states no spanning lemma, and this module neither quotes nor formalizes it. No
draft of another worker was reused.

## Development check

The module compiles in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
(Lean 4.34.0, Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`),
with no errors or warnings. Inspection of
`Langlands.Induction.compactLocalSectionSpanning` reports a theorem with level
parameters `uG` and `uV`. Its axioms are only `propext`, `Classical.choice`
and `Quot.sound`. These development checks are not independent acceptance or
publication.
