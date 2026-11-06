# Closed-ideal effectiveness for a split square of bounded algebra maps

This is an internal prerequisite for finite-cover closed-ideal descent. It
proves an abstract two-member form of the ideal case of Kiehl's theorem for a
commuting square of bounded algebra maps. The motivating source is Berkovich,
*Étale cohomology for non-Archimedean analytic spaces* (1993), Kiehl's Theorem
and Remark 1.2.1(ii), printed p.15 / PDF p.12, registered as
`berkovich-1993-etale-cohomology`; its use is recorded in the paired Markdown
of `FiniteDomainIdealDescent`. The hypotheses below are an internal
abstraction; nothing in this module cites or transcribes a particular proof
from the source.

Here `K` is a normed field, and `A`, `A₁`, `A₂`, `A₁₂` are normed commutative
`K`-algebras. The maps `p₁ : A → A₁`, `p₂ : A → A₂`, `r₁ : A₁ → A₁₂` and
`r₂ : A₂ → A₁₂` are bounded `K`-algebra maps (`BoundedAlgHom`). No ultrametric
hypothesis, completeness of `K`, or nontrivial valuation is assumed. The closed
extension of ideals is the imported `BoundedAlgHom.closedIdealMap` from
`FiniteDomainIdealDescent`.

## The structure `SplitSquare`

`Langlands.Analytic.BoundedAlgHom.SplitSquare p₁ p₂ r₁ r₂` is a structure
bundling the hypotheses on the square. Its fields are:

- `comm`: `r₁ (p₁ a) = r₂ (p₂ a)` for every `a ∈ A`;
- `glue`: gluing of single elements. If `r₁ a₁ = r₂ a₂`, then some `a ∈ A`
  has `p₁ a = a₁` and `p₂ a = a₂`;
- `dense`: `r₂` has dense range;
- `bound`, `bound_nonneg`, `split`: a real constant `β ≥ 0` such that every
  `h ∈ A₁₂` is `r₁ h₁ + r₂ h₂` with `‖h₁‖ ≤ β‖h‖` and `‖h₂‖ ≤ β‖h‖`.

The constant is data, so `SplitSquare` is a type, not a proposition. The
theorems below are in the namespace `Langlands.Analytic.BoundedAlgHom.SplitSquare`.

## Splitting lemmas

`exists_split_of_approx` is the iteration step. Let `I₁ ⊆ A₁` and `I₂ ⊆ A₂` be
closed ideals of complete algebras, `Φ : V → A₁₂` a family with
`‖Φ v‖ ≤ M · N v`, and suppose that every `Φ v` can be written as
`r₁ e₁ + r₂ e₂ + Φ v'` with `e₁ ∈ I₁`, `e₂ ∈ I₂`, `‖eᵢ‖ ≤ c · N v` and
`N v' ≤ N v / 2` (`M, c ≥ 0`). Then every `Φ v` equals `r₁ e₁ + r₂ e₂` exactly,
with `eᵢ` in the ideals and `‖e₁‖ ≤ 2c · N v`. The proof iterates the chosen step,
bounds the `k`-th remainder by `N v / 2ᵏ` by induction, and sums the two
geometric series. The partial sums lie in the ideals, so their limits do too by
closedness. Continuity of `r₁` and `r₂` and the vanishing remainders identify
the limit.

`exists_split_of_generators` gives a uniform step. Assume `I₁` and `I₂`
are closed in complete algebras, with finite families `x : Fin n → A₁` in `I₁` and
`y : Fin m → A₂` in `I₂`. Assume matrices `B, C` over `A₁₂` with
`∑ₗ B k l · r₂(y l) = r₁(x k)` and `∑ₖ C l k · r₁(x k) = r₂(y l)`. Assume dense
range of `r₂`, and a bounded splitting
`h = r₁ h₁ + r₂ h₂`, `‖hᵢ‖ ≤ β‖h‖`, of every overlap element. Then there is
`c ≥ 0` such that every combination `∑ₖ u k · r₁(x k)` equals `r₁ e₁ + r₂ e₂`
with `e₁ ∈ I₁`, `e₂ ∈ I₂` and `‖e₁‖ ≤ c ∑ₖ ‖u k‖`.

In the proof, first approximate each entry `B k l` by some `r₂(B' k l)` within a
radius `δ` chosen from the bound on `r₂`, `β` and the entries of `C`. Then split
each coefficient `v k = r₁(p k) + r₂(q k)`. The term `r₁(p k) r₁(x k)` lies in
`r₁(I₁)`. The term `r₂(q k) r₁(x k)` equals
`r₂(q k ∑ₗ B' k l y l)` plus an error
`∑ₗ r₂(q k)(B k l - r₂(B' k l)) r₂(y l)`. Rewriting `r₂(y l)` through `C`
turns this error into a new combination of the `r₁(x j)`. Its coefficient size
is at most half the old one. The previous lemma then finishes the proof.

## Main theorem

`closedIdealMap_inf_comap_eq` takes `S : SplitSquare p₁ p₂ r₁ r₂`. It further
assumes that `A₁` and `A₂` are complete and Noetherian, and that every ideal of
`A₁`, `A₂` and `A₁₂` is closed.

For ideals `I₁ ⊆ A₁` and `I₂ ⊆ A₂` whose closed extensions to `A₁₂` agree, let
`J` be the intersection of the inverse images `p₁⁻¹(I₁) ⊓ p₂⁻¹(I₂)`. The
conclusion is `p₁.closedIdealMap J = I₁` and `p₂.closedIdealMap J = I₂`.

In both cases the containment `⊆` is the imported adjunction
`closedIdealMap_le_iff`. For the reverse containments, closedness of all ideals
of `A₁₂` turns the hypothesis into equality of the algebraic extensions
`r₁(I₁)A₁₂ = r₂(I₂)A₁₂`. Noetherianity gives finite generators `x` of `I₁` and
`y` of `I₂`, and this equality gives the matrices `B` and `C`.

*First side.* Let `g ∈ I₁` and `ε > 0`. Write `r₁ g = ∑ₗ c' l · r₂(y l)` and
approximate each `c' l` by `r₂(d l)`. Then `r₁ g - r₂(∑ₗ d l · y l)` is a
combination of the `r₁(x k)` with small coefficients. The uniform step writes it
as `r₁ e₁ + r₂ e₂` with `e₁ ∈ I₁`, `e₂ ∈ I₂` and `‖e₁‖ < ε`. Gluing
`g - e₁` with `∑ₗ d l · y l + e₂` gives `a ∈ J` with `p₁ a = g - e₁`. Hence `g`
lies in the closure of `p₁(J)A₁`.

*Second side.* Since every ideal of `A₁` is closed, the first side gives
`p₁(J)A₁ = I₁`. Hence `r₂ h ∈ r₁(p₁(J)A₁)A₁₂` for `h ∈ I₂`. Induction
on the span, with the exact splitting applied to each coefficient, shows that
`r₂ h = r₁ t + r₂ s` with `t ∈ I₁` and `s ∈ p₂(J)A₂`; the generator case uses
`r₁ ∘ p₁ = r₂ ∘ p₂`. Gluing `-t` with `s - h` gives `a ∈ J` with
`p₂ a = s - h`. Hence `h = s - p₂ a` lies in the closure of `p₂(J)A₂`.

## Scope

The square, the gluing property, the dense range and the splitting are
hypotheses, bundled in `SplitSquare`. This module proves none of them for any concrete affinoid cover,
and it states no finite-cover effectiveness theorem. The constant `β` may be
any nonnegative real. No contractivity of the maps, nonzero algebra,
nonempty spectrum or reducedness is assumed.
