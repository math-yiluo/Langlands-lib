# Parabolics with a maximal Levi determined by a missed direction

`Langlands.GroupScheme.MaximalLeviConeComplementStatement.{u}` is a Prop-valued
definition. This module states it and proves nothing.

## Source

Renard, Représentations des groupes réductifs p-adiques (2026 version), VII.1.3,
proof of the theorem (printed p.225, PDF p.231). There `M` is a maximal standard
Levi, and Renard says: "Comme `M` est maximal, `A_M/A_G` est de dimension 1". He
then splits the restriction to `A_M` of the central character of `ρ` into three
mutually exclusive cases: `|χ| = 1` on `A_M`, `|χ| > 1` on `A_M^{++}`, or `|χ| < 1` on
`A_M^{++}`. On PDF p.230 he notes that `w·P` is the parabolic opposite to the
standard parabolic `P'` with Levi factor `w·M`, where `W(M,∗) = {1, w}`. Renard defines maximal Levi subgroups in V.4.8
(printed p.122, PDF p.128): they are the Levi factors of maximal proper parabolics,
the standard ones corresponding to `Θ = Δ∅ \ {α}`.

This statement is internal and derived. It isolates the structural fact behind that
case split, for the exponent comparison in the unitarizable-constituent step of
VII.1.3. It does not translate a numbered statement of the source.

The expected argument goes as follows. It is explanation only; the module records just
the statement.

- A parabolic `Q` with Levi `M` has the same rank as `P`. For a presentation of `Q`
  (a maximal split torus, a generic cocharacter `ν` and a set `J` of simple relative
  roots), exactly one simple root `α` lies outside `J`, since
  `dim A_M = dim A_G + 1`. So `Q` has one restricted root `β_Q`, the restriction of
  `α` to `A`, and its positive cone is the open ray `{c β_Q : c > 0}`.
- The cocharacters of `A` that are central in `G` span the real cocharacter space
  `a_G` of `A_G` inside `a_M`. Its annihilator in `Vstar A` is the dual of
  `a_M / a_G`, so it has dimension one. The pairing condition on `x` says exactly that
  `x` lies in this annihilator. The root `β_Q` is nonzero and vanishes on `A_G`, so it
  also lies in this line. Hence `x = c β_Q` for a real `c ≠ 0`.
- If `x` lies outside the cone of `Q`, then `c < 0`, so `-x` lies in that cone.
  For a cocharacter `λ` of `A` with `⟨-x, λ⟩ > 0`, the image of `Q` is the dynamic
  parabolic `P(λ)` and its unipotent radical is `U(λ)`. Two such `Q₁, Q₂` therefore
  have equal images and equal radical images.

## The proposition

It quantifies, in this order:

- an arbitrary field `k : Type u`;
- a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`; the instances
  `IsAffineHom` and `Smooth` of the structure map come from `hG`;
- group schemes `P, M` and a commutative group scheme `A` over `Spec k`, with maps
  `p : P ⟶ G`, `l : M ⟶ P` and `a : A ⟶ M`.

It assumes:

1. `IsParabolicSubgroup p`, `IsRationalLeviSubgroup l` and `¬ IsIso p`. So `P` is an
   actual proper rational parabolic with rational Levi `M`.
2. Maximality, in the same form as in the published
   `MaximalLeviContainmentStatement` and
   `MaximalLeviSupercuspidalUnitarizableConstituentStatement`. For every rational
   parabolic `q' : Q' ⟶ G` and every `j : P ⟶ Q'` with `j ≫ q' = p`, either `j` or
   `q'` is an isomorphism.
3. `IsSplitComponent a`: `A` is a split component `A_M` of `M`.
4. A nonzero `x : Vstar A`, a real character of `A` (characters tensored with `ℝ`).
   For every cocharacter `ν` of `A` such that `ν ≫ a ≫ l ≫ p` is central in `G`,
   `pair A x (1 ⊗ ν) = 0`.
5. Group schemes `Q₁, U₁, Q₂, U₂` with maps `qᵢ : Qᵢ ⟶ G`, `lQᵢ : M ⟶ Qᵢ` and
   `rQᵢ : Uᵢ ⟶ Qᵢ`. Each `rQᵢ` is a geometric unipotent radical
   (`LeviSubgroup.IsGeometricUnipotentRadical`), and `lQᵢ ≫ qᵢ = l ≫ p`. So each `Qᵢ`
   contains `M` with the same image in `G`.
6. Presentations `presᵢ : ParabolicRootPresentation qᵢ lQᵢ a`. Their compatibility
   fields make each `qᵢ` an actual parabolic with rational Levi `lQᵢ`. The positive cone
   `presᵢ.positiveCone` is the set of strictly positive combinations of the restricted
   simple roots on `A` outside `J`.
7. `x ∉ pres₁.positiveCone` and `x ∉ pres₂.positiveCone`.

It concludes `SubgroupFunctor.range q₁ = SubgroupFunctor.range q₂` and
`SubgroupFunctor.range (rQ₁ ≫ q₁) = SubgroupFunctor.range (rQ₂ ≫ q₂)`: the two
parabolics, and their unipotent radicals, coincide as subgroup functors of `G`.

The hypothesis `x ≠ 0` is necessary. The positive cone of a proper parabolic does not
contain `0`, while `P` and its opposite have different images.

## Use

In the unitarizable-constituent step, `x` is the real part of an exponent along a
parabolic with Levi `M`. For `w ∈ G(k)` normalizing `M`, the conjugate `wPw⁻¹` gets a
transported presentation. If `Ad(w)` fixes `x`, the statement applied to `x` or `-x` shows that
`wPw⁻¹` and `P` have the same image. The parabolic self-normalizer statement then puts
`w` in `P`. This identifies the unique full geometric-lemma piece carrying a given
exponent.

## Scope

The field is arbitrary, with no topology or valuation. The statement asserts nothing
about the existence of presentations, and nothing about parabolics that do not contain
`M`. It does not state that a parabolic with Levi `M` is maximal, nor that exactly two
such parabolics exist. Those facts appear only in the explanation above.
