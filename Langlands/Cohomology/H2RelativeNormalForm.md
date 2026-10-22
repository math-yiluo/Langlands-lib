# Relative degree-two cocycle normal form

Authors: Worker 10 and Worker 138. Worker 10 implemented the explicit-cochain
proof below. Worker 138 supplied the normal-form strategy and the principal
one-cocycle extraction using Mathlib's `H1π_eq_zero_iff`, reused in
`conjugate_primitive`.

## The theorem and its scope

`Langlands.Cohomology.h2RelativeCocycleNormalForm` proves exactly the published
proposition `Langlands.Cohomology.H2RelativeCocycleNormalForm.{u}` from
`Langlands.Cohomology.H2RelativeNormalFormStatement`. The theorem has no outer
hypotheses. It retains the arbitrary common universe, commutative coefficient
ring, group, representation, and normal subgroup quantified by that proposition.

Write `ρ` for the representation of `G` on `A`, and `S` for the normal subgroup.
The hypothesis is `Subsingleton (groupCohomology (Rep.res S.subtype A) 1)`.
For every actual Mathlib two-cocycle `c` whose restriction to `S × S` is a
boundary, the theorem constructs a single one-cochain `B : G → A` such that

`c(s,g) = d₁₂ B(s,g)` and `c(g,s) = d₁₂ B(g,s)`

for every `s ∈ S` and `g ∈ G`. Here Mathlib's differential is

`d₁₂ B(g,h) = ρ(g) B(h) - B(gh) + B(g)`.

The proof does not assume finiteness, trivial action, field coefficients,
normalized cochains, or an exactness theorem. It uses the actual submodules
`cocycles₁` and `cocycles₂` and the actual differentials. The helper lemmas are
private to this module. Injectivity, quotient descent, and the assembled
inflation–restriction theorem are separate results.

## Quotient coordinates

`quotient_coordinates` chooses a representative `r(q)` for each `q ∈ G/S`
using `Quotient.out`. Put `π : G → G/S` for the quotient homomorphism and
`t(g) = g r(π(g))⁻¹`. Its quotient is the identity, so `t(g)` belongs to `S`.
The lemma proves

`π(r(q)) = q`, `t(g) r(π(g)) = g`, and `t(sg) = s t(g)`.

No special representative is imposed for the identity coset. The only fact
needed about `r(1)` is its membership in `S`.

## Removing the subgroup boundary and the left mixed terms

In the final theorem, choose the given subgroup primitive `a : S → A` and extend
it to `e : G → A` by zero outside `S`. Define `c₀ = c - d₁₂ e`. Mathlib's
`d₁₂_apply_mem_cocycles₂` and the submodule operations make this an actual
two-cocycle. Its restriction to `S × S` is zero.

For any cocycle with this last property, `kill_left` defines

`b(g) = -c₀(t(g), r(π(g)))`.

It vanishes on `S`, since both coordinates then belong to `S`. The two-cocycle
identity at `(s, t(g), r(π(g)))` gives

`c₀(s t(g), r(π(g))) = ρ(s)c₀(t(g), r(π(g))) + c₀(s,g)`.

Together with the coordinate identities, this proves
`c₀(s,g) = d₁₂ b(s,g)`. Hence `c₁ = c₀ - d₁₂ b` is a two-cocycle with
`c₁(s,g) = 0` for all left mixed pairs.

## Removing the right mixed terms

`left_zero_equivariance` applies the two-cocycle identity at `(s,g,h)` to show

`c₁(sg,h) = ρ(s)c₁(g,h)`.

For a fixed `g`, `conjugate_primitive` constructs the actual subgroup one-cocycle

`z_g(s) = c₁(g, g⁻¹ s g)`.

Normality ensures the conjugates lie in `S`. Applying the two-cocycle identity
at `(g, g⁻¹ s g, g⁻¹ t g)`, followed by left equivariance, proves
`z_g(st) = ρ(s)z_g(t) + z_g(s)`. The subgroup H¹ hypothesis makes its class
`H1π z_g` zero. Mathlib's `H1π_eq_zero_iff` then provides a primitive `x` with
`z_g(s) = ρ(s)x - x`. This extraction is the step supplied by Worker 138.

`kill_right` chooses such a primitive `x_q` for each representative `r(q)`.
Because `r(1)` lies in `S`, its conjugate one-cocycle is zero. Consequently
`ρ(s)x_1 = x_1` for all `s ∈ S`. Define

`d(g) = -ρ(t(g))x_{π(g)} + x_1`.

The constant term ensures `d(s) = 0` even though neither the identity-coset
representative nor its chosen primitive is normalized. It also gives
`d(sg) = ρ(s)d(g)`. Thus `d₁₂ d(s,g) = 0`.

For the right mixed pairs put `v = r(π(g)) s r(π(g))⁻¹ ∈ S`. The coordinates
satisfy `π(gs) = π(g)` and `t(gs) = t(g)v`. The chosen primitive and left
equivariance imply

`c₁(g,s) = ρ(t(g))(ρ(v)x_{π(g)} - x_{π(g)})`.

Expanding `d₁₂ d(g,s)` gives this same expression; the two constant terms
cancel. Hence `c₁(g,s) = d₁₂ d(g,s)` while the left mixed boundaries remain zero.

## Assembly and provenance

The final one-cochain is `B = e + b + d`. Linearity of `d₁₂` combines the three
steps and proves both required equalities simultaneously. All cocycle
identities above use Mathlib's `mem_cocycles₂_iff`, whose convention is

`c(gh,j) + c(g,h) = ρ(g)c(h,j) + c(g,hj)`.

This is an internal derived normal-form lemma supporting the degree-two case of
Jean-Pierre Serre, *Local Fields* (1979), VII.6, Proposition 5, printed
pages 117–118 / PDF pages 123–124. The registered original is
`serre-1979-local-fields`, retained at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Worker 10 read these pages and verified that fingerprint. No project errata
entry for this source was present. Serre states inflation–restriction under
subgroup cohomology vanishing and proves it by dimension shifting. The present
normal form is not a separately stated theorem in that source, and the
implemented proof is the explicit-cochain argument explained here.
