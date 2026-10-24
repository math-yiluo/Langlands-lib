# Complete filtrations and cohomological triviality

Author: Worker 226.

This module proves an abstract successive-approximation principle for multiplicative
group cohomology in degrees one and two. It also gives explicit cochains that make
coinduced modules satisfy the approximation hypothesis modulo a subgroup.
`Langlands.ClassField.Global.LocalUnitLattice` uses both to find an open subgroup of the
units of a local field whose first and second cohomology vanish.

## Setting and conventions

`G` is a group acting on a commutative group `Γ` by `MulDistribMulAction`. The coboundaries
use Mathlib's conventions for `IsMulCoboundary₁` and `IsMulCoboundary₂`:

- `coboundary1 b g = g • b / b`;
- `coboundary2 x (g, h) = g • x h / x (g * h) * x g`.

Cocycles are Mathlib's `IsMulCocycle₁` (`f (g * h) = g • f h * f g`) and `IsMulCocycle₂`
(`f (g * h, j) * f (g, h) = g • f (h, j) * f (g, h * j)`). The module proves that both
coboundary maps are multiplicative (`coboundary1_mul`, `coboundary1_div`, `coboundary2_mul`,
`coboundary2_div`, `coboundary1_one`, `coboundary2_one`) and that coboundaries are cocycles
(`isMulCocycle₁_coboundary1`, `isMulCocycle₂_coboundary2`). It also proves that pointwise
quotients of cocycles are cocycles (`isMulCocycle₁_div`, `isMulCocycle₂_div`). The
commutative-group identities are proved by passing to `Additive Γ` and using `abel`.

## Complete filtrations

`IsCompleteFiltration G V`, for `V : ℕ → Subgroup Γ`, is a structure of three properties:

- `smul_mem`: every `V k` is stable under `G`;
- `eq_one`: the filtration is separated, i.e. an element of every `V k` is `1`;
- `exists_prod`: the filtration is complete in the following sense. For every sequence
  `b` with `b k ∈ V k`, there is `s` with `s / ∏_{i < k} b i ∈ V k` for every `k`.

The levels are not assumed to be decreasing; the proofs below do not need it.

`exists_coboundary1_eq` assumes approximation at each level. For every `k`, every
`1`-cocycle with values in `V k` must agree with `coboundary1 b` for some `b ∈ V k`, up to an
error in `V (k + 1)`. Under this hypothesis every `1`-cocycle `f` with values in `V 0` equals
`coboundary1 s` for some `s ∈ V 0`. In the proof, recursion on `k` (`Nat.rec` together with
`choose!`) produces cocycles `F k` with values in `V k` and elements `c k ∈ V k` such that
`F (k + 1) = F k / coboundary1 (c k)`. By induction, `F k = f / coboundary1 (∏_{i<k} c i)`.
Completeness gives `s`, and `f g / coboundary1 s g = F k g / coboundary1 (s / ∏_{i<k} c i) g`
lies in `V k` for every `k`, so it is `1` by separatedness. Finally `s ∈ V 0` is the
completeness condition at `k = 0`.

`exists_coboundary2_eq` is the same argument in degree two. The approximation hypothesis
supplies `1`-cochains `x : G → Γ` with values in `V k`, and completeness is applied
separately to each value `g`. The conclusion is a `1`-cochain `s` with values in `V 0` and
`coboundary2 s = f`.

## Coinduced modules modulo a subgroup

For an additive group `Y`, functions `φ : G → Y` carry the action
`(g • φ) ρ = φ (g⁻¹ * ρ)`. The two theorems are stated directly on functions, without an
action instance, and work modulo an additive subgroup `Y'`:

- `coinduced_approx₁`: if `a (g * h) ρ - a h (g⁻¹ * ρ) - a g ρ ∈ Y'` for all `g, h, ρ`, and
  all values of `a` lie in a subgroup `Y''`, then `x ρ = -a ρ ρ` has values in `Y''` and
  `a g ρ - (x (g⁻¹ * ρ) - x ρ) ∈ Y'`;
- `coinduced_approx₂`: if
  `a (g * h, j) ρ + a (g, h) ρ - a (h, j) (g⁻¹ * ρ) - a (g, h * j) ρ ∈ Y'`
  and all values lie in `Y''`, then `x g ρ = a (g, g⁻¹ * ρ) ρ` has values in `Y''` and
  `x h (g⁻¹ * ρ) - x (g * h) ρ + x g ρ - a (g, h) ρ ∈ Y'`.

Each error term is minus one instance of the hypothesis: at `(g, g⁻¹ * ρ, ρ)` in degree one,
and at `(g, h, h⁻¹ * (g⁻¹ * ρ), ρ)` in degree two.

## Provenance

This is internal, derived infrastructure. The module states no theorem from the
literature. It supports the proof of the local unit lemma in J. S. Milne, *Class Field
Theory* v4.03 (2020), source `milne-2020-class-field-theory`, PDF page = printed page + 9.
Chapter III, Lemma 2.4 (printed p.104, PDF p.113) constructs an open subgroup of `U_L`
with trivial cohomology through the exponential map. Its footnote refers to Serre's
proof for characteristic `p`, which uses the unit filtration instead; the successive
approximation above is that kind of argument. The vanishing of the cohomology of induced
modules is Milne II, Corollary 1.12 (printed p.62, PDF p.71). The explicit cochains above
give it directly for modules coinduced from the trivial subgroup, with the coefficients
reduced modulo `Y'` and the integrality subgroup `Y''` kept track of.
