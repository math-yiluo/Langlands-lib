# The Eisenstein analytic system from local finiteness and domination

This module defines the proposition

```
EisensteinAnalyticSystemReductionStatement : Prop :=
  UniformGrowthLocalFinitenessStatement.{u} →
  EisensteinSystemDominationStatement.{u} →
  EisensteinAnalyticSystemStatement.{u}
```

and proves it: `eisensteinAnalyticSystem_of_localFiniteness_of_domination hLF hD` is the
conditional proof, and `eisensteinAnalyticSystemReduction` packages it as a proof of
`EisensteinAnalyticSystemReductionStatement`. The form (a Prop-valued implication together with
a theorem proving it) follows the Library's reductions such as `EqualEulerGaugeReduction`.

It is a conditional proof; it does not establish either premise:

- `UniformGrowthLocalFinitenessStatement` is Bernstein–Lapid, Theorem 7.2, in Fréchet form;
- `EisensteinSystemDominationStatement` is Bernstein–Lapid, Proposition 8.4 with Lemma 8.1, with
  the domination of `Ξ_fnl` by a system `Ξ_main` made explicit.

The theorem is the step of BL §8.4 that combines the two ("we may apply Theorem 7.2"; journal
p.224, last paragraph of the proof of Proposition 8.4). The Fréchet form needs one extra
argument, a compactness argument that produces a single exponent `R` for the whole bounded
parameter set.

## The proof

1. `SmoothOfRelativeDimension d G.X.hom` gives `Smooth G.X.hom` (Mathlib's
   `SmoothOfRelativeDimension.smooth`), hence `LocallyOfFiniteType G.X.hom` by instances. This
   is the extra instance hypothesis of the domination statement.
2. The domination statement gives `R₀`. For given `n`, `e` and bounded open `W` it also gives:
   - group data `u`, `t`, `z` for a maximal split torus `iT` and a generic cocharacter `ν`;
   - admissible data `X` of `Ξ_main` on `⊤ = ℂⁿ`;
   - a compact open `L` and `R₁`;
   - for every `R ≥ R₁`, an analytic system on `𝔉^R_L` over `W` with the required properties.
3. Theorem 7.2, applied to `X` at every point `i` of `⊤`, gives an open neighbourhood `V i` and an
   exponent `R' i` such that the solutions of `Ξ_main` in `𝔉^R_L` are of finite type on `V i` for
   all `R ≥ R' i`.
4. The closure of `W` is compact (`Bornology.IsBounded.isCompact_closure`). The images of the
   `V i` in `ℂⁿ` are open (the inclusion of `⊤` is an open embedding) and cover it. So finitely
   many of them, indexed by a finset `fin`, cover the closure (`IsCompact.elim_finite_subcover`).
5. Put `R = |R₁| + ∑_{i ∈ fin} |R' i|`. Then `R ≥ R₁` and `R ≥ R' i` for every `i ∈ fin`. The
   domination statement at this `R` gives the system `eqn`, `c`. It is analytic, its solutions
   are unique (and equal to the Eisenstein series) at `R₀`-regular points, and they are
   automorphic. These are three of the four conclusions of `EisensteinAnalyticSystemStatement`,
   with the open subgroup `L`.
6. Local finite type. Take `s₀ ∈ W`. It lies in the closure of `W`, hence in the image of some
   `V i` with `i ∈ fin`. Let `incl : W → ⊤` be the inclusion of opens; it is smooth
   (`contMDiff_inclusion`), hence continuous and holomorphic. On the open set `incl⁻¹(V i)`, which
   contains `s₀`, take the holomorphic family `ℓ (incl s)` given by Theorem 7.2 at `R ≥ R' i`.
   Every solution of the system at `s` is a solution of `Ξ_main(incl s)` (domination), hence in
   the range of `ℓ (incl s)`. Holomorphy of the composite is `MDifferentiableOn.comp` with the
   differentiable inclusion. Injectivity is unchanged.

The proof uses only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
