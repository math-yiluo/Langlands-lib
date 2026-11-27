# Uniformly moderate growth of automorphic functions on `Γ \ G(𝔸)`: proof

Module `Langlands.Automorphic.GroupSchemeAutomorphicFunctionUniformGrowthProof`. The theorem

```lean
theorem Langlands.Automorphic.GroupSchemeFunctions.automorphicFunctionUniformGrowth :
    AutomorphicFunctionUniformGrowthStatement.{u}
```

proves the published statement of the module
`Langlands.Automorphic.GroupSchemeAutomorphicFunctionUniformGrowthStatement`. Let `G` be a
connected reductive group over a number field, `Kinf` a maximal compact subgroup of the infinite
adelic points, `rho` a closed matrix representation of positive size `N` and `Γ` any subgroup of
`G(𝔸)`. Then every function `φ` on `G(𝔸)` with `IsAutomorphicFunctionOn F G hsmooth hcalc Γ Kinf
rho φ` satisfies `HasUniformModerateGrowthFunction F G rho hsmooth hcalc φ`. Lean reports the axioms
`propext`, `Classical.choice` and `Quot.sound`. The module declares no other public names.

## The proof

`IsAutomorphicFunctionOn` is the conjunction of left `Γ`-invariance, smoothness
(`IsAdelicSmoothFunction`, whose second component says that every infinite slice
`a ↦ φ(a, b)` is plot-smooth), `Kinf`-finiteness (`IsInfiniteSubgroupFiniteFunction`),
centre-finiteness (`IsCenterFiniteFunction`) and moderate growth (`HasModerateGrowthFunction`).
The last four are exactly the hypotheses of the Library's
`Langlands.Automorphic.GroupSchemeFunctions.exists_uniformGrowth_functionInfiniteSlices` (module
`Langlands.Automorphic.GroupSchemeInvariantFunctionGrowth`), together with `0 < N`, the connected
reductivity of `G` and the maximality of `Kinf`. Left invariance is not used, so the argument holds
for every subgroup `Γ`.

That theorem gives an exponent `e ≥ 0`, chosen before the enveloping element, such that for every
element `a` of the complex enveloping algebra there is `C ≥ 0` with

`‖(a · φ(·, b))(x)‖ ≤ C · ‖(x, b)‖_ht ^ e`

for all finite points `b` and infinite points `x`, where `‖·‖_ht` is the adelic height
`RepresentationGrowth.adelicHeight` of `rho`. The proof keeps `e` and, for a given `a`, takes
the constant `(C + 1) · s ^ e`, where `s = N ^ (∑_v mult v) > 0`. It is positive. By
`RepresentationGrowth.adelicHeight_eq_scalar_mul_sourceNorm` the height is `s` times the adelic
source norm, and the source norm is positive for `N > 0`
(`RepresentationGrowth.adelicSourceNorm_pos`). So `‖(x, b)‖_ht ^ e = s ^ e · ‖(x, b)‖ ^ e`
(`Real.mul_rpow`), and the bound above is at most `(C + 1) · s ^ e · ‖(x, b)‖ ^ e`, the bound
required by `HasUniformModerateGrowthFunction` with the adelic source norm. The plot-smoothness
proof `h` of the slice supplied in `HasUniformModerateGrowthFunction` and the one from
`IsAdelicSmoothFunction` give the same element of `InfinitePlotSmoothFunctions F G`, by proof
irrelevance.

## Provenance

The statement is Mœglin–Waldspurger, *Spectral decomposition and Eisenstein series* (1995),
I.2.17, printed pp. 37–39: automorphic forms on `U(𝔸)M(k) \ G` and their derivatives have
moderate growth, in the uniform sense of I.2.3, printed p. 25, with one exponent for all elements
of the enveloping algebra. Mœglin–Waldspurger deduce this from Harish-Chandra's reproducing function
(p. 38) and the convolution estimate of I.2.5, Lemma (a), printed p. 27. The implemented route is
the elliptic one of `exists_uniformGrowth_functionInfiniteSlices`. A polynomial equation in an
adapted Casimir element, coming from `Kinf`-finiteness and centre-finiteness, gives an interior
elliptic estimate of all derivatives by the size of the function on a fixed compact neighbourhood.
This module only converts that estimate from the adelic height to the adelic source norm used in
the statement.
