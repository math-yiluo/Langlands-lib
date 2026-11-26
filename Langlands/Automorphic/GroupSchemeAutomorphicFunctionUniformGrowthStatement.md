# Uniformly moderate growth of automorphic functions on `Γ \ G(𝔸)`

Module `Langlands.Automorphic.GroupSchemeAutomorphicFunctionUniformGrowthStatement` contains two
`Prop`-valued definitions in the namespace `Langlands.Automorphic.GroupSchemeFunctions` and no
theorems. It states the second one and does not prove it.

## `HasUniformModerateGrowthFunction`

`HasUniformModerateGrowthFunction F G rho hsmooth hcalc φ` is a predicate on a plain function
`φ : AdelicGroupPoints F G → ℂ`, for a number field `F`, an affine group scheme `G` over
`Spec F`, a matrix representation `rho : MatrixRepresentation G (Fin N)`, the smooth structure
`hsmooth : SmoothOfRelativeDimension d G.X.hom` and `hcalc : AdelicDifferentialCommutator F G
hsmooth`. It holds when there is a real `r` such that for every element `a` of
`AdelicEnvelopingAlgebra F G hsmooth` (the universal enveloping algebra of the complexified Lie
algebra of the infinite adelic points) there is `C > 0` with

```
‖(plotSmoothEnvelopingAction F G hsmooth hcalc a ⟨functionInfiniteSlice F G φ b, h⟩) x‖
  ≤ C * adelicSourceNorm F G rho (pair F G x b) ^ r
```

for every finite adelic point `b`, every proof `h` that the infinite slice
`functionInfiniteSlice F G φ b` (the function `x ↦ φ(x, b)`) lies in
`InfinitePlotSmoothFunctions F G`, and every infinite adelic point `x`. The derivative is the
Library's enveloping action on plot-smooth slices (module
`Langlands.Automorphic.GroupSchemeEnvelopingAction`), the same action through which
`IsCenterFiniteFunction` lets the centre act. `adelicSourceNorm F G rho` is the adelic norm
`‖g‖` of `HasModerateGrowthFunction`. The exponent `r` is chosen before `a`; the constant `C`
depends on `a`. Slices that are not plot-smooth impose no condition.

This is the quantifier order of Mœglin–Waldspurger I.2.3 for "`φ` and its derivatives have
uniformly moderate growth", and of the Library's `HasAdelicUniformModerateGrowth` (module
`Langlands.Automorphic.GroupSchemeAdelicUniformGrowth`), which is the same condition on the
carrier `FinitePlotSmoothRationalFunctions F G`.

## `AutomorphicFunctionUniformGrowthStatement`

`AutomorphicFunctionUniformGrowthStatement.{u}` quantifies over a number field `F : Type u`, an
affine group scheme `G` over `Spec F`, an arbitrary subgroup `Γ` of `AdelicGroupPoints F G`, a
subgroup `Kinf` of `InfiniteAdelicGroupPoints F G`, a matrix representation `rho` of size `N`, and
`hsmooth`, `hcalc`. Under the hypotheses

- `IsConnectedReductive G`,
- `IsClosedSubgroup rho`,
- `CompactIwasawa.IsMaximalCompact Kinf` (compact and contained in no larger compact subgroup),
- `0 < N`,

it asserts that every `φ` with `IsAutomorphicFunctionOn F G hsmooth hcalc Γ Kinf rho φ` satisfies
`HasUniformModerateGrowthFunction F G rho hsmooth hcalc φ`. `IsAutomorphicFunctionOn` (module
`Langlands.Automorphic.GroupSchemeInvariantForms`) requires left invariance under `Γ`,
continuity, plot-smooth infinite slices, invariance under an open subgroup of the finite adelic
points, finiteness under right translation by `Kinf`, annihilation of all slices by one ideal of
finite codimension in the centre of the enveloping algebra, and moderate growth for `rho`.

For `Γ = parabolicQuotientSubgroup F p iU l`, the subgroup `U(𝔸) M(F)`, these are the
automorphic forms on `U(𝔸) M(F) \ G(𝔸)`. The hypotheses are those of the Library's
`AdelicAutomorphicUniformGrowthStatement` (module
`Langlands.Automorphic.GroupSchemeAutomorphicUniformGrowthStatement`, proved as
`adelicAutomorphicUniformGrowth`), with the carrier of rational finite plot-smooth functions
replaced by plain functions left invariant under an arbitrary `Γ`, and with an arbitrary `hcalc`.

## Sources

C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series*, Cambridge
University Press, 1995, registered as `moeglin-waldspurger-1995-spectral-decomposition`, chapter
file `05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf` (printed page = PDF page + 17):

- I.2.3, printed p. 25: "`φ` and its derivatives have uniformly moderate growth if
  `∃ r ∈ ℝ, ∀ X ∈ 𝒰, ∃ c_X ∈ ℝ, ∀ g ∈ G, |δ(X)φ(g)| ≤ c_X ‖g‖^r`".
- I.2.5, Lemma (a), printed p. 27: for `f` smooth with compact support and `φ : G(k) \ G → ℂ` of
  moderate growth, `δ(f)φ` has moderate growth and, if `k` is a number field, `δ(f)φ` and its
  derivatives have uniformly moderate growth. The printed proof integrates over `G(k) \ G`, sums
  the translated kernel over `G(k)` and uses the counting estimate I.2.4 (b)(i).
- I.2.17, printed pp. 37–39: automorphic forms on `U(𝔸)M(k) \ G` (moderate growth, smoothness,
  `K`-finiteness, `𝔷`-finiteness). After the lemma citing Harish-Chandra (a smooth compactly
  supported `f` with `δ(f)φ = φ` for `φ` in a finite-dimensional space of such forms, printed
  p. 38) the text concludes (printed pp. 38–39): "The preceding lemma and Lemma I.2.5 show that
  for all `P` and all `φ ∈ A(U(𝔸)M(k)\G)`, `φ` and its derivatives have moderate growth", in the
  uniform sense of Lemma I.2.5 (a).

## Provenance

The statement is derived from Mœglin–Waldspurger I.2.17 with I.2.3 and I.2.5. The source states
it for a standard parabolic `P = MU` and `Γ = U(𝔸)M(k)`, and its Lemma I.2.5 (a) is stated and
proved for functions on the rational quotient `G(k) \ G`. The statement here allows an arbitrary
left subgroup `Γ` and plain functions on `G(𝔸)`. This extension rests on two observations, neither
of which uses left invariance.

- The derivative estimate for a convolution holds on the whole group. For `f` smooth with compact
  support `S` and `δ(f)φ(x) = ∫_G f(y) φ(xy) dy`, every enveloping derivative of `δ(f)φ` is again a
  convolution of `φ` with a test kernel supported in `S` (in the Library:
  `Langlands.Global.AdelicGroupPoints.adelicRightConvolutionEnveloping`). The source norm `ν = adelicSourceNorm`
  is submultiplicative only up to a constant: with `D = N ^ (∑ v, v.mult)`, the scaled height
  `adelicHeight = D ν` satisfies `adelicHeight (xy) ≤ adelicHeight x · adelicHeight y`
  (`adelicHeight_eq_scalar_mul_sourceNorm`, `adelicHeight_mul_le`), so `ν(xy) ≤ D ν(x) ν(y)`.
  If `|φ(z)| ≤ c ν(z)^e` with `e ≥ 0`, then `|φ(xy)| ≤ c D^e ν(x)^e ν(y)^e`, with `ν(y)` bounded on
  `S`. So all these convolutions are bounded by constants, depending on the derivative, times
  `ν(x)^e` with the same exponent `e`.
- The reproducing identity `δ(f)φ = φ` of Harish-Chandra, quoted on printed p. 38, concerns
  `K`-finite, `𝔷`-finite smooth functions and is local on the group; it does not use the left
  invariance of `φ`.

An alternative route is the one implemented in the Library for the rational carrier
(module `Langlands.Automorphic.GroupSchemeAutomorphicUniformGrowthReductionProof`): a
`Kinf`-finite, centre-finite function is annihilated by a monic polynomial in an elliptic element
of the enveloping algebra, and an interior elliptic estimate bounds every derivative at a point by
the supremum of the function on a fixed compact neighbourhood of that point. These steps apply to
a left translate of each infinite slice and use only the moderate-growth bound of the function, so
they do not use rationality or left invariance either.

Derivatives are taken slice by slice in the infinite variable, through the Library's enveloping
action on plot-smooth functions on the infinite adelic points; this is the action of `𝒰` by right
differentiation used in the source.
