# Constant terms of automorphic functions along nested parabolic subgroups

Module `Langlands.Global.AdelicParabolicConstantTermAutomorphy` states and proves
`Langlands.Global.ParabolicConstantTermAutomorphyStatement` (universe `u`): the constant term of
an automorphic function along the unipotent radical of a subgroup `P'` is automorphic on
`U'(𝔸)M'(F) \ G(𝔸)`. The proof is `Langlands.Global.parabolicConstantTermAutomorphy`.

## Statement

Let `F` be a number field and `G` an affine group scheme over `Spec F`, locally of finite type.
Let `p' : P' → G` and `l' : M' → P'` be homomorphisms of group schemes and `iU' : U' → P'` a
geometric unipotent radical (`LeviSubgroup.IsGeometricUnipotentRadical iU'`), with `U'` affine and
`iU' ≫ p'` a closed immersion. Fix a matrix representation `rho : G → GL_N`, a smooth structure
`hsmooth : SmoothOfRelativeDimension d G.X.hom` with its commutator datum `hcalc`, a subgroup
`Γ` of `G(𝔸)` and a subgroup `Kinf` of `G(F_∞)`. If

- `Γ` contains the rational points `P'(F)` (`rationalImage F p' ≤ Γ`), and
- `φ : G(𝔸) → ℂ` is automorphic on `Γ \ G(𝔸)`
  (`IsAutomorphicFunctionOn F G hsmooth hcalc Γ Kinf rho φ`: left invariance under `Γ`,
  smoothness, finiteness under right translation by `Kinf`, annihilation of all infinite slices
  by one ideal of finite codimension of the center `𝔷` of the enveloping algebra, and moderate
  growth for the adelic norm of `rho`),

then the constant term

\[
  C_{U'}\varphi(g) = \int_{U'(F)\backslash U'(\mathbb A)} \varphi(u g)\,du
\]

(`subgroupConstantTerm F (iU' ≫ p') φ`, for the normalized quotient measure) is automorphic on
`U'(𝔸)M'(F) \ G(𝔸)`: `IsAutomorphicFunctionOn F G hsmooth hcalc
(parabolicQuotientSubgroup F p' iU' l') Kinf rho (subgroupConstantTerm F (iU' ≫ p') φ)`.

The theorem `IsAutomorphicFunctionOn.subgroupConstantTerm_of_range_le` is the nested case: for
`p : P → G` with a rational Levi subgroup `l : M → P` and a geometric unipotent radical
`iU : U → P`, and `SubgroupFunctor.range p' ≤ SubgroupFunctor.range p`, an automorphic function
on `U(𝔸)M(F) \ G(𝔸)` has automorphic constant term on `U'(𝔸)M'(F) \ G(𝔸)`. Here
`P'(F) ⊆ P(F) ⊆ U(𝔸)M(F)` by `rationalImage_le_of_range_le` and
`rationalImage_le_parabolicQuotientSubgroup`.

## Sources

- C. Mœglin and J.-L. Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995),
  chapter file `05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`:
  - I.2.6, printed p. 27 (PDF p. 10): for a standard parabolic `P = MU` and `φ` on `U(k)\G`,
    `φ_P(g) = ∫_{U(k)\U(𝔸)} φ(ug) du`; if `φ` is left invariant under `G(k)`, has moderate
    growth, or is smooth, then `φ_P` is left invariant under `M(k)`, has moderate growth, or is
    smooth, respectively.
  - I.2.17, printed pp. 37–38 (PDF pp. 20–21): a function on `U(𝔸)M(k)\G` is automorphic if it
    has moderate growth, is smooth, `K`-finite and `𝔷`-finite.
- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
  Math. Soc. 37 (2024), §6.2, p. 201: for `Q ⊂ P` the constant term
  `C_{P,Q}φ(g) = ∫_{U_Q(F)\U_Q(𝔸)} φ(ug) du` defines a linear map `𝒜_P → 𝒜_Q`.

## Correspondence and scope

For `Γ = U(𝔸)M(F)` and `P' ⊆ P` the statement is the assertion of Bernstein–Lapid that
`C_{P,P'}` maps automorphic forms on `U(𝔸)M(F) \ G(𝔸)` to automorphic forms on
`U'(𝔸)M'(F) \ G(𝔸)`, for parabolics that need not be standard. Mœglin–Waldspurger I.2.6 treats
functions left invariant under `G(k)`; the proof uses only the invariance under `P'(F)`, which is
why the hypothesis is `P'(F) ⊆ Γ`. The homomorphism `l'` enters only through `M'(F)`, which is
contained in `P'(F)`; no Levi condition on `l'` is needed. The sources use the infinite part
`K_∞` of a fixed maximal compact subgroup; finiteness under right translation by any subgroup
`Kinf` passes to the constant term, so `Kinf` is arbitrary. The proof also shows that the
annihilating ideal of `𝔷` and the open subgroup of `G(𝔸_f)` fixing `φ` can be kept for the
constant term.

## Proof

Write `j = iU' ≫ p'`. Since `U'` is smooth, connected and unipotent, `U'(F) \ U'(𝔸)` is compact
(`compactSpace_rationalQuotient_range_unipotent`) and carries the normalized probability measure.

**Linearity.** `integrable_subgroupConstantTermIntegrand`: for a continuous function invariant
under `U'(F)`, the representative-based integrand descends to a continuous function on the
compact quotient, hence is integrable. This gives `subgroupConstantTerm_add` on such functions;
`subgroupConstantTerm_smul`, `subgroupConstantTerm_zero` and
`subgroupConstantTerm_rightTranslate` (the constant term commutes with right translation) hold
for all functions.

**Invariance and continuity.** `inducingConstantTermCovariance p' iU'` applies to the continuous
function `φ`, which is left invariant under `P'(F) ⊆ Γ`: the constant term is continuous and left
invariant under `P'(F)` and under `U'(𝔸)`. `M'(F)` lies in `P'(F)` (`rationalImage_comp_le`), and
invariance under `U'(𝔸)` and `M'(F)` gives invariance under the subgroup
`parabolicQuotientSubgroup F p' iU' l'` they generate (`IsLeftInvariantUnder.sup`).

**Smoothness.** `IsUnipotentAverageRegular j L f` collects continuity, plot-smoothness of all
infinite slices, left invariance under `U'(F)` and right invariance under `L ⊆ G(𝔸_f)`. For `L`
the open level of `φ`, `φ` is regular. `adelicUnipotentConstantTermDifferentiation` shows that
the infinite slices of the constant term of a regular function are smooth
(`IsUnipotentAverageRegular.subgroupConstantTerm_slice_mem`, through `isPlotSmooth_iff_contMDiff`)
and that the derivative of the slice `y ↦ C_{U'}f(y, b)` in an archimedean direction `X` is the
slice of the constant term of the adelic derivative `adelicDirectionalValue hsmooth X f`, which
is again regular. Right invariance under `L` passes to the constant term since the constant term
commutes with right translation.

**`Kinf`-finiteness.** The continuous `U'(F)`-invariant functions form a submodule containing the
right translates of `φ` by `Kinf`, on which the constant term is linear. The right translates of
the constant term are the constant terms of the right translates of `φ`, so their span lies in the
image of the finite-dimensional span of the translates of `φ` under this linear map.

**`𝔷`-finiteness.** `exists_unipotentAverage_envelopingLift`: for every element `D` of the
complex enveloping algebra and every regular `f` there is a regular `f'` whose infinite slices are
the images under `D` of those of `f`, and such that `D` maps each infinite slice of `C_{U'}f` to the
corresponding slice of `C_{U'}f'`. The proof writes `D` as the image of an element of the tensor
algebra (`RingCon.mkₐ_surjective`) and inducts on it: scalars act by scalar multiplication,
products by composition and sums by addition (using linearity of the constant term on regular
functions); a generator `z ⊗ X` of the complexified Lie algebra acts by `z` times the directional
derivative, where the differentiation step above applies. For `z` in the ideal `J` annihilating
the slices of `φ`, the function `f'` attached to `φ` has zero slices, hence is zero, so `z`
annihilates every slice of `C_{U'}φ`
(`IsUnipotentAverageRegular.centerAction_subgroupConstantTerm_eq_zero`). The same ideal `J`
therefore works for the constant term.

**Moderate growth.** `HasModerateGrowthFunction.subgroupConstantTerm`. For `N > 0` the
moderate-growth condition is a bound by a power `r ≥ 0` of the submultiplicative adelic height
(`hasModerateGrowthFunction_iff_hasHeightGrowth`). Every class of the compact quotient has a
representative of height at most a constant `B` (`exists_le_of_compactSpace_leftCosetSpace`);
representatives differ by points of `U'(F)`, which fix `φ`. The integrand is then bounded by
`C B^r H(g)^r` and the measure is a probability. For `N = 0` the adelic norm is constant and the
bound of `φ` passes directly to the average.
