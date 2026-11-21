# Solutions of `Ξ_main` are automorphic forms

Source: J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*,
J. Amer. Math. Soc. 37 (2024), 187–234 (literature id
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`): §7.2, the system `Ξ_main` and
Theorem 7.2, pp.211–212; §8.1, Lemma 8.1 and its proof, pp.221–222; §8.4, proof of Proposition
8.4, pp.223–224.

In the proof of Proposition 8.4, BL show that every solution of `Ξ_fnl(λ)` is an automorphic
form, using Lemma 8.1 with an equation (8.2a) for which `c_i(λ) ≠ 0`. The proof of Lemma 8.1
derives `𝔷`-finiteness from the finite dimensionality of a space of solutions of a system of the
form of §7.2, which is Theorem 7.2. This module **states** that step for the system `Ξ_main`
itself; nothing is proved here.

## The statement `Langlands.Global.LocalFinitenessSolutionAutomorphyStatement`

The setting is that of `UniformGrowthLocalFinitenessStatement` (module
`AdelicLocalFinitenessStatement`, BL Theorem 7.2), with the same binders:

- `G` connected reductive over a number field `F`, a maximal split torus `iT : T → G` and a
  generic cocharacter `ν`;
- group data `u`, `t`, `z` of `Ξ_main` (`IsLocalFinitenessGroupData`);
- a closed matrix embedding `rho` and the smooth structure `hsmooth`, `hcalc`;
- admissible analytic data `X : LocalFinitenessData` on an open set `W ⊆ ℂⁿ`
  (`X.IsAdmissible`).

Additional hypothesis: a subgroup `K_∞` of `G(𝔸_∞)` (`Kinf`) such that every test function
`h i k` of the Harish-Chandra equations of `X` is left `K_∞`-finite. This is written
`IsInfiniteSubgroupFiniteFunction F G Kinf (fun g => X.h i k g⁻¹)`: the right `K_∞`-translates
of `g ↦ h i k (g⁻¹)`, that is, the functions `g ↦ h i k (k⁻¹ g⁻¹)`, span a finite-dimensional
space.

Conclusion: for every compact open `L ≤ G(𝔸_f)`, every real `R`, every `s ∈ W` and every
solution `v` of `Ξ_main(s)` in `𝔉^R_L` (`X.solutions … R L s`, with `a α = iT(t α)` and central
elements `iT(z j)`), the underlying function of `v` is an automorphic form on `G(F) \ G(𝔸)`:
`IsAutomorphicFunctionOn` for `rationalSubgroup F G` and `K_∞`. This means left
`G(F)`-invariant, smooth, right `K_∞`-finite, `𝔷`-finite and of moderate growth.

## Why it is true (not formalized here)

- **Invariance, smoothness, growth.** Elements of `𝔉^R_L` are smooth functions on
  `G(F) \ G(𝔸)`, right `L`-invariant, of moderate growth with exponent `R`.
- **`K_∞`-finiteness.** By admissibility some `c i s ≠ 0`, so
  `f = c i s⁻¹ ∑_k b i k s · δ(h i k) f` for the function `f` of `v`. For `κ ∈ K_∞`,
  left invariance of Haar measure gives `δ(h) f (x κ) = δ(h(κ⁻¹ ·)) f (x)`. The functions
  `h i k (κ⁻¹ ·)` lie in a finite-dimensional space of compactly supported continuous
  functions, and `δ(·) f` is linear on it. So the right `K_∞`-translates of `f` span a
  finite-dimensional space. This is the argument of the proof of Lemma 8.1.
- **`𝔷`-finiteness.** The center `𝔷` of the enveloping algebra acts by right derivatives. It is
  invariant under `Ad G(F_∞)`, because `G(F ⊗ ℂ)` is connected. So it commutes with every
  `δ(h)`, with left translations and with constant terms, and it preserves `𝔉^R_L`. Hence the
  solution space of `Ξ_main(s)` in `𝔉^{R'}_L` is `𝔷`-stable for every `R'`. By Theorem 7.2
  (`UniformGrowthLocalFinitenessStatement`) it is finite-dimensional for `R'` large: a family
  of finite type has finite-dimensional fibres. Since `𝔉^R_L ⊆ 𝔉^{R'}_L` for `R ≤ R'`, `v`
  lies in such a finite-dimensional `𝔷`-stable space. The annihilator of that space is an ideal
  of finite codimension in `𝔷`.

The statement thus follows from BL Theorem 7.2 together with the elementary facts above. It is
stated separately so that the reduction proving `EisensteinSystemDominationStatement` need not
contain the analysis of convolution and of the center action.

## Use

This is one premise of the planned reduction proving `EisensteinSystemDominationStatement`.
The solutions of the system built there are solutions of `Ξ_main(s)` for data `X` whose test
functions are bi-`K`-finite (BL Lemma 8.3), so this statement gives their automorphy. Every
solution of `Ξ_main` at every parameter is covered, not only at regular parameters.
