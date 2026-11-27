# Uniform slice growth from uniformly moderate growth

Module `Langlands.Global.AdelicSliceGrowthEnveloping`, namespace `Langlands.Global.AdelicGroupPoints`.

## Declarations

- `envelopingWord hsmooth w`: for `w = [X₁, …, Xₖ]` the element
  `ι(1 ⊗ Xₖ) ⋯ ι(1 ⊗ X₁)` of `AdelicEnvelopingAlgebra F G hsmooth`, defined by `List.foldr`, with
  `envelopingWord_nil` and `envelopingWord_cons`.
- `plotSmoothEnvelopingAction_envelopingWord`: on plot-smooth functions on the infinite adelic
  points, `plotSmoothEnvelopingAction hcalc (envelopingWord w)` acts as `listDirectionalDerivative w`.
  Proof: induction on `w`; the action is an algebra homomorphism, and
  `plotSmoothEnvelopingAction_real_generator` identifies `ι(1 ⊗ X)` with
  `plotSmoothDifferential X`, whose underlying function is `groupDirectionalValue X`.
- `exists_hasUniformSliceGrowth`: if `φ` satisfies `IsAutomorphicFunctionOn F G hsmooth hcalc Γ Kinf rho φ`
  and `HasUniformModerateGrowthFunction F G rho hsmooth hcalc φ`, with `0 < N`, then there is
  `e ≥ 0` with `HasUniformSliceGrowth hsmooth Γ (adelicHeight F G rho) e φ`. Proof: smooth slices
  and left invariance are part of `IsAutomorphicFunctionOn` (`isPlotSmooth_iff_contMDiff`). For a
  list `v`, apply the uniform bound to `envelopingWord v`; with
  `adelicHeight = D · adelicSourceNorm` for `D = N ^ (∑ v, v.mult)` the bound
  `C · ‖g‖ ^ r` becomes `C D^{-r} · adelicHeight(g) ^ r`, and `adelicHeight ≥ 1` allows the exponent
  `max r 0`.

## Provenance

Internal: the passage from the enveloping-algebra form of uniform moderate growth
(Mœglin–Waldspurger, *Spectral decomposition and Eisenstein series* (1995), I.2.3, printed p. 25) to
bounds on iterated invariant derivatives.
