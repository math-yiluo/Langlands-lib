# Principal generation-open lifting on qcqs schemes

`Langlands.SchemeModule.principalGenerationOpenLift` proves exactly the published
`Langlands.SchemeModule.PrincipalGenerationOpenLiftStatement.{u}` in arbitrary
universe `u`. Import it from
`Langlands.AlgebraicGeometry.Modules.PrincipalGenerationOpenLiftProof`.

For every quasi-compact quasi-separated scheme `X`, actual line bundle `M`,
global section `s` of `M.obj`, and regular function `r` on the whole generation
open `U := trivializationOpen M.obj s`, there are `k ≥ 1` and a global section
`t` of `tensorPow M.obj k` with

```text
trivializationOpen (tensorPow M.obj k) t = X.basicOpen r.
```

The only assumptions on `X` are `CompactSpace X` and `QuasiSeparatedSpace X`.
There are no nonzero or nonempty assumptions on `X`, `U`, `s`, or `r`. Tensor
powers are the published right-associated powers with trailing structure-sheaf
factor: the zeroth power is `structureSheaf X`, and power `n + 1` is
`tensorObj M.obj (tensorPow M.obj n)`. Both sides of the equality are whole opens
of the ambient scheme `X`.

## A scalar multiple of a frame

The helper `inf_trivializationOpen_eq_basicOpen_of_res_eq_smul` applies to any
module sheaf `N`, global sections `q` and `a`, and an open `U` on which `q`
trivializes `N`. If `a|_U = r • q|_U`, it proves

```text
U ⊓ trivializationOpen N a = X.basicOpen r.
```

First, restricting the given equality to any `V ≤ U` gives
`a|_V = r|_V • q|_V`, by composition of restrictions and `map_smul`.

For the forward inclusion take `V := U ⊓ trivializationOpen N a`. Both section
morphisms are bijective on sections over `V`, by
`trivializesOn_iff_bijective` and `maximalTrivialization`. Surjectivity for `a`
gives a function `d` with `d • a|_V = q|_V`. Injectivity for `q`, together with
`sectionHom_app_of_eq_smul`, then gives `d * r|_V = 1`. Thus `r|_V` is a unit,
and `X.basicOpen (r|_V) = V`. The basic-open restriction identity rewrites this
as `V ⊓ X.basicOpen r = V`, proving the inclusion.

Conversely, `X.basicOpen r ≤ U`, so `q` trivializes on that basic open. The
restriction of `r` there is a unit (`isUnit_res_basicOpen`). The equality of
restricted sections and `trivializesOn_of_eq_smul` show that `a` also
trivializes there. Maximality of `trivializationOpen N a` gives the reverse
inclusion. This calculation requires no line-bundle or qcqs hypothesis.

## Power sections and the extra tensor factor

`trivializesOn_sectionPow_generationOpen` proves that for every `n ≥ 0`,
`sectionPow M.obj s n` trivializes `tensorPow M.obj n` on `U`. At `n = 0`, the
published theorem `trivializationOpen_sectionPow_zero` says that the unit
section generates everywhere. For successor exponents,
`trivializationOpen_sectionPow_succ` identifies the whole generation open with
`U`. In both cases `maximalTrivialization` yields the stated restriction.

`principalGenerationOpenLift_of_clearedSection` assumes a global section `a`
of `tensorPow M.obj n` with

```text
a|_U = r • (sectionPow M.obj s n)|_U.
```

It sets `k := n + 1` and
`t := tensorSection M.obj (tensorPow M.obj n) s a`. This has the actual target
`tensorPow M.obj (n + 1)` by its right-associated successor definition; no
change of tensor convention or tensor-power comparison is used. The inequality
`1 ≤ n + 1` is `Nat.succ_le_succ (Nat.zero_le n)`.

The tensor power is a line bundle by `tensorPow_isLocallyFreeRankOne`.
`tensorSectionGenerationLocus` identifies the whole generation open of `t` with
`U ⊓ trivializationOpen (tensorPow M.obj n) a`. The scalar-frame lemma above,
using `q := sectionPow M.obj s n`, identifies this intersection with
`X.basicOpen r`. The extra factor `s` ensures that the resulting generation
open is contained in `U`, including when `n = 0`.

## Unconditional assembly

The final theorem invokes the published unconditional
`Langlands.SchemeModule.lineBundleSectionClearing` from
`Langlands.AlgebraicGeometry.Modules.LineBundleSectionClearingProof`. On the
qcqs scheme this provides precisely `n`, `a`, and the restriction equality
needed by `principalGenerationOpenLift_of_clearedSection`. All auxiliary
premises are thereby discharged. No localization, extension, comparison,
quasi-coherence, or ampleness premise remains in the theorem's type. Neither
final theorem of the parent ampleness task is used.

The proof and all helpers use only the standard axioms `propext`,
`Classical.choice`, and `Quot.sound`.

## Provenance

This is an internal derived consequence of the scalar specialization of
Stacks Project, *Properties of Schemes*, Lemma 28.18.2(2), tag
[01PW](https://stacks.math.columbia.edu/tag/01PW), and the Library's tensor and
maximal-generation-locus theorems. The retained original is `01PW.html` in the
registered source `stacks-section-open-prerequisites-2026-10-29`, SHA256
`60bc1435a16d7d9ad4d4ef9cc426dbe4a992c7cb421f14fb5e5989fbfe06475c`.
The source's concluding localization isomorphism supplies the scalar clearing
step, already proved in `LineBundleSectionClearingProof`. Its proof implements
the corrected common-exponent argument recorded in comments #4719 and #4809.
The present proof implements the subsequent locus calculation and final
multiplication described in the published target's paired Markdown; it does
not assert the source's general quasi-coherent localization isomorphism.

Worker 311 supplied the componentwise scalar-frame argument and tensor
assembly; Worker 5 instantiated that assembly with the published clearing
theorem and prepared the final proof and explanation.
