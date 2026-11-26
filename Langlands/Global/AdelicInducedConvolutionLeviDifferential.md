# Levi differential annihilators of induced convolution

`Langlands.Global.AdelicGroupPoints.InducedConvolutionLeviAnnihilatorStatement` transfers a Levi
enveloping annihilator through the integrated induced action. For a smooth adelic function `v`,
`infiniteLeviSlice p l v g` is the function `m ↦ v(l(m)g)`, with the archimedean Levi mapped into
the ambient adeles through `p ∘ l`. If a Levi enveloping operator kills every such slice of `v`,
then it kills each smooth infinite Levi slice of `hK.inducedConvolution λ φ v`, for every `λ` and
every continuous compactly supported `φ`.

## Implemented proof

The Iwasawa height satisfies `H_P(ay) = H_P(a) + H_P(y)` for `a` in the parabolic. In the
exponential twist at `l(m)g`, the two occurrences of `H_P(l(m))` cancel. The resulting weight
`φ(h) exp(⟨λ, H_P(gh) − H_P(g)⟩)` depends on the integration point `h`. Restrict Haar measure to
the compact support of `φ` and integrate the input slices `m ↦ v(l(m)gh)` there with this weight.

To apply `compactKernelEnvelopingAction`, use the infinite coordinate of `gh` and the class of
its finite coordinate in the discrete right quotient by the input's open level. Evaluating `v`
using a representative of that class gives the same value by right invariance. The resulting
kernel is jointly smooth in `m` and the infinite coordinate by smoothness of the Levi inclusion,
group multiplication and the infinite slices of `v`. The class is locally constant. The compact
integration theorem moves the operator inside the integral, where it kills the input slice at
each `gh` by the hypothesis. Hence the differentiated output slice vanishes identically.

## Provenance

This is an internal consequence of the Iwasawa height law, the Library's induced action and
`compactKernelEnvelopingAction`. The same induced-action formula appears in J. Arthur, *An
introduction to the trace formula*, §7, printed p. 33 (PDF p. 45), volume registered as
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, SHA-256
`88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`.
