# Separate center and compact differential finiteness imply joint finiteness

Author: Worker 88. Module:
`Langlands.Global.ArchimedeanSeparateJointFiniteProof`.
The theorem `Langlands.Global.ArchimedeanGL.separateJointFinite` proves the
whole published proposition
`Langlands.Global.ArchimedeanGL.SeparateJointFiniteStatement K n`.
It applies to every number field `K : Type u` and every natural rank `n`,
including zero, with no additional hypotheses.

## Implemented proof

Fix the actual smooth function `f` satisfying `IsCenterFinite K n f` and
`IsCompactLieFinite K n f`. Write `V` for its center orbit span. Finite
dimensionality of the compact orbit span implies finite generation.
`Submodule.fg_span_iff_fg_span_finset_subset` chooses a finite set `s` of
actual compact translates whose span is that compact orbit span. For each
`i` in `s`, choose a compact enveloping element `b i` with
`compactEnvelopingAction (b i) f = i`.

Let `S` be the finite supremum of the images of `V` under the linear maps
`compactEnvelopingAction (b i)`. Each image is finite-dimensional because
`V` is, and their finite supremum is therefore finite-dimensional.
For each central element `z`, its action sends every generator `i` of
`s` into `S`: multiplicativity of the actual enveloping action and
`centerInclusion_commute` give

```text
z (b i f) = b i (z f).
```

The latter vector lies in the `i`th image of `V`. By linearity, the center
action sends the entire span of `s` into `S`; Lean expresses this as
containment in the inverse image submodule `S.comap (centerAction z)`.
In particular, every joint translate `z (c f)` lies in `S`. Taking its
linear span proves that the joint orbit span is a subspace of `S`, hence
finite-dimensional. The argument also covers an empty generating set.

## Provenance and scope

This is an internal algebraic proof of the published target using its
actual complex orbit spans, actual enveloping action, and actual central
commutation. It implements the finite-image argument proposed in the
statement's companion Markdown. The original literature motivation and
its analytic boundaries are recorded there; the proof invokes no analytic
result from that literature.

No finite-dimensionality of the full smooth-function carrier is assumed.
The result neither identifies compact differential finiteness with compact
group finiteness nor proves admissibility, reproduction, or automorphic
derivative growth. It does not replace the parent theorem's simultaneous
center-finite adelic family or common annihilating ideal. The statement
pair and its imports are unchanged. The proof uses default heartbeats.
