# Module comparisons on an intersection-closed genuine frame atlas

This is derived infrastructure for projective frame bundles. It adapts the
published `EvaluationPullback.existsUnique_hom_of_frameRestriction` argument
from inverse images of all frame opens to the actual projective charts of a
specified genuine frame atlas. It uses the existing module morphism-gluing
construction, with no new external geometric input.

Let `S : Scheme.{u}`, `M : S.Modules`, `n : ℕ`, and `a : FrameAtlas M n`.
Assume the opens in the atlas are closed under binary intersection:
`hInf : ∀ U V : a.opens, U.val ⊓ V.val ∈ a.opens`.
The atlas already includes its covering basis and actual module frames.
No separate local-freeness hypothesis is needed for this construction.

`intersection hInf U V` is the atlas member with underlying open
`U.val ⊓ V.val`. `chart_intersection_opensRange` proves that its actual
projective chart has range equal to the intersection of the ranges of the
two original charts. This follows from the published Cartesian chart-range
formula and preservation of intersections by inverse image under `a.toBase`.

Write `jU = a.cocycle.chart U` and, for an ordered atlas arrow `h : U ⟶ V`,
write `r = a.cocycle.chartFunctor.map h`. The published transition equation
is `r ≫ jV = jU`.

For any two module sheaves `A B` on `a.bundle`, suppose that the actual
chart pullbacks have isomorphisms `e U : jU* A ≅ jU* B`. The required
compatibility is

`r*((e V).hom) ≫ compHom r jV jU (transition_chart h) B`

`= compHom r jV jU (transition_chart h) A ≫ (e U).hom`.

`existsUnique_iso_of_restriction` proves that such data determine a unique
`E : A ≅ B` whose forward map pulls back to `(e U).hom` on every chart.
`restrictionIso` chooses this isomorphism; `restrictionIso_local` gives its
actual local formula. Compatibility remains an explicit input: these
results do not assert that arbitrary local isomorphisms glue.

The morphism version `existsUnique_hom_of_restriction` first proves the
corresponding unique gluing of forward maps. For two charts, restriction
to the intersection chart gives a canonical common-source square via
`square_compatible_of_common_restriction`. Its range is the whole
intersection, so the existing `OpenCoverHomGluing.transport_compat`
identifies the transported section maps on every smaller open. The existing
`LocalFamily.hom` then constructs the global module morphism. Its local
formula and uniqueness follow from the same transport lemmas and
sectionwise extensionality.

For isomorphisms, the restriction equation also holds for the inverse
maps by cancellation of the pulled-back forward isomorphisms. The morphism
theorem glues both directions. Their composites are identities because
they restrict to identities on the covering charts and the glued morphism
is unique. This proves the claimed existence and uniqueness.

The joint frame-and-line basis used by `TensorFrames.sourceAtlas` and
`TensorFrames.tensorAtlas` satisfies the intersection condition by
`TensorFrames.opens_of_le`. This module supplies a gluing mechanism for
that application; it does not construct the tensor-line degree-one
comparison, a moduli space, or the main representability proof.
