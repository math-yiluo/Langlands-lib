# Preservation of ampleness by closed-immersion pullback

`Langlands.AlgebraicGeometry.Picard.ClosedImmersionPullbackAmpleStatement`
is the following universe-polymorphic proposition, stated here without a proof:

```text
∀ (X Z : Scheme.{u}) (i : Z ⟶ X) (L : LineBundle X),
  IsClosedImmersion i → L.IsAmple → ((LineBundle.pullback i).obj L).IsAmple
```

Here `LineBundle X` is the published full subcategory of actual module sheaves
that are locally free of rank one. The functor `LineBundle.pullback i` is the
published lift of `Scheme.Modules.pullback i`; its preservation of local rank
one is already proved. Thus the conclusion concerns the actual pulled-back
module sheaf with that line-bundle structure.

Both schemes are arbitrary. In particular, the statement includes nonreduced
closed subschemes, closed immersions that are not of finite presentation, and
the empty scheme. No properness, finite type, projectivity, reducedness,
residue-comparison or tensor-coherence hypothesis is imposed.

## Whole generation-open scope

The imported predicate `L.IsAmple` asserts `CompactSpace X` and that every point
of `X` belongs to `L.sectionOpen s` for some positive integer `n` and global
section `s` of `Langlands.Scheme.Modules.tensorPow L.obj n`, with the **whole**
open `L.sectionOpen s` affine. Tensor powers are the actual published sheafified
tensor powers, with zeroth power the structure module and successor given by
the right-associated tensor product.

The open `L.sectionOpen s` is `trivializationOpen (tensorPow L.obj n) s`,
the largest open on which the section-induced map from the structure module
is an isomorphism. Affineness is required of that entire open subscheme. An
arbitrary smaller affine neighborhood on which the section generates would
not suffice. The conclusion uses this same definition on `Z` for
`(LineBundle.pullback i).obj L`, including its compactness requirement.

## Source correspondence and remaining proof

The source is Stacks Project Lemma 28.27.3, tag
[01PU](https://stacks.math.columbia.edu/tag/01PU), statement and proof,
retained as `01PU.html` in the registered source
`stacks-ample-powers-restriction-quasiaffine-2026-10-24`, directory SHA256
`03dddd39b5528263fbc3633f1545b8544e937bb29c9752ffe4a351bb6e093e9a`.
It states preservation of ampleness upon restriction to any closed subscheme.
Restriction here means pullback of the module sheaf along its closed
immersion, rather than restriction to an open subset or replacement by the
reduced closed subscheme. The displayed Lean proposition expresses that
interpretation for any closed-immersion morphism.

The source's proof uses compactness of a closed subspace and affineness of a
closed subscheme of an affine scheme. To implement this argument with the
published definitions, a future proof must also construct the pullback of a
global section of each positive tensor power and identify the pulled-back
power with the corresponding power of the pulled-back bundle. It must prove
that the **whole** generation open of the resulting section is `i ⁻¹ᵁ
(L.sectionOpen s)`. The restricted closed immersion then identifies this open
as a closed subscheme of the affine `L.sectionOpen s`. Compactness follows
from the closed embedding of `Z` into the compact space underlying `X`.
These are proof obligations, not extra premises of the statement.

Stacks uses the nonvanishing description of the generation locus for
invertible sheaves. The published `Ample` module uses the maximal
trivialization-open presentation and documents its source correspondence.
Its comparison with residue-field nonvanishing is currently conditional on
`LineBundleResidueOpenComparison` (and rank one of the tensor powers when
applying that comparison to powers). This statement does not assume or prove
that comparison. A future proof must establish any needed comparison or work
directly with generation opens; it cannot use a conditional comparison as an
unconditional theorem.
