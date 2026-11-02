# Glued line bundles under refinement of open covers

This internal construction extends the published transition-cocycle and frame
gluing modules. Let `X : Scheme.{u}`, let `T : ι → X.Opens` and
`S : κ → X.Opens`, with both index types in `Type u`. A refinement consists of
`β : κ → ι` and inclusions `hβ j : S j ≤ T (β j)`. No finiteness, affineness,
compactness or separation hypothesis is imposed.

For actual structure-sheaf units `g i j` on `T i ⊓ T j`, `refineCocycle g β hβ`
restricts `g (β i) (β j)` to `S i ⊓ S j`. The lemma `refineCocycle_val`
computes its underlying ring section.

If `g` is a cocycle, `refineFrame g hg β hβ j` is the original local generator
of `glued g` for the index `β j`, restricted to `S j`. Restriction of the
generator and the published scalar-multiplication bijection prove
`isFrameOn_refineFrame`. The published relation between local generators gives
`isTransition_refineFrame`: these frames have precisely the restricted
transition units. Applying the published cocycle equation for transitions
of frames proves `isCocycle_refineCocycle`. None of these constructions requires
that either family covers `X`.

If `S` is a full cover, `refinementIso g hg β hβ hS` is a specified isomorphism
of actual module sheaves

```text
glued g ≅ glued (refineCocycle g β hβ).
```

It is the published `frameIso` for the restricted original generators.
Its forward morphism takes coefficients in these frames. The two lemmas
`refinementIso_hom_app_genSec` and `refinementIso_inv_app_genSec` compute the
forward and inverse maps on the corresponding local generators over every
`V ≤ S j`. The forward map sends the original generator with index `β j`
to the refined generator with index `j`; the inverse recovers it.
There is no separate full-cover hypothesis on `T`.

The proof is an internal composition of the published
`CocycleLineBundleFrame` and its generator/restriction inputs. It is not a
translation of a new assertion from an external source. This module establishes
sheaf-level gluing compatibility under refinement. It does not assert
compatibility with ordered cochain refinement or actual derived sheaf
cohomology, a cover-independent Picard classification, pullback naturality,
line-bundle deformation, or Picard representability.
