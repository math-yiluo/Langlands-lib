# Compact sections along proper continuous equivariant maps

This module constructs compact-section maps along actual proper continuous
equivariant maps. Its namespace is
`Langlands.Sheaf.Equivariant.ProperCompactSections`.

The construction is internal: it combines the full direct image in
`Langlands.Sheaf.Equivariant.DirectImage` with the actual restriction-defined
support in `Langlands.Sheaf.LocalSupport` and its equivariant compact-section
functor in `Langlands.Sheaf.Equivariant.LocalSupport`. The proof uses Mathlib's
`IsProperMap.isCompact_preimage` and closed-subset compactness. It does not
translate a new assertion from Harris or Berkovich.

The space universe `u`, group universe `v`, commutative-ring universe `r`, and
module universe `w` are independent; the source and target spaces share `u`.
The coefficient category is `ModuleCat.{w} R`, and the resulting action category
is `Rep.{w} R G`. Before constructing representations, only a group acting on
each space is required. For the representation maps, each individual group
translation must be continuous on each space, expressed by
`ContinuousConstSMul G X` and `ContinuousConstSMul G Y`. Neither a topology on
`G` nor joint continuity of its action is required.

For a continuous equivariant map `f : X → Y` and a transport presheaf `F` on
`X`, the global sections of `f_* F` are literally the global sections of `F`.
If such a section vanishes on a neighborhood of `f x`, it vanishes on its
inverse open neighborhood at `x`. Thus its support on `X` is contained in the
inverse image of its support on `Y`. Here `pushed` is the entire transport
presheaf direct image, rather than a coefficient subfamily. `vanishesNear`
uses the same zero restriction on the actual inverse open.
`support_subset` expresses this containment. The source support is closed
even for a presheaf. If `f` satisfies `IsProperMap f`,
`preserves_compactSupport` proves that this closed subset of a compact inverse
image is compact. This argument does not require a sheaf condition.

When every individual group translation on both spaces is continuous, `map`
restricts the unchanged original global section to the compact-support
submodule. It intertwines the original group action. `presheafNatTrans` and
`natTrans` make this map natural in every original transport-presheaf or sheaf
morphism. In particular, `natTrans` has type

```text
(DirectImage.sheaf f hf (ModuleCat R)) ⋙ LocalCompactSections.functor R G Y
  ⟶ LocalCompactSections.functor R G X.
```

The map's underlying original section is unchanged, as `map_apply` states.
The group action also agrees literally: direct image retains the original
group labels on every transport arrow. Thus the intertwining obligation
is reflexive. `globalIso` identifies the entire global-section representation
functors along direct image, and `inclusion_triangle` proves compatibility
with their actual compact-section inclusions.

`natTrans_id` proves that the identity spatial map induces the identity on
compact sections. For proper equivariant maps `f : X → Y` and `g : Y → Z`,
`natTrans_comp` identifies the compact-section map for `g ∘ f` with the map for
`g` applied to `f_* F`, followed by the map for `f` applied to `F`. The generic
direct-image identity and composition endpoints are definitionally the
required ones. Both laws are proved by equality of original section values.

More generally, let `K` be any full equivariant module sheaf on `Y`, let `F`
be any such sheaf on `X`, and let `b : K → f_* F` be an actual sheaf morphism.
`pullback` composes the compact-section functor applied to `b` with
`natTrans.app F`. Its `pullback_apply` formula is exactly

```text
s ↦ b.hom.app (op ActionOpens.top) s.val.
```

No separate support-preservation hypothesis on `b` is required: functoriality
of local support handles `b`, and properness handles the spatial step.
`pullback_precomp` and `pullback_postcomp` prove naturality in both sheaves
using their original morphisms. For `c : L → g_* K`,
`pullback_comp` proves that the map associated to
`c ≫ (DirectImage.sheaf g hg _).map b` along `g ∘ f` equals the compact
pullback along `g` followed by the compact pullback along `f`. These identities
also reduce to the actual global-section component formulas.

The construction assumes no coefficient topology, finite dimensionality,
Hausdorff property, local compactness or smoothness. The map `K → f_* F` is
genuine input data; this module does not construct such a map for every pair
of sheaves. In particular, it makes no inverse-image adjunction assertion.
It establishes neither smoothness of direct images nor a higher derived,
Godement or étale comparison. Those comparisons, the arithmetic towers and
the Harris specialization remain separate obligations of the wider task.
