# Pullback of the projective degree-one bundle by evaluation

This is derived infrastructure for the actual projective frame bundle. It uses
`ProjectiveBundle/EvaluationTwist`, `ProjectiveBundle/TautologicalRestriction`,
`Modules/RefinedPullbackComparison`, `Modules/CommonSourceCocycle`, and the
unconditional sheaf-morphism construction in `Modules/OpenCoverHomGluing`.
No new assertion from an external source is invoked.

The schemes `X,S` lie in an arbitrary common universe `u`. The data are a map
`p : X → S`, a module sheaf `M` on `S`, a line bundle `L` on `X`, a module map
`ev : M → p_*L.obj`, a natural number `n`, an explicit proof `hM` of local
freeness of rank `n + 1`, and `hs : FrameEvaluationGenerates p L ev n`.
The last hypothesis says that the actual evaluated basis sections generate on
the inverse image of each chosen frame open. These are the same hypotheses
used to construct the existing global evaluation map. In particular, the
compatibility of the local module comparisons is proved in this module and
its imports; it is not an additional hypothesis on the final construction.

Write `E = evaluationMap p L ev hM hs` and let `G` be the module underlying
`FrameBundle.twistOne hM` on `frameBundle M n hM`. The abbreviation
`EvaluationPullback.source` is the actual pullback module `E^*G` on `X`.
The definition `EvaluationPullback.globalIso` constructs an isomorphism

```text
E^*G ≅ L.obj.
```

It is characterized by its formula on every inverse-image frame open.
For `U : FrameOpen M n`, put `aU = (p inverse-image U).ι`, let `fU` be the
actual local evaluation map, and let `cU` be the frame-bundle chart. The
isomorphism `EvaluationPullback.localIso U` has source `aU^*(E^*G)` and target
`aU^*L.obj`. It is the composite of the canonical pullback composition
isomorphism, the normalized pullback along `fU` of the global degree-one
chart comparison, and `EvaluationTwist.localIso U`. Normalization uses the
proved equality `fU ; cU = aU ; E`. Here `;` denotes composition from left
to right. Thus the local formula concerns the given modules and scheme maps.

The theorem `globalIso_local` identifies the pullback of the constructed
isomorphism's hom with `localIso U.hom` for every frame open. The theorem
`globalIso_unique` says that any isomorphism with all these formulas equals
the constructed one. The preceding `existsUnique_iso` states both existence
and uniqueness together.

## Restriction of the local comparisons

The generic lemma `Modules.squarePullbackIso_reverse` identifies the square
comparison for the reversed commuting square with the inverse of the original
comparison. Its proof unfolds the canonical square and equality comparisons.

`RefinedPullbackComparison.normalize_local_restrict` handles arbitrary six
schemes, a global map, two local source maps, and their restrictions. Its
hypotheses are the indicated commuting scheme-map equations, two global chart
isomorphisms compatible under restriction, and a compatible square of local
module morphisms. It concludes the restriction equation for their normalized
composites. The proof combines `normalize_refine`, square reversal, and the
associativity law for `compHom`. No Cartesian or open-immersion hypothesis is
needed for this generic lemma.

The concrete `EvaluationPullback.localIso_restrict` applies that lemma to the
actual evaluation and frame charts. The inputs are the proved
`FrameBundle.twistOneModuleIso_restrict` and
`EvaluationTwist.localIso_compatible`. For `U ≤ V` and the actual inclusion
`j : p inverse-image U → p inverse-image V`, its equation is

```text
j^*(localIso V.hom) ; compHom(j,aV,aU,L.obj)
  = compHom(j,aV,aU,E^*G) ; localIso U.hom.
```

The target comparison is written in Lean as `openPullbackIso`; it is the
canonical composition comparison for the actual inclusions.

## Gluing on the inverse-image frame opens

The generic lemma `Modules.square_compatible_of_common_restriction` takes two
maps between restrictions of fixed modules and their restrictions to a common
source. If both restriction equations have the same resulting map, the lemma
proves their square compatibility. It cancels the canonical composition
comparison and applies `CommonSourceCocycle.square_normalize` twice.

The helper `existsUnique_hom_of_frameRestriction` works with arbitrary module
sheaves `A,B` on `X`, the same map `p`, and the locally free sheaf `M` of rank
`n + 1`. It glues a family of maps `aU^*A → aU^*B` satisfying all nested-frame
restriction equations. The inverse-image frame opens cover `X`, by
`exists_frameOpen` applied at `p x`. The intersection of two frame opens is
again a frame open, using the actual restriction of one frame. Pulling both
maps to its inverse image gives the common-source restriction equations, and
hence square compatibility. Its image is the intersection of the two original
inverse-image opens, by preservation of intersections under preimage.

The proof uses `OpenCoverHomGluing.conj_square` and `transport_compat` to
obtain compatible maps on sections over every open contained in a cover member.
The resulting `LocalFamily` has naturality and scalar compatibility supplied
by the existing transport lemmas. `LocalFamily.hom` glues it as a module
morphism. The local computation is proved using `hom_app`, `transport_image`,
and `pullback_map_eq_of_app`. Uniqueness follows from `hom_ext_of_local` and
the local pullback equations. This uses actual sheaf gluing rather than a
supplied gluing proposition.

The helper `existsUnique_iso_of_frameRestriction` applies this morphism gluing
to the forward and inverse maps of compatible local isomorphisms. The inverse
restriction equations follow by cancellation from the forward ones. Each
global inverse identity follows by uniqueness of gluing the local identity
family: the composite and the identity have identical restrictions. Equality
of isomorphisms then follows from equality of their forward maps.

Finally `existsUnique_iso` applies this helper to the constructed `localIso`
and the proved `localIso_restrict`. `globalIso` chooses the resulting actual
isomorphism; its local computation and uniqueness are the corresponding
existence-and-uniqueness conclusions.

This unit constructs the evaluation pullback comparison under the explicit
local-freeness and generation hypotheses. It does not establish comparison
between different frame choices, tensor-line invariance of the projective
bundle, a relative cubic embedding, or a representing moduli scheme. The host
`LargeLevelRepresentabilityStatement` remains unproved.
