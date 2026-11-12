# Actual coherent families on the relative space of a coproduct chart

Module: `Langlands.AlgebraicGeometry.CoherentSheaves.CoproductChartFamily`.

Author: Worker 3694, for task `5b9ad399-34f2-4314-bb39-902f491aad01`.

This internal construction glues actual flat finitely presented families on the
relative spaces of the components of a coproduct chart. It is the coherent
analogue of the published `Picard.CoproductChartBundle.bundle`, and it reuses
that module's disjoint relative cover and overlap identifications. No literature
assertion is formalized here. All schemes and index types are in one universe `u`.

## Locality of the family conditions on open covers

Namespace `CoherentSheaves.OpenCoverFamily`. Let `𝒰` be an open cover of a scheme
`Y` and `N : Y.Modules`.

- `isFinitePresentation_of_openCover`: if the ordinary pullback of `N` to every
  member of `𝒰` is locally finitely presented, so is `N`. For a point `y`, choose
  a member and a preimage `x`. The restriction of `N` to the member is
  isomorphic to the pullback, hence locally finitely presented. The published
  `exists_finitePresentation_restrict` gives an open `W ∋ x` with a finite
  presentation there. The restriction comparison moves it to the composite open
  immersion, and the published `exists_presentation_opensRange` gives a finite
  presentation on its open image, which contains `y`. The published
  `isFinitePresentation_of_forall_exists_presentation` concludes.
- `isFlatOver_of_openCover`: for `p : Y ⟶ B`, if the pullback of `N` to each member
  is flat over the composite of the member's map with `p`, then `N` is flat
  over `p`. This is the published `isFlatOver_iff_openCover`, transported along
  the isomorphism between restriction and ordinary pullback.

## The glued family

Namespace `CoherentSheaves.CoproductChartFamily`. Fix `f : X ⟶ S`,
`V : ι → Over S`, and actual families `M i : FamilyGroupoid f (V i)`. The published
`relativeCover f V` is the open cover of the relative space of
`sigmaOver V` by the relative spaces of the `V i`; distinct members do not meet
(`relativeCover_isDisjoint`).

- `module f V M` is the published `OpenCoverModuleGluing.glued` of the
  underlying modules of the `M i`, with the published disjoint-cover transitions
  `DisjointCoverGluing.transition`.
- `moduleIso f V M i` is the published `OpenCoverModuleGluing.pieceIso`, using
  the published cocycle `DisjointCoverGluing.cocycle`. It identifies the
  ordinary pullback of the glued module along
  `(relativeSpace f).map (sigmaOverι V i)` with the module of `M i`.
- `isFamily_module`: the glued module is finitely presented and flat over the
  relative projection of the coproduct chart. Both properties are checked on
  `relativeCover f V` with the two locality lemmas. On the `i`-th member, the
  pullback is isomorphic to `M i`. The composite of the member's map with the
  relative projection of `sigmaOver V` equals the relative projection of `V i`
  followed by the open immersion `(sigmaOverι V i).left`, by naturality of the
  relative projection. Flatness over this composite follows from flatness of
  `M i` and of the open immersion (published `isFlatOver_comp_of_flat`).
- `family f V M : FamilyGroupoid f (sigmaOver V)` is the resulting actual family.
- `familyIso f V M i` is the actual isomorphism in the family groupoid from the
  ordinary pullback of `family f V M` along `sigmaOverι V i` to `M i`. Its
  underlying module isomorphism is `moduleIso f V M i`.
