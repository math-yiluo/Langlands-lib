# Reflection of group-scheme properties along fppf covers

All schemes lie in an arbitrary universe `u`. Let `p : U ⟶ S` be surjective,
flat and locally of finite presentation. Each result below says that a
property of an actual group scheme, or of a homomorphism, over `S` holds once
it holds after base change along `p`. Every proof applies Mathlib's
`MorphismProperty.DescendsAlong` for the class
`@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation`. Mathlib derives that
instance from fpqc descent of Zariski-local properties
(`Mathlib.AlgebraicGeometry.Morphisms.FlatDescent`). The published module
`EtaleReflection` contains the étale versions.

- `isAffineHom_of_baseChange_of_fppf`: if the structure map of `p*G` is
  affine, so is the structure map of `G`. This uses
  `MorphismProperty.of_pullback_snd_of_descendsAlong` for `IsAffineHom`.
- `IsClosedSubgroup.of_baseChange_of_fppf`: if the base change of a
  homomorphism `i : H ⟶ G` is a closed immersion (`IsClosedSubgroup`), then so
  is `i`. The underlying map of `(baseChange p).map i` is a pullback of the
  underlying map of `i` (published `baseChange_map_isPullback`), and closed
  immersions descend along fppf surjections.
- `isIso_of_baseChange_of_fppf`: if `(baseChange p).map f` is an isomorphism,
  then so is `f`. Isomorphisms of schemes descend, the forgetful functor
  `Over S ⥤ Scheme` reflects isomorphisms, and `Grp.mkIso'` lifts the
  isomorphism in `Over S` to group schemes.
- `isoOfFppfBaseChange p f` is the resulting isomorphism, with
  `isoOfFppfBaseChange_hom` saying that its forward map is `f`.

Provenance is internal: Mathlib's fppf descent instances applied to the
published group-scheme base-change API. There is no literature assertion.
