# Basic geometry of an abelian scheme over a discrete valuation ring

Author: Worker 171.

Module `Langlands.AlgebraicGeometry.Picard.DvrAbelianGeometry`, namespace
`Langlands.AlgebraicGeometry.Picard.DvrAbelianGeometry`. `R` is a discrete valuation
domain in universe `u` and `A : Langlands.AbelianScheme (Spec (CommRingCat.of R))`.

- `geometricallyIntegral`: the structure morphism of any Library abelian scheme over
  any base is `GeometricallyIntegral`. Every base change to a field is smooth and
  geometrically connected, so the published `smoothGeometricIntegrality` and Mathlib's
  `GeometricallyIntegral.isIntegral_of_subsingleton` apply.
- `isIntegral_total`: the total space `A.X.left` is integral
  (`GeometricallyIntegral.isIntegral_of_isLocallyNoetherian`, using flatness and
  universal openness of smooth morphisms).
- `eq_bot_or_eq_closedPoint`, `bot_ne_closedPoint`: `Spec R` has exactly the points
  `⊥` and `IsLocalRing.closedPoint R`, and they differ.
- `unif π`, `unifX A π`: an element `π : R`, as a global function on `Spec R` and,
  pulled back, on the total space. `mem_basicOpen_unif_iff` and
  `mem_basicOpen_unifX_iff`: for irreducible `π` the principal open of `unifX A π` is
  the complement of the special fibre.
- `isAmple_basicOpen`: if the fibre bundle at `⊥` is ample, the restriction of `L` to
  the principal open of `unifX A π` is ample. The published
  `properFibreAmpleSpreading` gives an open neighbourhood of `⊥` with ampleness; the
  principal open lies in it and its inclusion is affine, so
  `LineBundle.IsAmple.pullback_of_isAffineHom` and `openPullbackIso` apply (the same
  pattern as `LineBundle.isAmple_of_affine_base_neighbourhoods`).
- `exists_specialGeneric`: the special fibre has a point `ξ` specializing to every
  point of the special fibre (image of the generic point of the integral fibre scheme,
  via `Scheme.Hom.range_fiberι`).
- `exists_generic_generization`: every point of the special fibre is a specialization
  of a point of the generic fibre (`Flat.generalizingMap`).
- `exists_global_section_of_basicOpen`: on a quasi-compact quasi-separated scheme, a
  section of a power of the restriction of `L` to a principal open `D(a)` is, after
  clearing a power of `a`, the restriction of a global section with the same
  generation open on `D(a)`. This repeats the first half of the published proof of
  `LineBundle.isAmple_of_principal_neighbourhoods` (`openPowSection_surjective`,
  `PrincipalSectionExtension.exists_global`, `trivializationOpen_smul_unit`).

All statements are internal infrastructure derived from published Library and
Mathlib results; no external source is asserted.
