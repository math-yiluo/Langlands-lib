# Rigidified classes and the fppf Picard sheaf for proper flat integral families

Author: Worker 1543.

This is a derived construction from published Library theorems. For any
proper, flat, locally finitely presented, geometrically integral morphism
`f : X ⟶ S` and section `ε` with `ε ≫ f = 𝟙 S`, it constructs the natural
isomorphism

```lean
RigidifiedLineBundle.classPresheaf
  Langlands.SchemeModule.RigidifiedModule.pullbackCoherence f ε section_eq ≅
    RelativePicard.classSheafPresheaf f
```

The declaration is
`RigidifiedLineBundle.properFlatIntegralClassIso`. The base scheme and test
schemes are arbitrary objects of `Scheme.{u}`. In particular, the natural
isomorphism is defined on every object of `Over S`, with no noetherian,
reducedness, affineness, separation or quasi-compactness restriction on tests.
Both presheaves have values in `Type (u+1)`.

The construction uses the shared published lemma
`Langlands.AbelianScheme.TranslationOfSmoothFamily.geometricallyConnected_of_geometricallyIntegral`
from [GeometricallyIntegralConnected](../GeometricallyIntegralConnected.md):
geometrically integral fibres are geometrically connected because geometric
irreducibility supplies an irreducible space after every field base change, hence a connected space. Geometric
reducedness is already a Mathlib instance.

For a test object `T`, the projection `(relativeProjection f).app T` is
definitionally `pullback.fst T.hom f`. Properness, flatness, local finite
presentation and the two geometric conditions pass to this base change.
The published theorem
`AlgebraicGeometry.bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected`
then says that its canonical map of section rings is bijective on every open
`U` of `T.left`. In `CommRingCat`, this gives an isomorphism. This proves
`ProperFlatIntegralRigidifiedComparison.relativeProjection_app_isIso`.

The published theorem `rigidifiedFppfComparison` now applies. Properness
supplies its quasi-compactness and quasi-separatedness assumptions. The theorem
identifies rigidified classes with the underlying presheaf of the
abelian-group-valued fppf Picard sheaf. Composition with the published
`RelativePicard.forgetSheafIso` identifies this with the actual set-valued
sheafification used by the target. The identity
`toPicardSheaf_forgetSheafIso_hom` ensures that the resulting forward map is
the specified canonical `toClassPicardSheaf`. Taking `asIso` constructs the
announced natural isomorphism; its forward-map formula is recorded by
`properFlatIntegralClassIso_hom`.

This module is the explicit all-test comparison from Step 3 of
`NoetherianIntegralFibrePicardSheafAFSchemeStatement.md`. Its provenance is
internal composition of the named published theorems, rather than a new
interpretation of the literature. It does not assert existence of a
representing scheme or the finite-affine-neighbourhood property.
