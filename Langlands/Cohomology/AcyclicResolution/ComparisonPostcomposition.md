# Exact postcomposition of the canonical degreewise comparison

This is an internal construction in abelian categories with independent object
and morphism universes. For an abelian category `C` with injective resolutions,
additive functors `Φ : C ⥤ E` and `Ψ : C ⥤ E'`, and an additive functor
`P : E ⥤ E'` preserving homology, supply an isomorphism
`e : Φ ⋙ P ≅ (𝟭 C) ⋙ Ψ`. The construction
`exactPostcompIso Φ P Ψ e n` is the existing
`DerivedComparison.rightDerivedCompIso` for the identity source functor,
followed by the left unitor. Thus it is a natural isomorphism

`Φ.rightDerived n ⋙ P ≅ Ψ.rightDerived n`.

No chosen derived-category instance is required. Preservation of homology is
the precise exactness premise on `P`; preservation of injective objects by
`P` is not required.

For `compComparison_postcomp`, let `F : C ⥤ D` be additive and preserve
finite limits, where `D` also has injective resolutions. Let
`G : D ⥤ E`, `H : C ⥤ E`, `G' : D ⥤ E'`, and `H' : C ⥤ E'` be additive.
Supply `e : F ⋙ G ≅ H`, the exact postcomposition isomorphisms
`eG : G ⋙ P ≅ (𝟭 D) ⋙ G'` and
`eH : H ⋙ P ≅ (𝟭 C) ⋙ H'`, and `e' : F ⋙ G' ≅ H'`.
Assume for every `Q : C` that the actual underived maps agree:

`eH.hom.app Q ≫ e'.inv.app Q = P.map (e.inv.app Q) ≫ eG.hom.app (F.obj Q)`.

For an object `A`, assume the positive derived functors of `F` vanish on
`A`. In every nonnegative degree, the theorem proves

`(exactPostcompIso H P H' eH n).hom.app A ≫ compComparison G' e' A hA n`

`= P.map (compComparison G e A hA n) ≫ (exactPostcompIso G P G' eG n).hom.app (F.obj A)`.

The comparison maps are the existing canonical `compComparison` maps. The
result requires neither preservation of homology by `F` nor preservation
of injectives by any of the displayed nonidentity functors. Objectwise
vanishing supplies the required image resolution.

The proof takes one injective resolution `I` of `A` and maps its augmentation
along `F`. The published acyclicity result makes that mapped augmentation
a right resolution. The private identity-augmentation lemma identifies
mapping by the identity functor with the original augmentation. Apply
`resolutionComparison_rightDerivedCompIso` to the source resolution and
the mapped right resolution. The termwise compatibility hypothesis gives
an equality of cochain maps and therefore of their degree-`n` homology maps.
The source resolution comparison is the inverse of `I.isoRightDerivedObj`,
so its image under `P` can be cancelled. Apply
`resolutionComparison_compComparison` on each side and use naturality of
`mapHomologyIso` to finish with the cochain homology identity.

The provenance is internal, from the existing arbitrary-resolution comparison
formulas and homology-comparison naturality. The related theorem
`derivedCompComparison_postcomp` in `DerivedComparisonComposite` concerns
morphisms in chosen derived categories; the present result directly concerns
the degreewise right-derived functors. Scheme-module specialization,
comparison with Ext-defined sheaf cohomology, actual Picard obstruction
naturality, and the exact field Picard-stack atlas remain further obligations.
