# Free Čech exactness for objectwise surjective presheaf arrows

This internal construction proves that the actual free module presheaf Čech
augmentation is a quasi-isomorphism when the underlying set-valued presheaf
arrow is surjective at every object. Exact sheafification gives the same
conclusion for `freeCechAugmentation` from `FreeNerve`.

Let `C` be a category with independent object and morphism universes, let
`R : Type w` be a commutative ring, and let
`f : Arrow (Cᵒᵖ ⥤ Type w)`. The hypothesis is
`∀ U : Cᵒᵖ, Function.Surjective (f.hom.app U)`. There is no local-smallness
assumption on `C`. The sheaf conclusion also fixes a Grothendieck topology
`J` on `C` and assumes `HasSheafify J (ModuleCat.{w} R)`.

`freeModulePresheafFunctor R` applies `ModuleCat.free R` objectwise.
`freePresheafAugmentedCechNerve R f` applies that functor to the actual
augmented Čech nerve in the category of set-valued presheaves. The limits
needed for this nerve exist in the presheaf category; no products in `C`
are assumed. `freePresheafCechChainComplex R f` is its alternating-face-map
chain complex in nonnegative degrees. `freePresheafCechAugmentation R f`
is the actual augmentation to the free module presheaf on `f.right`,
concentrated in degree zero.

The module first gives a general augmentation comparison. For abelian
categories `A` and `D`, an additive functor `F : A ⥤ D` and an augmented
simplicial object `X` in `A`, `augmentationMapArrowIso F X` is an isomorphism
of arrows between the image of the actual augmentation under
`F.mapHomologicalComplex` and the actual augmentation of the mapped
simplicial object. Its source is Mathlib's alternating-face-map comparison,
and its target is Mathlib's single-complex comparison. The square is proved
by checking each degree: in degree zero both sides are the image of the
augmentation component, and in positive degrees both sides are zero.
`quasiIso_map_augmentation_iff` transports quasi-isomorphism across this
arrow isomorphism. It does not require `F` to be exact.

`evaluationSplitEpi f U h` chooses the right inverse of a surjection
`f.hom.app U` using `Function.surjInv`. The choice is made separately for
each `U` and need not be natural in `U`.
`evaluatedFreePresheafCechExtraDegeneracy` first applies
`mappedCechExtraDegeneracy` from `CechEvaluation` to evaluation of
set-valued presheaves, which preserves the defining wide pullbacks.
It then applies `ModuleCat.free R` to that extra degeneracy. Evaluation of
the free module presheaf nerve agrees with this objectwise free nerve,
so the resulting extra degeneracy contracts precisely the evaluated
augmented free module presheaf nerve.

`quasiIso_freePresheafCechAugmentation_of_surjective` applies Mathlib's
criterion `HomologicalComplex.quasiIso_iff_evaluation`. For each `U`,
the extra degeneracy gives a homotopy equivalence whose forward map is
the actual augmentation of the evaluated augmented nerve.
`quasiIso_map_augmentation_iff` identifies its quasi-isomorphism with that
of the evaluated original augmentation. Thus the actual presheaf
augmentation is a quasi-isomorphism in every degree.

Finally, `quasiIso_freeCechAugmentation_of_objectwise_surjective` applies
`presheafToSheaf J (ModuleCat R)`. Under `HasSheafify`, this additive left
adjoint preserves finite limits as well as finite colimits, hence preserves
homology and quasi-isomorphisms. The same augmentation comparison identifies
the resulting quasi-isomorphism with the existing `freeCechAugmentation`.

The provenance is internal: objectwise sections, the defining Čech
wide-pullback comparison, Mathlib's extra-degeneracy homotopy equivalence,
the evaluation criterion for complexes in a functor category, and exact
sheafification. No external-source theorem is asserted here.
Objectwise surjectivity is stronger than local surjectivity. The module does
not prove exactness for an arbitrary locally surjective presheaf arrow,
analytic higher-nerve presentations, restricted-injective coefficient
acyclicity or the analytic comparison theorem.
