# Natural native coefficient image-quotient comparisons

This internal construction extends the published complex image-filtration proof to native representations over a complex algebra. Its ingredients are `CoefficientExactness`, the actual `Localization.imageSubfunctor` and `imageFiltration`, and the natural quotient first-isomorphism construction `RepSubfunctor.quotientNatIsoOfSurjective`. It does not assume a geometric lemma.

Let `R` be a commutative complex algebra, `G` a topological group, `U ≤ G` a limit of compact subgroups, and `M ≤ G` a subgroup normalizing `U`. Let `F : C ⥤ Rep R G` have smooth objects. All coefficient, group, carrier, object-category and morphism universes are independent. For an actual subfunctor `S`, its image is the set of native quotient classes with a representative in `S`. The character throughout the comparisons is one.

`imageHom` sends the native quotient of `S` to this actual ambient image by the quotient map induced from the inclusion `S → F`. It is surjective because every element of the image has a representative in `S`. Its definition and surjectivity work over arbitrary commutative rings, without the complex-algebra or topological assumptions. `imageIso` additionally uses native injectivity for the smooth ambient action, proved in `CoefficientExactness`, to turn this canonical map into a natural isomorphism. Naturality follows from the original subfunctor maps on representatives.

For nested actual subfunctors `S ≤ T`, `imageQuotientMap` first uses the inverse of `imageIso` for `T`, then applies the native quotient functor to the original projection `T → T/S`. `imageQuotientMap_imageHom` specifies its effect on a localized upper vector. The map is surjective because the original quotient projection is surjective and native quotients preserve surjections.

`imageQuotientMap_kernel` proves that its kernel is exactly the actual lower ambient image, pulled back to the actual upper image. The inclusion `S → T` has range equal to the kernel of `T → T/S`. Native middle exactness gives the analogous range-kernel identity after quotienting by `U`. Native injectivity for the inclusion `T → F` then identifies this range with the lower image inside the ambient quotient. Thus the kernel assertion concerns the actual specified submodules, not an existential replacement filtration.

`imageQuotientIso` descends this map through the actual image quotient by `quotientNatIsoOfSurjective`. It gives the natural `R`-linear `M`-representation isomorphism

```text
image(T) / image(S)  ≅  (T/S)_U .
```

The exact denominator on the left is `lowerInUpper`, as in the existing quotient API. `imageQuotientIso_projection` fixes the comparison on representatives: the class of the ambient image of `v ∈ T` maps to the native `U`-class of its original `T/S` class. The inverse used to construct the comparison therefore does not leave an unspecified comparison map.

`imageFiltrationGradedIso` applies this construction at each adjacent pair of a supplied actual finite filtration. It identifies every grade of the fixed `imageFiltration` with the native quotient of the corresponding original grade. It retains all indices, including repeated steps and zero grades. No finiteness, admissibility, flatness or Noetherian premise is present.

This unit supplies the native support-image exactness bridge needed in the coefficient geometric-lemma route. The rational-parabolic finite orbit geometry, passage from subgroup-stable support to the ambient quotient, normalized orbit-Jacquet formulas, cuspidal elimination and final compact-open fixed-module finiteness are separate obligations.
