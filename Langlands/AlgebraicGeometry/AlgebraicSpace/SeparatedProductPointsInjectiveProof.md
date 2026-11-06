# Proof of injectivity for product-ring points of separated algebraic spaces

Author: Worker 105.

`separatedProductPointsInjective` proves `SeparatedProductPointsInjectiveStatement`.
The work is done by `separatedProductPoints_injective`, for a fixed commutative ring
`C`, a separated algebraic space `X` over `Spec C` and a family `R` of `C`-algebras.

The proof follows Conrad's scheme argument for (3.6.2) on printed pp.7–8: the locus
where two points agree is a closed subscheme of `Spec (∏ R i)` that contains every
factor spectrum, so it is everything.

1. Let `p` and `q` be points with values in `∏ R i` that have the same images in
   every factor. The Library lemma `exists_representsEqualizer_of_relative_diag`
   (in `Langlands/AlgebraicGeometry/AlgebraicSpace/DiagonalEqualizer.lean`) applies
   to the separatedness hypothesis, that is, to the diagonal being a representable
   closed immersion. It gives a scheme `Z` over `Spec C` and a morphism
   `j : Z ⟶ ringTest C (∀ i, R i)` whose underlying scheme morphism is a closed
   immersion. A morphism `g` into `ringTest C (∀ i, R i)` factors through `j` exactly
   when the pullbacks of `p` and `q` along `g` agree (`RepresentsEqualizer`).
2. For each `i`, the pullbacks of `p` and `q` along the factor map
   `ringTestMap C (Pi.evalAlgHom C R i)` agree by hypothesis. So this factor map
   factors as `z i ≫ j`.
3. `Spec (∏ R i)` is affine, so the closed subscheme `Z.left` is affine
   (`IsClosedImmersion.isAffine_surjective_of_isAffine`), hence quasi-compact, and
   `j.left` is an immersion. The morphism `Sigma.desc (fun i => (z i).left)` from the
   disjoint union of the factor spectra, followed by `j.left`, is Mathlib's
   `sigmaSpec`. Here the factor rings are viewed as the family of commutative rings
   `CommRingCat.of (R i)`, and the identification is checked on each summand. Andrew
   Yang's Mathlib lemma `isIso_of_comp_eq_sigmaSpec` (in
   `Mathlib/AlgebraicGeometry/PointsPi.lean`) then shows that `j.left` is an
   isomorphism. This is the step where a quasi-compact locally closed subscheme of
   `Spec (∏ R i)` containing all factor spectra is the whole spectrum.
4. The inverse of `j.left` is a morphism over `Spec C`, which gives a section `s` of
   `j`. Applying `RepresentsEqualizer` to the identity, which factors as `s ≫ j`,
   shows that the pullbacks of `p` and `q` along the identity agree, so `p = q`.

The proof uses no hypothesis on `C`, on the index type or on the factors, and no
finiteness condition on `X`.
