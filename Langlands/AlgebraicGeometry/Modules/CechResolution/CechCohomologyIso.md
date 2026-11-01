# Čech cohomology computes relative cohomology in every degree

Author: Worker 1137.

This internal helper module turns the published derived-category Čech
comparison into an isomorphism of cohomology objects in each natural degree.

`rightDerivedObjIsoHomologyOfDerivedIso F K e n` works for an additive functor
`F : C ⥤ D` between abelian categories with derived categories, where `C` has
enough injectives. It takes a natural-indexed cochain complex `K` in `D`, an
isomorphism `e` in `DerivedCategory D` from `Q` of the integer extension of
`K` along `ComplexShape.embeddingUpNat` to the image under
`DerivedCategory.Plus.ι` of `DerivedPlus.derivedComplex F` at `A`, and a degree
`n : ℕ`. It returns `(F.rightDerived n).obj A ≅ K.homology n`. The isomorphism
is the composite of:

1. the inverse of `DerivedPlus.homologyIso F (injectiveResolution A) n`, which
   identifies `F.rightDerived n` at `A` with degree-`n` cohomology of the
   derived complex (bounded-below cohomology is by definition `Plus.ι`
   followed by `DerivedCategory.homologyFunctor`);
2. degree-`n` derived-category cohomology applied to `e.symm`;
3. `DerivedCategory.homologyFunctorFactors`, which identifies cohomology of
   `Q` of a complex with its complex cohomology;
4. `HomologicalComplex.extendHomologyIso`, which identifies cohomology of
   the extension in degree `(n : ℤ)` with cohomology of `K` in degree `n`.

`nonempty_relativeCohomology_iso_cechCochainComplex_homology π 𝒰 M n`
specializes this. Here `π : X ⟶ Spec R` is separated, `𝒰` is any
`X.OrderedAffineCover`, `M` is a quasi-coherent module sheaf, and the common
universe `u` is arbitrary. The theorem states
`Nonempty ((relativeCohomology π n).obj M ≅ (cechCochainComplex π 𝒰 M).homology n)`.
Its proof maps `rightDerivedObjIsoHomologyOfDerivedIso` over the published
`nonempty_cechCochainComplex_iso`. It uses the local instance
`HasDerivedCategory.standard` only inside the proof. The statement involves no
derived category.

Provenance: internal. This is the standard fact that a complex
quasi-isomorphic to the derived complex computes the derived functors in each
degree. It contributes to the Künneth proof of task
`4011daf4-db93-4fbc-aba0-1659c8a196b9`, where it is applied to both factors
and to the product.
