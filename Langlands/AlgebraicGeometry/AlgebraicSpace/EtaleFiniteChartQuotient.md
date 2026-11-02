# Affine open images of charts with finite kernel pair

This internal helper constructs affine open images for the monomorphism schemehood proof. All schemes and presheaves retain the arbitrary base universe `u`.

`HasFiniteKernelPair a` says that the kernel pair of the actual scheme chart `a : h_U → F` is represented by an actual scheme `R` over the base, with both projections `R → U` finite. It does not itself require that the chart is etale.

`isAffineOpen_sheafify_range_of_hasFiniteKernelPair` assumes that `U` is affine, `a` is representable etale, `F` is an fppf sheaf, and `a` has a finite represented kernel pair. It proves that the fppf sheafified image of `a` is an affine open subfunctor of `F`, in the published sense `AffineOpenSubfunctors.IsAffineOpen`. In particular it supplies an actual affine scheme over the base and an actual natural isomorphism with that image.

The implemented proof uses the published `OpenSubfunctorImages` results to make the image an open subsheaf with an etale surjective chart. Cancellation of its monomorphic inclusion identifies its kernel pair with the given one. Etaleness of the chart makes both projections etale, hence flat and locally of finite presentation. The published finite locally free equivalence relation quotient theorem therefore supplies an affine scheme quotient. The published common-kernel-pair comparison identifies its functor of points with the image sheaf, including descent of the structure morphism to the base.

`hasFiniteKernelPair_of_finite_mono_composite` requires a monomorphism `f : F → h_T` and an actual finite scheme morphism `w : U → T` with `a ≫ f = h_w`. The scheme pullback `U ×_T U` has finite projections by base change of `w`. Yoneda preservation of this pullback and cancellation of `f` show that it represents the kernel pair of `a`. The final theorem `isAffineOpen_sheafify_range_of_finite_mono_composite` combines these results. There is no surjectivity requirement on `a` or affineness requirement on the base or `T`.

Provenance is internal and derived: the argument combines the published modules `OpenSubfunctorImages`, `EtaleEquivalenceRelationPresentation`, and `FiniteLocallyFreeEquivalenceRelationAffineQuotientProof` with Mathlib kernel-pair cancellation and stability of finite morphisms under base change. It constructs only the indicated image; it does not assert that all locally finite type monomorphisms from algebraic spaces have scheme sources.
