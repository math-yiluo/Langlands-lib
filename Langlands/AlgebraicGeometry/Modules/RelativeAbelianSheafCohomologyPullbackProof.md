# Relative module cohomology and arbitrary sheaf-cohomology pullback

The theorem `Langlands.AlgebraicGeometry.Modules.AbelianSheafComparison.relativeAbelianSheafCohomologyPullback` proves exactly the existing proposition `RelativeAbelianSheafCohomologyPullbackStatement.{u}`. For every commutative ring `R`, schemes `X` and `Y` over `Spec R`, morphism `f : Y ⟶ X`, modules `M` on `X` and `N` on `Y`, coefficient arrow `k : M ⟶ f_* N`, natural degree `n`, and class `x` in sheaf cohomology of the underlying abelian sheaf of `M`, the actual additive comparison `relativeHAddEquiv` intertwines the Ext-defined sheaf map `pushforwardMap f.left.base ((toAbSheaf X.left).map k)` with the canonical relative module pullback followed by cohomology of the module-adjoint coefficient arrow.

The result imposes no additional geometric condition on `f`, no vanishing condition on higher direct images, and no exactness condition on module inverse or direct image. It compares the fixed constructions in the statement, including both specified adjunctions. The statement and its import closure are used unchanged.

## Implemented proof

`relativeComparisonOnComplex_pushforward_single` evaluates the established relative sections/Hom comparison on the actual termwise pushforward of a singleton complex. Naturality along `singlePlusMapIso`, followed by `relativeComparisonOnComplex_singlePlus`, expresses the result as the derived morphism of `x` followed by the shifted inverse of `relativePushforwardSingleDerivedIso`. The last identification is the singleton coherence lemma `relativePushforwardSingleDerivedIso_inv`.

`relativeDerivedComplexSectionsPullback_single_fac` expands the definition of `pushforwardSingleDerivedSectionsComparison` and applies the lifted underlying additive cohomology functor. The final inverse singleton localization isomorphism cancels the forward singleton localization isomorphism. This factors the singleton comparison through the two source singleton transports and the actual complex-level derived-sections pullback.

`relativeSingleDerivedSectionsClass_pushforward` proves the corresponding equality of classes in the singleton derived-sections model. It applies the injective map given by singleton localization followed by the target sections/Hom comparison. This map is an isomorphism: singleton localization is an isomorphism and `relativeDerivedHomComparison_isIso` makes the comparison invertible. The preceding factorization and `relativeComparisonOnComplex_pullback` move the source class through the actual derived comparison square. The pushforward-singleton evaluation, `relativeComplexHomPullback_single`, and the target singleton evaluation then identify both images. In particular, the Ext-defined sheaf map is identified through its actual inverse-image and counit construction.

`relativeHAddEquiv_canonicalPushforward` translates that class equality back to relative module cohomology using `DerivedPlus.homologyIso` for the chosen injective resolutions. The target inverse and forward homology isomorphisms cancel. The source composite is precisely the definition of `canonicalPushforwardCohomologyMap`.

Finally, `relativeAbelianSheafCohomologyPullback` applies `relativeCohomologyPullback_coefficient` to the module-adjoint of `k`. Coefficient naturality of `relativeHAddEquiv` reduces to the identity-coefficient canonical-pushforward equality. On the sheaf side, `pullbackMap_naturality_left` and naturality of the actual sheaf adjunction identify the resulting map with `pushforwardMap` at the original coefficient arrow.

## Provenance

This is an internal proof about the existing relative module and sheaf constructions. Its inputs are the derived sections/Hom comparison, its complex pullback compatibility, the singleton evaluation and singleton Ext comparison imported through `RelativeDerivedHomPullbackExt`, and the existing canonical coefficient factorization. The argument specializes these constructions, cancels canonical isomorphisms, and uses coefficient naturality. No external literature or downstream Picard or family representability result supplies the proof.
