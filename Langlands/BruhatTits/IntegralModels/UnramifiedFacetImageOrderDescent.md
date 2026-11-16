# Descent of actual facet-image order

This internal unit connects the actual quotient images over the original residue field to those over the maximal-unramified integers. It combines the published coefficient comparison isomorphism for reductive images, fpqc reflection of represented subgroup containment, algebraic reflection of parabolicity, and the preceding conditional upstairs facet-image order theorem. It makes no new original-literature assertion. All statements and proofs are at arbitrary universe `u`.

The general coefficient results concern two relative component source models mapping compatibly into a common target over a local domain `R`, with a compatible local coefficient extension `R → A` and fraction-field extension `K → L`. A special-fibre quotient `Q` is supplied. No reductive-quotient hypothesis is needed for these coefficient comparisons.

`RelativeComponentModelHom.reductiveImage_range_baseChange` identifies the residue-field base change of the actual quotient-image subgroup functor with the actual quotient image of the base-changed comparison and quotient data. The proof uses the already constructed `reductiveImageBaseChangeIso`, whose homomorphism preserves the actual inclusions into the base-changed quotient. Precomposition with this isomorphism leaves the all-test range unchanged.

`reductiveImage_le_iff_baseChange` reflects and preserves inclusion of these actual quotient-image subgroup functors. The residue extension is faithfully flat and quasi-compact. The image on the right is represented by its closed schematic-image inclusion, so `SubgroupFunctor.baseChange_le_range_iff` applies. The equality specialization `reductiveImage_eq_iff_baseChange` applies the order equivalence in both directions.

When the residue-field extension is algebraic, `hasParabolicReductiveImage_of_baseChange` reflects parabolicity. The image comparison isomorphism first transports the supplied upstairs parabolic inclusion to the base change of the original closed image inclusion. The proved `IsParabolicSubgroup.of_baseChange_of_algebraicExtension` then descends it.

For the unramified specialization, `B` is valuation building data of an affine group scheme `G` over a nonarchimedean local field `F`. The supplied maximal-unramified building `C` is for the actual base change of `G`, and `E` is a zero datum. The point and apartment maps satisfy the same apartment axioms, common-apartment, equivariance, compatibility and exact facet-restriction hypotheses as the preceding image-order unit.

The two original source models and their compatible maps `φ` and `ψ` are over `𝒪[F]`. Their neutral models after actual maximal-unramified base change are characterized by the zero fixers of the images of full downstairs facets `Fc` and `Fd`. Both source integral-point groups are required to contain the upstairs target congruence subgroup. Assume no inversions, that `Q` is a reductive quotient, and that the two actual special-fibre images after base change are parabolic.

Under these explicit hypotheses, `reductiveImage_le_iff_descendedFacetPrecedes_of_unramified` proves that inclusion of the original actual quotient images is equivalent to `Fd ≺ Fc`. The general coefficient-order equivalence passes to the actual extended images. The preceding upstairs theorem then recovers reverse downstairs incidence. The quotient is reductive after base change by the published coefficient theorem.

`hasParabolicReductiveImage_of_unramifiedSpecialFibre` also proves that each original actual quotient image is parabolic. It first passes the upstairs special-fibre parabolic image through the reductive quotient and then descends quotient-image parabolicity along the algebraic unramified residue extension. The Henselian and algebraically closed residue-field properties used upstairs are supplied by the proved arithmetic of the maximal-unramified integers. `HasUnramifiedDescendedQuotientImageOrder` packages parabolicity and the order equivalence, and `hasUnramifiedDescendedQuotientImageOrder` proves it.

The module leaves no inversions, the two upstairs congruence containments, and upstairs special-fibre parabolicity as premises. It does not construct models, prove attainment of every original residue-field parabolic, or assert the full host bijection.

The local coefficient, tower, and residue-field instances have explicit module-specific names so this module can be imported together with the independent neutral-model descent interfaces. Their types and definitions are unchanged.
