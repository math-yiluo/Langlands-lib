# Actual analytic Godement terms and injective coefficient diagrams

This is an internal specialization of the actual twisted-site point-product
identification and the coefficient acyclicity reduction. It retains independent
universes `u`, `v`, `uL` and `z` for the ground field, analytic atlas data,
extension field and group. The coefficient ring and module carriers use
`W = max u (v + 1) uL`. The group is small in `W`, and the distinguished lift
system has the admissible refinements required by the actual locally discrete
coreflector. The supplied point axioms `h` are retained throughout.

`etaleCoefficientRestrictedSmoothPointProductFunctor` specializes the existing
`coefficientRestrictedSmoothPointProductFunctor` to the actual analytic étale
site. Its index is `ULift.{W}` of the actual `L`-valued point set, exactly as in
`etaleGodementPoints`. It applies the existing point product, actual right Kan
induction, locally discrete coreflector, inclusion and ordinary étale restriction.
The needed right Kan extensions follow from the existing analytic size theorem.

`etaleGodementCoefficientFunctor` includes an actual étale `G`-sheaf, restricts
it to the ordinary étale site and takes its actual fibers at those lifted points,
presented as a discrete diagram. `etaleRestrictedGodementPointProductIso`
specializes `restrictedSmoothGodementPointProductIso`: its source is exactly
`etaleGodementZeroFunctor` followed by `etaleGSheafRestriction`, and its target
is the coefficient functor followed by the actual restricted smooth point product.
This is a natural identification of both objects and maps.

`isZero_etaleCompactCohomology_coefficientRestrictedSmoothPointProduct_of_injective`
assumes positive compact cohomology vanishes on that point product for injective
coefficient diagrams and deduces it for arbitrary diagrams. The proof installs the
existing analytic local-smallness, sheafification, enough-injectives and right
Kan-extension instances and the actual `pointTopology L X`, then applies the
generic coefficient reduction. The support index is the unlifted actual point
set, with the existing `etalePoints L h`, and the section object is exactly
`etaleSelf X`. Thus the compact-derived functor is definitionally the existing
`etaleCompactCohomology`; no change of support theory is involved.

`analyticEtaleGodementCompactAcyclic_of_injectiveCoefficients` concludes the exact
published `AnalyticEtaleGodementCompactAcyclicStatement` from the displayed
injective-coefficient vanishing under its Hausdorff, point-surjectivity and
continuous-action hypotheses. For arbitrary input `F`, the coefficient reduction
applies to its actual coefficient diagram. The right-derived compact-sections
functor maps the actual Godement identification to an isomorphism, and zero
transports across it. The final input `F` has no injectivity premise.

The injective-coefficient analytic vanishing remains an explicit, unproved
hypothesis of these conditional results. This module does not prove the
unconditional analytic target `AnalyticEtaleGodementCompactAcyclicStatement`;
the Library has only conditional proofs of it. It assumes neither equivariant compact/global
comparison, parent restricted-injective acyclicity nor injectivity preservation by
ordinary restriction. The provenance is the stated categorical specialization;
no result is attributed to the analytic literature.
