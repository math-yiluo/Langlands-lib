# Derived proper restriction on analytic étale sites

Restriction of module sheaves along an étale analytic map is additive and exact. It acts by precomposition on presheaves, which preserves limits. Its right adjoint on sheaves is the direct image constructed by base change of the small étale site, so restriction also preserves colimits.

For a proper étale analytic map \(f\colon X\to Y\), with properness on the underlying topological spaces, the section map uses the proved support containment under restriction. `etaleCompactComplexRestriction` derives this section map along the exact restriction functor and gives \(R\Gamma_c(Y,F)\to R\Gamma_c(X,f^*F)\). The source and target are the existing compactly supported étale complexes, using field-valued geometric points satisfying the point axioms on Hausdorff spaces, with independently chosen fields in the same universe and surjectivity onto both spaces. `etaleCompactCohomologyRestriction` uses the natural homology identification to give the corresponding maps on the ordinary right-derived cohomology functors.

The analytic étale inverse image and compact support come from Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993), §4.1 and §5.1. Exactness here follows from the actual test-category adjunction. The derived comparison is the one induced by the natural transformation on compactly supported sections.
