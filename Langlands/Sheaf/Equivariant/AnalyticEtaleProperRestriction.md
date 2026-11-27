# Proper restriction of compactly supported analytic étale sections

An étale analytic map from \(X\) to \(Y\) composes every small étale test over \(X\) with the map to \(Y\). `etaleRestriction` is the induced restriction of module sheaves. `etaleSectionsRestriction` evaluates a global section on the arrow from the substituted identity test of \(X\) to the identity test of \(Y\).

For Hausdorff underlying spaces and surjective projections from the independently chosen field-valued geometric points, `etaleRestriction_support_subset` places the underlying support on \(X\) inside the inverse image of the underlying support on \(Y\). A section with zero germ on \(Y\) vanishes after an étale neighborhood and hence on its open image. An open domain in \(X\) over the inverse image factors through that open image as an étale test over \(Y\). This makes the original restriction zero there.

If the underlying map is proper, the inverse image of a compact set is compact. This supplies the intrinsic support condition in `etaleCompactSectionsRestriction`, a natural map of the actual compact-section functors. The comparison on elements is the same map on global sections.

The construction uses the ordinary analytic étale site and compactly supported sections in Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993), §§4.1–4.2 and §5.1 (pp. 82–88 and 96–98). The support containment and its expression using field-valued points are derived here from étale lifting, openness and sheaf descent.
