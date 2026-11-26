# Pointed analytic Galois refinements by ordered frames

The theorem `Langlands.Analytic.SaturatedAtlasPresentation.pointedAnalyticGaloisRefinement`
proves `PointedAnalyticGaloisRefinementStatement`. Start with a compact Hausdorff analytic
domain through the marked source point. Choose it over a Hausdorff open of the target.
Its map to the original target is quasi-étale, and its restriction over a neighbourhood
of the image point is étale.

Lift the image point to a complete algebraically closed value field. The geometric fibre
of the compact domain is finite, by applying finiteness on the étale slice where the
ordinary fibre is compact. Its cardinal is positive by the pointed lifting theorem.
Enumerating this fibre produces a distinct ordered frame of that length. The same pointed
lifting theorem on the next fibre power shows that no longer frame lies over the image
point.

The set of base points admitting a frame of the chosen length is open in the étale slice.
The longer distinct frames form a relatively closed subset over the same slice. Take its
closure in the compact fibre power. The closure has no point over the marked base point
and has closed image in the Hausdorff base open. Remove that image to obtain an open on
which the full ordered frames form a Galois cover under coordinate permutations.

Choose a point over the marked base point in this cover and restrict to a deck component
for its stabilizer. The component has a singleton ordinary fibre there. Identify its
image with an open domain in the original target using the nested-domain isomorphism.
The first coordinate gives the required map to the source of the original étale arrow.

The proof gives the pointed Galois refinement used in the finite étale germ argument of
Vladimir G. Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
Theorem 3.4.1 and Proposition 4.2.4, printed pp. 65 and 87–88. The source is registered as
`berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The ordered-frame proof constructs the cover directly from compact fibre powers and
geometric fibres.
