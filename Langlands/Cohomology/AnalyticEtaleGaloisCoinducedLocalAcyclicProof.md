# Local acyclicity of coinduced Galois fixed sections

The theorem `analyticEtaleGaloisCoinducedLocalAcyclic` proves
`AnalyticEtaleGaloisCoinducedLocalAcyclicStatement` in
`Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic`.
An étale `G`-sheaf with `HasCoinducedGaloisFixedSections` has vanishing ordinary
higher direct images in positive degrees after restriction to the ordinary étale site,
under the Hausdorffness, continuity and instance hypotheses of the statement.

`pointedAnalyticGaloisRefinement` supplies the pointed relative refinements using
compact ordered frames. The relative-refinement bridge shrinks these covers over the
ambient base to obtain distinguished étale sources. The Galois–Cartan reduction then
uses coinducedness of the fixed sections and compatibility of finite group cohomology
with filtered colimits to obtain vanishing on the section germs. Those germs detect
the ordinary higher direct images.

The source for the local acyclicity argument is Vladimir G. Berkovich,
*Étale equivariant sheaves on p-adic analytic spaces*, Proposition 1.5.1, step (1′),
printed pp. 10–11. The retained `Equish_1996` manuscript is registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
SHA-256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
The comparison with completed-residue-field cohomology in the source is
Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
Propositions 4.2.2 and 4.2.4, printed pp. 87–88, registered as
`berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
Lean obtains the vanishing through the finite Galois covers and the Cartan criterion.
