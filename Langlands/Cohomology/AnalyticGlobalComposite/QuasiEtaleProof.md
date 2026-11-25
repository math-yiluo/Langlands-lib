# Berkovich's composite comparison for quasi-étale `G`-sheaves

The theorem
`Langlands.Cohomology.AnalyticGlobalComposite.analyticQuasiEtaleGlobalComposite`
proves the unchanged Library proposition
`AnalyticQuasiEtaleGlobalCompositeStatement X G ρ R`. For every natural
degree `n` it gives additive isomorphisms

`H^n(X(G), F) ≃+ Hom_D(R, RΓ(X{G}, F)[n])`

natural in the quasi-étale `G`-sheaf `F` of `R`-modules. On the right, `D` is
the derived category of smooth representations of `G`, and `R` denotes the
trivial smooth representation placed in degree zero. Naturality is exactly
the equation in the statement: the map induced by a sheaf morphism agrees,
under the isomorphisms, with postcomposition by its derived global-section
map shifted by `n`.

The theorem retains the statement's five universe parameters
`w, u, v, uL, z`, including an arbitrary `HasDerivedCategory.{w}` model for
smooth representations. The field is complete and ultrametric, the group is
topological and small in the coefficient universe, and the compact lift
system has finite equivariant refinements for the twisted quasi-étale
topology. These are precisely the published hypotheses. The result adds no
continuity, Hausdorff, or compactness assumption.

The proof specializes `smoothGlobalComposite` from
`AnalyticGlobalComposite.SmoothGlobalProof` to the additive functor
`quasiEtaleGSheafSections ρ R`. The existing theorems
`twistedQuasiEtale_hasSheafify` and `twistedQuasiEtale_enoughInjectives`
provide the required abelian category and injective resolutions. It chooses
the standard derived-category model for the quasi-étale sheaf category,
exactly as the definition of `quasiEtaleGSheafComplex` does, and installs
`quasiEtaleGSheafSections_preservesInjectiveObjects` from
`AnalyticConstantAdjunction`.

The generic comparison applies to an injective resolution `I` of `F`.
Smooth sections send its terms to injective smooth representations, giving
a bounded below K-injective complex. Resolution homology computes the
right-derived functor of sections followed by invariants. The natural
identification of invariants with maps from the trivial representation
turns it into Hom-complex homology; K-injectivity identifies that homology
with shifted morphisms in the derived category. The resolution comparison
then transports the target to the published global complex. Lifts of
sheaf morphisms to injective resolutions give the complete naturality
equation.

No further transport is needed in this specialization:
`quasiEtaleGSheafInvariantCohomology` is definitionally the right-derived
functor of `quasiEtaleGSheafSections ⋙ smoothInvariantsFunctor`, and
`quasiEtaleGSheafComplex` is definitionally
`DerivedPlus.derivedComplex quasiEtaleGSheafSections` with the specified
sheaf-category model. Thus the generic conclusion has exactly the type of
the published proposition.

The original source is V. G. Berkovich, *Etale equivariant sheaves on p-adic
analytic spaces* (unfinished 1995–1996 manuscript), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
§1.2, printed/PDF pp.4–5. Page 4 defines the global sections on `X(G)` and
the smooth global-section functor to discrete `G`-modules. Page 5 identifies
its open-subgroup invariants and states the composite spectral sequence.
The present theorem proves the derived-category composite identification
underlying that sequence. It does not construct the sequence itself. The
precise comparison of the Library's quasi-étale model with the source is
documented in the unchanged paired Markdown of `Statement`; the proof
uses the existing Library categories and functors throughout.
