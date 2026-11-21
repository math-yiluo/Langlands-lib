# Ground field extension preserves full atlas quasi-isomorphisms

`AffinoidAtlasPresentation.GroundFieldExtension.GroundFieldExtensionQuasiIsoStatement`
is a proposition about the actual chart-quotient map and bounded pullbacks
constructed by `compatibleMap`. Let `K` and `L` be complete ultrametric
normed fields and give `L` a `NormedAlgebra K L` structure. There is no
nontrivial-valuation or finite-degree hypothesis. The two field universes and
the original space and chart-index universes are independent.

For every compatible strong map `f` between indexed affinoid atlas
presentations over `K`, the target says that if `f.toStrongHom.IsQuasiIso`
holds, then `(compatibleMap K L f).toStrongHom.IsQuasiIso` holds. Here
`IsQuasiIso` includes an ambient homeomorphism and the full
`PresentedAffinoidAlgebra.Represents` property for the actual image locus
at **every** admissible source–target chart pair. It does not assert just a
homeomorphism of spectra or just that one pullback per chart exists. Neither
presentation is required to be saturated or globally Hausdorff.

This is the presentation-level step toward the ground field extension
functor on the localized analytic category. It uses the quasi-isomorphism
condition of Berkovich, *Étale cohomology for non-Archimedean analytic
spaces* (1993), Definition 1.2.9, printed p. 19 (PDF p. 16), and the ground
field extension of §1.4, printed p. 30 (PDF p. 27), registered as
`berkovich-1993-etale-cohomology`. The statement is derived: it expresses
preservation of that condition using the Library's compatible maps,
quotient charts and represented domains. The localized functor and the
comparison with analytification in Conrad, *Weil and Grothendieck approaches
to adelic points*, proof of Proposition 5.11(3), p. 19, are not part of this
target.
