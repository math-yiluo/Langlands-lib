# Étale base change along the glued fibre product

`Langlands.Analytic.SaturatedAtlasPresentation.etaleBaseChange` proves the
unchanged `EtaleBaseChangeStatement.{u}`. For strong maps `f : X ⟶ S` and
`g : Y ⟶ S` between Hausdorff saturated presentations, if the localized image
of `f` is étale, so is that of `fibreProductSnd f g`. The complete ultrametric
normed base field, the spaces and the atlas indices have the common universe
`u` of the statement.

## Implemented proof

Apply [`etaleBaseChange_of_descent`](EtaleBaseChangeReduction.md) to two
published proofs at universe `u`:

1. `PresentedAffinoidAlgebra.finiteAffinoidAlgebraDescent` gives effective
   descent for finite Banach affinoid algebras along finite full-domain covers.
   The reduction uses this to obtain target locality of finiteness, which,
   together with the finite-piece étale criterion, gives a pullback with an
   étale second projection in the localized category.
2. `fibreProductPullback` identifies the localized square of the glued fibre
   product as a pullback of the same cospan. The two pullbacks are isomorphic
   over the second projections. Since `etale` respects isomorphisms, the
   reduction transfers étaleness to the image of `fibreProductSnd f g`.

Both premises of the reduction are discharged; the theorem has no additional
hypotheses. This proves the base-change clause for étale morphisms in the
scope of the Library statement, not the unramified, composition or ground-field
extension clauses of Berkovich, *Étale cohomology for non-Archimedean analytic
spaces* (1993), Corollary 3.3.8, printed p. 63 (PDF p. 60). The source is
registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
