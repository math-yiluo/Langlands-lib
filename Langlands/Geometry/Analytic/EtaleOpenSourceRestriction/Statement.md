# Étaleness under open-source restriction

`Langlands.Analytic.SaturatedAtlasPresentation.EtaleOpenSourceRestrictionStatement K`
applies to every complete ultrametric normed field `K : Type u` and an
independent ambient universe `v`. For any morphism `f : U ⟶ X` in
`LocalizedCategory.{u, v, v}` with `etale f` and any open subset `V` of
`localizedSpaceFunctor.obj U` with `hV : IsOpen V`, it asserts
`etale (domainι U ((presentationOf U).openDomain V hV) ≫ f)`.
Here `openDomain` constructs the analytic domain of `V`, `domainι` is its
canonical inclusion in the localized category, and `etale` is the
all-affinoid-pieces predicate of [EtaleSite](../EtaleSite.lean).
Étaleness of `f` and openness of `V` are the only hypotheses on the arrow
and the subset.

The proposition is an internal prerequisite for whole-site point-fibre
joint faithfulness, `AnalyticEtalePointFibersJointlyFaithfulStatement`
(module `Cohomology/AnalyticEtaleRestrictedInjectiveAcyclic/GodementReduction`).
Its intended deduction uses étaleness of
the canonical open-domain inclusion and closure of localized étale
morphisms under composition.
[Open-domain étaleness](../EtaleOpenDomains/Proof.lean) and
[localized étale composition](../LocalizedEtaleComposition.lean) supply
these two facts.
