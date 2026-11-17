# Joint faithfulness of analytic étale field-valued point fibres

This internal derived proof establishes the existing
`AnalyticEtalePointFibersJointlyFaithfulStatement` in `GodementReduction`.
The base field, space and extension field retain their independent universes.
The hypotheses are precisely the supplied point axioms, Hausdorffness of the
base analytic space and surjectivity of its field-point projection, with the
original module coefficient ring and universe. No analytic equivariant
comparison theorem is used.

The proof first obtains surjectivity of the field-point projection on every
object of the base's actual étale site. It applies
`pointProjection_surjective_on_etale_of_openSourceRestriction`, whose
complement-cover and fibre-isolation argument is described in
`AnalyticEtalePointLifting.md`. The published `etaleOpenDomainStatement`
supplies étaleness of open domains of the base. For an arbitrary étale object,
the same published theorem supplies étaleness of each open-domain inclusion
in its source. The published `etale_comp` composes that inclusion with the
object's structure map. Thus both geometric premises of the lifting helper
are discharged, and no additional geometric assumption remains.

Finally,
`etalePointFibers_jointlyFaithful_of_objectwise_surjective` uses these
objectwise surjections to prove joint faithfulness of the actual sheaf-fibre
functors. Its proof detects sections on every étale object by equality in the
filtered point-fibre colimits and the sheaf condition, then applies this to
the values of the two sheaf morphisms. This establishes detection on the whole
site, as required by the fixed target.
