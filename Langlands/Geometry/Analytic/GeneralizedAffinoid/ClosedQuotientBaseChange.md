# Actual closed quotients under bounded affinoid base change

Worker 1685 constructs a bounded equivalence between the actual affinoid pushout
of a presented closed quotient `A → A/J` along any bounded affinoid algebra map
`f : A → B` and the presented quotient of `B` by the closed extension
`f.closedIdealMap J`. Both algebras use their stored quotient norms. The
coefficient field is complete, normed and ultrametric; arbitrary positive radii,
trivial coefficient valuations, nonreduced or zero algebras and empty spectra
remain permitted.

This is internal derived infrastructure from the actual bounded affinoid pushout,
`ClosedQuotient` and Worker 1582's closed-ideal extension construction in
`FiniteDomainIdealDescent`. The latter unchanged supporting pair is reused and
credited. No new assertion from the original literature is used: the result is
proved by the two constructed bounded quotient universal properties.

The new quotient map of `B` annihilates `f(J)`, so its composite with `f` descends
to `A/J`. These two bounded maps define `pushoutToChangedQuotient`. Conversely,
the actual right pushout leg annihilates `f(J)` by the pushout equation and the
kernel of `A → A/J`. Continuity makes its kernel closed. The closed-extension
adjunction therefore proves that it annihilates all of `f.closedIdealMap J`;
bounded quotient descent constructs `changedQuotientToPushout`.

The two composites are the identity as entire bounded maps. For the composite on
the pushout, the right-leg equation is immediate from the quotient lift
equations; equality on the left leg follows by precomposing with the surjective
original quotient and then using the pushout equation. The full pushout
uniqueness property finishes the proof. For the reverse composite, surjectivity
of the changed quotient map suffices.

`pushoutEquiv` packages these two explicitly bounded inverse maps. Its
injectivity, together with the unchanged right-leg equation, proves
`ker_rightMap`: the actual right pushout leg has exactly the closed extended
ideal as kernel. Finally, the inverse equivalence is admissible because it has
the constructed bounded section. Composing it with the admissible presented
quotient map proves `rightMap_isAdmissibleEpi`. Thus both surjectivity and positive
two-sided comparison with the actual quotient seminorm are conclusions.

The proof uses no flatness theorem, open mapping theorem, strict-radius
specialization or ideal-effectiveness assumption. In particular, this unit
supplies local quotient identification after a global ideal is given; it does
not prove that a compatible finite family of local ideals descends.
