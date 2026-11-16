# Étale descent of admissible relative derived subgroups

This internal supporting module develops descent for the unchanged
`RelativeDerived.IsAdmissible` predicate. It retains
`RelativeSemisimpleFppfPerfectStatement` as an explicit premise. It does not
prove perfectness or unconditional relative derived-group existence.

Admissibility is invariant under replacing a subgroup source by an isomorphic
group scheme. Equal all-test ranges of closed inclusions therefore transfer
admissibility. With the perfectness premise, the published local-commutator
description identifies admissible ranges even when their ambient groups are
related by an isomorphism: local commutators map in both directions.
Applying this comparison to the two pullbacks on each cover overlap gives
the all-test matching condition for effective closed-subgroup descent.

These are internal consequences of the published admissibility predicate,
its commutator reduction, and the covering-family descent APIs. No new
external structural assertion or additional hypothesis on the base is used.

## Construction and proof

For an arbitrary scheme `S`, a reductive `G` over `S`, and an arbitrary
étale covering family `𝒰`, suppose a closed inclusion `d i` into the pullback
of `G` is admissible for each cover member. Here admissible has exactly the
published meaning: closedness, normality on every relative scheme test,
relative reductivity, semisimple geometric fibres, and a represented fppf
quotient which is a relative torus.

`RelativeDerived.admissibleRepresentativeEtale` constructs a closed
representative of `CoverDescent.subgroup 𝒰 (fun i => range (d i))` and proves
its inclusion admissible. The global subgroup condition requires membership
after every restriction to every cover member. The preceding overlap argument
and `CoverDescent.closedRepresentativeEtale` make this functor an actual closed
subgroup scheme. Its pullback range on each cover member is the original local
range. Closed subgroup representatives with equal ranges have isomorphic
sources, so `IsAdmissible.of_range_eq` recovers the full local admissibility
certificates for the constructed global inclusion.

Smoothness descends along the étale covering family. The global subgroup
is affine over `S` because its inclusion is closed and `G` is affine over `S`.
Normality follows directly from the definition of the global subgroup condition
and local normality on all relative scheme tests.

The helper `isSemisimple_geometricFiber_of_baseChange_at` reflects
semisimplicity at a point `s` from any point `t` over `s`, without imposing
any condition on that base change. It uses the residue-field map to choose
a compatible embedding of algebraic closures. Pullback coherence identifies
the extension of the geometric fibre at `s` with the geometric fibre at `t`;
the published arbitrary-field-extension reflection theorem then applies.
Every base point has a lift to some member of `𝒰`. This gives semisimplicity
of all geometric fibres of the global subgroup, and their connected reductivity
supplies the fibre clause of relative reductivity.

For the torus quotient clause, choose each local torus quotient of the
recovered local inclusion. Relative tori are affine over their bases.
`NormalQuotient.exists_affine_fppfQuotient_of_etaleCover` descends these
quotients to an affine represented fppf quotient over `S`. Each pullback of
the global quotient is isomorphic to the corresponding local torus quotient
by `FppfQuotientComparison.iso`. The quasi-compactness required for this
comparison follows from affineness of the source structure map and
quasi-separatedness of the affine target structure map. It does not require
the base or cover to be quasi-compact. Finally `RelativeTorus.IsTorus.of_etaleCover`
proves that the global quotient is a relative torus.

`RelativeDerivedAdmissibleEtaleDescentStatement` is the Prop-valued statement
that these local existence witnesses imply a global admissible inclusion,
under the explicit premise `RelativeSemisimpleFppfPerfectStatement`.
`relativeDerivedAdmissibleEtaleDescent` proves it by choosing the local
witnesses and applying the construction. All declarations are polymorphic
in the universe `u`.

## Scope and provenance

This unit is internal glue for the relative derived-group existence task.
It combines the unchanged `RelativeDerivedInputs` and `RelativeDerivedReduction`
interfaces with published effective closed-subgroup descent, affine normal
quotient descent, semisimple field reflection and relative-torus locality.
Its geometric-fibre comparison follows the published
`IsRelativeUnipotentRadical.geometricFiber_of_baseChange_at` construction.
There is no new literature assertion; these are consequences of those
published definitions and proofs.

Perfectness is used only to obtain matching ranges on the cover. The unit
supplies neither that premise nor the local admissible subgroups. Both
remain inputs for any application to the unchanged unconditional
`RelativeDerivedGroupExistenceStatement`. There are no quasi-compactness,
noetherianity, reducedness, splitness or characteristic hypotheses on `S`.
