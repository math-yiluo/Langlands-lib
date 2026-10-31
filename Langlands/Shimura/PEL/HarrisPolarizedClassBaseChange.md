# Pointed pullback of actual Harris polarized isogeny classes

This internal construction continues the actual object and tower pullbacks in
`HarrisPolarizedActionBaseChange` and `HarrisPolarizedTowerBaseChange`. It
constructs pointed pullback on ambient polarized rational-isogeny classes and
proves naturality for every compact-open transporter arrow at the original
Harris indices. The ambient classes here are the full polarized classes before
the Harris Lie-determinant and numerical-dimension restrictions.

`DualEvaluationData` packages dual-scheme, geometric, Poincaré-inverse,
evaluation and endomorphism-additivity construction inputs for a specified
actual abelian scheme. `PositivePullbackDualData` constrains that scheme to the
actual base change of the source action's abelian scheme. Its inputs do not
contain an independently supplied changed polarized action, level or quotient
map. The family of dual data is explicit; this construction does not prove
existence of that family or independence of its choice.

`levelDataBaseChange` uses the source's existing monodromy-fixed compatible
orbit to obtain a nonempty actual frame type. The existing constructor builds
the positive polarized pullback with its actual rational action and canonical
integral polarization, and the existing tower map pulls the orbit back at the
same original Harris index. No monodromy-fixed representative of the orbit is
required. The positive auxiliary left involution and Hodge form are exactly
those used by `hodgeLevelFunctor`.

`levelDataBaseChange_related` proves preservation of the actual polarized
rational-isogeny relation. Given a source rational unit and action isomorphism,
it uses the action pullback functor's image of that same isomorphism.
`IsRationalDualPullbackMultiple.integral_baseChange_of_naturality` proves the
changed geometric multiplier equation with the same rational unit. The
canonical dual-valued base-change map is the integral map in this equation.
The generic Tate square `weilAdelicLevelIsogeny_baseChange`, composed with the
pullback of the original orbit equality, proves the new orbit equality. Thus
no extra multiplier-preservation or orbit-preservation hypothesis is introduced.

`ambientClassBaseChange` is `Quotient.map` of this representative construction
and the proved relation preservation. `ambientClassBaseChange_mk` states its
value on each actual representative. `levelDataBaseChange_mapData` proves the
representative construction commutes with every arrow transported by
`hodgeLevelFunctor`. The constructed actions agree by proof irrelevance for
the frame-existence witnesses; equality of their level orbits follows from
naturality of `framedPositiveActionTowerBaseChange`. Quotient induction then
proves naturality of `ambientClassTowerBaseChange` between the existing
ambient polarized class towers reindexed by the original Harris level
functor. This covers subgroup-inclusion and Hecke transporter arrows as
instances of the stated naturality.

The named full polarization-stability and integral dual-naturality propositions
remain explicit, as do tensor/Picard inputs, the chosen dual family,
ordered-pair dual additivity on both bases, finite fibres, torsion, roots of
unity and the adelic coefficient comparison. No flatness condition on the
base map is imposed. The construction is pointed, using the target geometric
point and its composite on the source. It does not assert successive-base-change
coherence, determinant or dimension preservation, an unpointed moduli functor,
scheme representability, canonical models or coefficient descent.

The provenance is an internal derivation from the imported constructions and
the quotient universal property, rather than a new translation of an original
literature statement. The existing imported Harris definitions retain their
original-source conventions and citations.
