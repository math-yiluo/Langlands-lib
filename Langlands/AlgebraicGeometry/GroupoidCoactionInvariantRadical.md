# Radical invariant ideals of Noetherian affine étale relations

Worker 148. This is internal support algebra derived from the published ring
étale relation, coaction annihilator, quotient-base-change constructions, and
Mathlib's reducedness results. It is a prerequisite for the geometric support
argument; it does not prove the host acyclicity statement.

The rings and schemes have arbitrary universe `u`. Coefficient modules in the
last result have independent universe `v`.

`EtaleReduced.isReduced_of_etale_to_field` proves that an étale scheme over
`Spec K`, for a field `K`, is reduced. On each member of its affine open cover,
the map on global sections is étale over the global sections of `Spec K`.
Transport the field structure through `Scheme.ΓSpecIso`. Étale algebras are
formally unramified, so Mathlib's
`Algebra.FormallyUnramified.isReduced_of_field` makes each affine coordinate
ring reduced. The affine reducedness criterion and the open cover then make
the original scheme reduced.

`EtaleReduced.geometricallyReduced_of_etale` applies this to every field base
change. Étaleness is stable under base change, and the second projection of
the specified pullback is therefore étale. This supplies precisely the
published `GeometricallyReduced` predicate.

`EtaleReduced.isReduced_of_etale_algebra` assumes commutative rings `B`, `C`,
an algebra `B → C`, a Noetherian reduced base `B`, and `Algebra.Etale B C`.
Pass to the induced map of spectra. It is étale, hence flat and geometrically
reduced. Mathlib's
`GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian` makes the
source spectrum reduced, since the base spectrum is reduced and locally
Noetherian. The affine reducedness criterion returns `IsReduced C`.

`EtaleReduced.isRadical_map_of_etale` assumes a Noetherian commutative ring
`B`, a commutative ring `C`, an étale ring map `f : B →+* C`, and a radical
ideal `I` of `B`. The quotient `B/I` is reduced and Noetherian. The published
`RingEtaleEquivalenceRelation.etale_quotientMap` gives the étale map from
`B/I` to `C/(I.map f)`. The preceding algebra result makes this target
reduced, so `I.map f` is radical.

`EtaleReduced.map_radical_of_etale` retains the same ring and étale-map
hypotheses and allows an arbitrary ideal `I`. The universal containment
`I.radical.map f ≤ (I.map f).radical` gives one direction. The image of
`I.radical` is radical by the preceding result and contains `I.map f`;
minimality of the radical gives the reverse direction.

`GroupoidCoaction.IsInvariantIdeal.radical` assumes a Noetherian base and
the unchanged `RingEtaleEquivalenceRelation t`. Both its source algebra map
and its target map `t` are étale. Commuting radical with the two ideal images
and using the given equality of those images proves that `I.radical` is
invariant whenever `I` is invariant.

`GroupoidCoaction.radical_annihilator_isInvariantIdeal` applies this to a
finite `B`-module `M` equipped with an actual `GroupoidCoaction t M`.
Noetherianity and finiteness supply finite presentation, so the published
`annihilator_isInvariantIdeal` applies. Taking its radical proves invariance
of the ideal of the reduced closed support. No hypothesis of geometric
acyclicity or affine descent is used.

`GroupoidCoaction.reducedSupportInvariantIdeal` records the actual radical
annihilator together with its radicality and invariance as an element of
`{I : Ideal B // I.IsRadical ∧ IsInvariantIdeal t I}`. Its value is exactly
`(Module.annihilator B M).radical`, as the reflexive value lemma states.
This defined support object retains the Noetherian, finite-module, and actual
coaction hypotheses used by the preceding proof.
