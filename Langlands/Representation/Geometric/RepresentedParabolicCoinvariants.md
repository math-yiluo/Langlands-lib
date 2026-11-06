# Normalized coinvariants on the represented parabolic

This internal construction extends the actual normalized Jacquet quotient to
representations of the parabolic point image itself and identifies its
restriction from ambient representations with the published
`leviJacquetFunctor`. It works in
`Langlands.Aubert.General.RepresentedParabolic`.

The construction serves the support-quotient step of Renard,
*Représentations des groupes réductifs p-adiques*, 2026 version, VI.5.1,
printed pp.163–164 / PDF pp.169–170: the support spaces are representations
of the target parabolic before taking its radical coinvariants.
The normalized Jacquet convention is the one already implemented by the
published represented-parabolic functor. No geometric-lemma assertion
is used as a premise.

`parabolicRadicalPoints` is the literal radical image in the ambient group,
viewed as a subgroup of the literal parabolic image. The actual semidirect
decomposition proves it normal. `leviToParabolicPoints` is the original
Levi point map, with its codomain restricted to the parabolic image.

`leviInverseHalfCharacter` pulls the existing ambient inverse half Haar
character back along `leviPointsEquiv`. Its kernel is open by continuity
of that homeomorphism. Thus it is the same normalizing character used by
`leviJacquetFunctor`, with domain the Levi's own rational points.

`leviParabolicCoinvariantsFunctor` first forms the actual quotient by the
trivial-character radical relations for an arbitrary algebraic
representation of the parabolic image. Normality permits the whole
parabolic to act on this quotient. The functor then restricts the action
along the actual Levi point map and twists by the just-defined inverse
half character. Its maps are the original intertwiners descended to the
quotients. The map-on-classes lemma gives precisely `[x] ↦ [f x]`.

`leviParabolicCoinvariantsRestrictionIso` compares this construction after
restriction of an ambient smooth representation with its published actual
normalized Jacquet functor. The topological subgroup equivalence
`subgroupOfContinuousEquiv` identifies the nested radical with its ambient
point image without changing a point. `Jacquet.Localization.transportEquiv`
therefore identifies the two quotients by sending a class to the class of
the same vector. This equivalence intertwines both actual normalized Levi
actions. Its naturality follows by applying the same original intertwiner
to each vector representative.

The field and representation carrier universes are independent. The
construction uses the canonical ambient and Levi point topologies,
the represented parabolic, rational Levi, geometric radical and matching
multiplication isomorphism, and the ambient local compactness and
nonarchimedean group assumptions of the existing functor. It imposes no
local-field, representation dimension, length, admissibility or
irreducibility condition.

This module does not assert exactness, identify successive support
quotients, or cancel the moduli of different radicals. Those remain
separate obligations in the normalized geometric lemma.
