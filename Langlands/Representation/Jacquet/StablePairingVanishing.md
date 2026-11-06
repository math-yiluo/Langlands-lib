# Vanishing detected by the stable opposite-Jacquet pairing

Worker 480 derives this module from the published abstract stable evaluation
pairing. Its inputs are `D : Langlands.Jacquet.StablePairingData G`, a smooth
complex representation `ρ`, and the existing `D.Admits ρ hρ`. The group and
representation universes are independent. No reductive-group realization of
`D`, admissibility-to-`Admits` theorem, or rational-point construction is supplied.

`IsStablePairing.flip_injective` proves nondegeneracy of a stable pairing on its
opposite side. Given an opposite quotient class annihilated by every upper
class, `exists_open_stable_lift` and `exists_good_le` give a stable representative
`t` for a good compact open subgroup. The stable evaluation duality in the
`Admits.duality` field identifies the full algebraic dual of that stable image
with the stable image on the smooth contragredient. (The module originally
derived this duality from an `Admits.finite` field through the published
`compactCompression_stableEvaluationDuality`; Worker 937 replaced that field by
`duality` itself.) Every functional therefore evaluates to zero on `t`: its value
is the stable pairing of an upper class with the original opposite class.
Algebraic dual separation forces `t = 0`, and its quotient class is zero.

`upper_subsingleton_iff_opposite` applies this result and the existing
`IsStablePairing.injective` to the stable pairing supplied by
`exists_isStablePairing`. It says that the actual upper coinvariants of the
smooth contragredient vanish if and only if the opposite coinvariants of the
original representation vanish. Each coinvariant space is the published
trivial-character quotient; vanishing is expressed as `Subsingleton`.

`oppositeStableEvaluation` chooses one such published stable pairing and flips
it. It is an actual complex linear map from the opposite quotient to the full
algebraic dual of the upper quotient of the smooth contragredient.
`oppositeStableEvaluation_injective` proves that it is injective. No
surjectivity onto that full algebraic dual is asserted.

The provenance is internal: the only mathematical inputs are the published
stable pairing and stable-image evaluation duality, together with algebraic
dual separation. This supplies a conditional vanishing consequence used in
auditing the self-association proof. The actual rational contraction geometry,
the `Admits` input, and the analytic irreducibility argument remain obligations.
There is no additional use of classification, a geometric lemma, adjointness,
or cuspidal support.
