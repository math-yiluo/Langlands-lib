# Faithful central-quotient actions and inner discrepancy cocycles

This derived supporting construction applies over any scheme `S`. Let
`p : G ⟶ A` be a `RelativeRoot.IsFppfQuotient (center G) p` and let
`c : AutomorphicAction A G` restrict along `p` to conjugation on `G`.
The full scheme-theoretic centre is essential to the hypothesis.

`AutomorphicAction.hom_ext_of_fppf_quotient_lift` checks equality of two
morphisms from a test scheme after pulling back an fppf homomorphism along
one point of its target. The projection of that pullback is an effective
epimorphism, hence an epimorphism. This version uses flatness, surjectivity
and local finite presentation. It does not require quasi-compactness or
affineness.

`AutomorphicAction.centralQuotient_act_lift` evaluates the specified action
at a quotient point with a lift, using the restriction equality.
`centralQuotient_action_kernel` proves that an acting point which acts
trivially after every refinement is the identity. After an fppf lift, the
lift commutes with every group point on every refinement, so belongs to
`center G`. The quotient kills it by the equality of its actual kernel
range with that centre. Equality descends by the preceding local-lift
lemma. `centralQuotient_action_isFaithful` uses the existing
`AutomorphicAction.isFaithful_of_kernel` to conclude faithfulness.

For a `LocalGroupIso G H U` with pointwise inner discrepancy,
`LocalGroupIso.innerCocycleOfCentralQuotient` constructs a natural
`A`-valued cocycle from that discrepancy. It applies the existing
`LocalGroupIso.innerCocycle` with the faithfulness proved here. Thus
naturality and the cocycle law are proved rather than supplied as
additional inputs. The accompanying `hasDiscrepancy` theorem verifies the
original discrepancy equation.

The provenance is a general-base adaptation of the published field
construction in `Langlands.GroupScheme.Rational.InnerDiscrepancy`, using
the explicit fppf central-quotient hypotheses that already occur in
Conrad's *Reductive group schemes* (2014), Proposition 7.2.12,
pp.258–259, and the published relative quasi-split-inner-form targets.
No quasi-split existence theorem or torsor-vanishing theorem is asserted.
