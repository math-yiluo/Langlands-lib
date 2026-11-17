# The Weyl criterion for inner automorphisms normalizing a split maximal torus

Worker 838. Internal support for `InnerFormStarActionStatement`, derived from the published
split Weyl comparison, pinning base change, and fppf-local innerness interfaces. Its
mathematical source is Conrad, *Reductive group schemes* (2014), Proposition 7.1.6 and
the discussion on pp.242–243: the inner subgroup is the kernel of the action on based
root data. This module treats automorphisms that normalize the supplied split maximal
torus, and expresses the kernel condition as Weyl membership on the full root datum.

The preliminary lemmas `IsAdjointQuotient.isFppfQuotient` and
`IsAdjointQuotient.innerAction_restrict` expose the full-centre quotient condition
and the conjugation restriction of the published field adjoint action. The first
assembles fields of the quotient interface; the second checks the action at the
two universal points and uses the published lifted-action equation.

Over an algebraically closed field, `IsFppfLocallyInner.exists_innerIso_of_isAlgClosed`
chooses a rational point of the supplied nonempty fppf cover and specializes the
all-refinement conjugation equation. For a general field, `SplitPinning.mem_weylGroup_of_locallyInner`
pulls the automorphism and pinning to the algebraic closure, realizes the resulting
conjugation on the root datum by a Weyl element, and transports that element back using
the canonical root-datum equivalence. This does not require a smooth centre.

Finally, `SplitPinning.exists_adjointPoint_iff_mem_weylGroup` combines this necessity
with the published sufficiency theorem `SplitPinning.exists_adjointPoint_of_weylImage`.
Its hypotheses include a split pinning, a supplied actual adjoint quotient, a torus
normalizing square, and a full root-datum automorphism with the specified character
map. It quantifies over arbitrary fields and universes; it constructs no global map
from all automorphisms to based root-datum automorphisms.

`SplitPinning.InnerWeylCriterionStatement` is the explicit Prop-valued definition
of the final criterion, quantified over every supplied adjoint quotient and
compatible automorphism, torus isomorphism, and root action. The theorem
`SplitPinning.innerWeylCriterion` proves this definition using
`exists_adjointPoint_iff_mem_weylGroup`; its parameters and conclusion are exactly
the ones described above.
