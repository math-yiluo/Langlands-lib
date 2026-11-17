# The affine split torus and Borel conjugacy clause

Worker 591, using Worker 686's connected root-datum and root-weight-line
constructions. This internal derived assembly proves the full affine
conjugacy clause of Conrad, *Reductive group schemes* (2014), Proposition
6.2.11(2), p.211, with exactly the original connectedness and actual
line-bundle Picard hypotheses. It retains no root datum, root-line,
vector-series or local isomorphism hypothesis.

Let `S` be any connected affine scheme with every actual `LineBundle S`
trivial, and let `G` be reductive. For two closed split fibrewise maximal
tori, whose finite coordinate index types may differ,
`connectedPicardAffineSplitTorusBorelConjugacy` proves existence of a section
of `G(S)` carrying the first represented torus range onto the second.
For any two relative Borels containing respectively those tori, it also
proves existence of one section carrying both the torus and Borel ranges
to their targets.

The proof moves to the canonical ring model `Spec Γ(S, ⊤)`. Connectedness
transports across the affine isomorphism, and actual line-bundle triviality
transports using the retract lemma. Closedness and fibrewise maximality of
the coordinate torus maps persist after the actual base change and canonical
coordinate isomorphisms. The connected Picard-trivial split-coordinate
construction supplies the Borel vector-series presentation for both model
tori. The pair-only spectrum conjugacy theorem then gives a torus
conjugator, whose actual point transports to `S`. The simultaneous conclusion
uses the arbitrary affine-base conjugacy theorem with the first model
presentation and the originally supplied Borels.

`picardAffineSplitTorusConjugatingPoint` chooses a torus conjugator, and
its specification is the full represented-range equality under the actual
inner automorphism. The theorem also contains the complete simultaneous
Borel conclusion. The general-base isomorphism clause of the parent target
is a separate remaining obligation.
