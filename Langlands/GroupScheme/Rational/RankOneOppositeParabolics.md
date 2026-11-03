# Proper opposing rank-one parabolics and a rational normalizer

This derived construction works over an arbitrary field and universe with the
actual integral character and cocharacter lattices and all-test subgroup
functors. It combines the contracting-subgroup action, the ground-field radical
criterion, cyclic-root minimality and rational conjugacy correction.

`Dynamic.parabolic_eq_top_iff_centralizer_eq_top_of_torusActionUnipotence`
retains `RelativeRoot.TorusActionUnipotenceStatement` as an explicit hypothesis.
Apply it to the actual multiplicative-group conjugation action on the canonical
closed representative of the contracting subgroup. That representative has no
zero Lie weight, is smooth and connected, and is therefore unipotent under the
supplied hypothesis. If the parabolic is full, its contracting subgroup is a
smooth connected unipotent normal subgroup. Triviality of the ground-field
unipotent radical kills it. The limit decomposition then identifies the
parabolic with its centralizer. The reverse implication is the existing
constant-orbit inclusion.

`Dynamic.parabolic_ne_top_of_root_pairing_ne_zero` deduces properness from a
single actual root with nonzero integral pairing. A full parabolic would make
the cocharacter central by the preceding criterion. The published central
restriction theorem would then make that root's composite character zero,
contradicting its nonzero pairing. This does not require the negative character
to be a root. Applying the result to `ν` and `-ν` proves properness of both
opposing parabolics using the same root.

`SubgroupConjugate.le_comap_of_isRepresentedBy` records the passage from an
equation of actual representative inclusions to subgroup-functor containment
after pullback by inner conjugation. It lifts an arbitrary test point through
the first representative and uses the supplied source isomorphism and inclusion
equation to exhibit its conjugate in the second.

For the remaining construction the ambient group is smooth, connected and
affine with trivial ground-field unipotent radical. Its chosen torus embedding
is maximal split. Every actual relative root is an integral multiple of a
specified actual root `a`, and `ν` pairs positively with `a`. The supplied
closed representatives `P` and `Q` of the two opposing parabolics are both
smooth and connected. These representative hypotheses remain explicit.

`RelativeRoot.isMinimalPseudoParabolic_opposing_rankOne` combines the derived
properness with arbitrary-cocharacter cyclic-root minimality. For the negative
parabolic, use cyclic direction `-a` and cocharacter `-ν`; their pairing is the
same positive integer. Every root is also a multiple of `-a`. No assertion that
`-a` is a root is used. Smooth maximal-split-torus conjugacy remains an explicit
hypothesis inherited from that minimality theorem.

`RelativeRoot.rankOneOppositeParabolicNormalizer` additionally assumes
`MinimalPseudoParabolicConjugacyStatement`. Apply it to the two minimal
pseudo-parabolics. The chosen maximal split torus lies in both parabolics on
every test. The published normalizer correction therefore changes the rational
conjugator by a point of the negative parabolic so that it normalizes the torus.
The result is an actual rational normalizer point together with an actual
isomorphism `P ≅ Q` and the equation identifying their inclusions after
conjugation.

`rankOneOppositeParabolicNormalizer_moves_root` converts this equation to
all-test parabolic containment and applies the existing positive-Lie-weight
root-movement theorem. It proves that the constructed normalizer does not fix
`a`. The proof uses an actual nonzero Lie vector and requires no nonidentity
ground-field point in a root subgroup.

This unit is an internal deduction from the named Library APIs and the included
contracting-action and cyclic-minimality helpers. The torus-unipotence,
maximal-split-torus-conjugacy and minimal-pseudo-parabolic-conjugacy propositions
are explicit inputs, not proved here. It does not establish full root-kernel
centralization, an integral coroot, a root sign, or reflection existence.
