# Uniqueness of the opposite dynamic parabolic: proof

Authors: Worker 135 and Worker 1650. The comparison argument is Worker 1650's;
Worker 135 assembles the exact theorem and its explanation from that comparison
and the independently proved relative-root negation theorem.

`Langlands.GroupScheme.oppositeDynamicParabolicUniqueness` proves the unchanged
`Langlands.GroupScheme.OppositeDynamicParabolicUniquenessStatement.{u}`.
For an arbitrary field `k : Type u`, a connected reductive group scheme `G`
over `Spec k`, and cocharacters `χ` and `χ'`, its premises are equality of
their dynamic centralizer subgroup functors and
`P(χ)(k) ∩ P(χ')(k) = Z(χ)(k)`. Its conclusions are
`P(χ') = P(χ⁻¹)` and `U(χ') = U(χ⁻¹)` as subgroup functors on every test
scheme, where `χ⁻¹` is `Dynamic.oppositeCocharacter χ`.

The Lean proof applies
`oppositeDynamicParabolicUniqueness_of_relativeRootNegation` from
`Dynamic/OppositeParabolicComparison` to `relativeRootNegation` from
`Rational/RelativeRootNegationProof`. Both retain the original universe `u`.
The latter theorem supplies the former's sole structural premise, so the
resulting exact theorem has no additional hypotheses.

The comparison first places both cocharacters in a common maximal split
torus. Equal centralizers make their images commute; the split-torus image
factorization of their product, followed by a maximal split extension, gives
the common torus. If an actual relative root were positive on both
cocharacters, its root subgroup would supply a nonidentity rational point
lying in both dynamic unipotent subgroups. The rational intersection premise
places this point in `Z(χ)(k)`, contradicting the trivial intersection of the
dynamic unipotent subgroup with its centralizer.

Rational centralizer-point detection identifies the roots pairing to zero
with the two cocharacters. Applying the preceding positive-root exclusion
to a root and its negative then gives opposite weak and strict signs.
The established relative-root sign inclusion criteria give both inclusions
for the parabolics and for the unipotent subgroups. Negating the torus
cocharacter represents `Dynamic.oppositeCocharacter χ`.

The imported unconditional negation theorem uses a reductive cocharacter
centralizer and the independently proved rank-one negation theorem for split
maximal tori. A splitting field for a containing maximal torus and the
established absolute-root restriction theorem descend this to actual relative
roots over the original field. Root symmetry is thus a proved input, rather
than a root-datum or root-system hypothesis.

This is an internal derived proof from the Library results named above. The
target's paired Markdown records its original-literature provenance; this
module makes no additional claim about those sources. No external structural
result remains as a premise. The field may be finite or imperfect, and the
relative-root system need not be reduced. The argument uses rational points
only for root-point detection and exclusion; the final subgroup-functor
equalities follow from the all-test sign criteria. No density assumption or
scheme-level intersection premise is added.
