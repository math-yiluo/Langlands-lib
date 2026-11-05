# Rational double-coset realization for corrected supports

This internal adapter constructs `standardParabolicDoubleCosetEquiv` from
clause four of the published `StandardParabolicPointsStatement`, at exactly the
finite sets of actual simple relative roots used by the rational Aubert family.
The statement is an explicit input; this module does not prove it or the assigned
`RationalCorrectedSurvivingSupportStatement`.

The representative-preservation lemma follows from the chosen equivalence's
specification. Surjectivity gives an actual normalizer representative of every
parabolic double coset. At the empty left root set this proves
`isBruhatCover_of_standardParabolicPoints` directly. This deduction uses neither
a separate rational Bruhat statement nor a standard-parabolic endpoint statement.
It needs only the elementary inclusion of scheme-normalizing points into the
normalizer of the torus point image.

For the actual quotient comparison,
`parabolic_doubleCoset_mk_eq_iff_of_standardParabolicPoints` first reflects equality
through the chosen equivalence, then transports both Weyl subgroups through
`weylEquiv`. The theorem `weylEquiv_map_schemeStandardWeyl` and the supplied
`actualLeviWeylIdentification` identify those images with the literal generated
Coxeter subgroups. The input equalities `HasPointNormalizerComparison` and
`HasPointCentralizerComparison` remain explicit. Both Weyl quotients retain the
full centralizer denominator.

The generic helpers are elementary deductions from imported constructions.
`exists_doubleCoset_rep_of_equiv` uses equivalence surjectivity, quotient induction,
surjectivity of the normalizer homomorphism and `DoubleCoset.eq`.
`IsTitsSystem.doubleCoset_mk_eq_iff` uses the independently published
`IsTitsSystem.exists_doubleCoset_equiv` and equivalence injectivity.
`doubleCoset_mk_eq_map_iff` transports the two subgroup witnesses of
`DoubleCoset.eq` along a multiplicative equivalence.

The rational conclusions hold over arbitrary fields at universe `u`, with a
connected reductive group, a maximal split torus and a generic cocharacter as
required by the supplied points statement. They require no local-field topology,
root-length comparison, positive-simple comparison or nonempty root set. They do
not prove fixed-order prefix openness, any closure/length comparison, the
standard-parabolic points statement itself, or any paused structural target.
No premise is added to the exact rational surviving-support target and its
Lean/Markdown import closure is unchanged.
