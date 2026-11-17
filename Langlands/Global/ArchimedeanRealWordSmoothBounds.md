# Real words and supplied orbit derivatives

This internal comparison specializes `ArchimedeanRealWordBounds` to a supplied
representation π by bounded complex operators on a normed complex space E.
It uses a model with corners I for the group, a complex algebra action A of
the actual archimedean enveloping algebra on an algebraic space V, a complex
linear map j from V into E, and a map ζ from the actual real Lie algebra to
the model vector space.

The explicit hypothesis is the generator identity, for every real direction
X and every original vector v: applying j after the actual generator action
is the orbit derivative of j(v) in direction ζ(X). This hypothesis is neither
constructed nor inferred from an invariant positive form.

`map_realEnvelopingWord_eq_iteratedLieDerivative` proves the identity for
every real word by list induction. Multiplicativity of the enveloping action
and compatibility on all original vectors give the cons step. In particular,
the proof does not need linearity of orbit differentiation on arbitrary E.

`sum_norm_enveloping_le_iteratedLieDerivatives` combines this identity with
the algebraic finite-word norm bound. It maps the finite word family through
ζ and bounds repeated image terms by the full nonnegative image sum. Its
constant includes the cardinality of the original family, so it requires
no injectivity assumption on ζ. The word family and nonnegative constant
are uniform over the original vector.

The conclusion is a norm inequality on j(V). No continuity or smoothness of
π, smoothness or density of j(V), Hilbert structure, globalization, or
extension of a functional is asserted. Such properties require separate
hypotheses and proofs in applications. The construction uses the published
orbit-derivative definitions and the internal real-word spanning estimate;
it is a derived comparison, not an additional claim from the literature.
