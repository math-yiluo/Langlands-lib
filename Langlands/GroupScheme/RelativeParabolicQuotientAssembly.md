# Relative parabolic quotient assembly with explicit inputs

This internal construction assembles a proper quotient from five explicit
universe-polymorphic inputs. It does not prove those inputs or the unconditional
relative parabolic quotient existence statement.

`RelativeParabolicQuotient.ProperAmbientCriterion` records the generic
properness implication used here. For any base scheme `S`, an object `X` of
`Over S` is assumed smooth, separated and quasi-compact over `S`. It admits a
monomorphism over `S` into `Y`, whose structure map is proper and locally of
finite presentation. For every field and every actual field-valued map to `S`,
the actual pullback of `X` is proper and connected. The implication concludes
properness of `X` over `S`. This proposition is an explicit input, not a proved
criterion in this module.

`ProperHomogeneousQuotient i` stores an actual `HomogeneousQuotient i` together
with properness of its structure morphism.
`properQuotientOfStatements` constructs this data over every commutative ring
`R`. Its geometric hypotheses are those of the published relative parabolic
quotient existence target: `G` is reductive, the actual subgroup map `i : P ⟶ G`
is a closed immersion, `P` is smooth, and every algebra-valued field base change
of `i` is parabolic.

The construction additionally assumes `RelativeSelfNormalizerStatement`,
`ParabolicSelfNormalizerStatement`, `ParabolicDynamicStatement`,
`SelfNormalizingProperAmbientStatement`, and `ProperAmbientCriterion`.
The first four inputs feed the normalizer reduction's
`properAmbientOfStatements`, yielding an actual proper, locally finitely
presented ambient scheme and an exact-coset map from `G`. The published
`quotientEmbeddingOfMapKernel` then constructs the actual homogeneous quotient
and its monomorphic map into that same ambient scheme.

Smoothness of the ambient group descends through the smooth surjective quotient
projection, by `RelativeParabolicQuotientFibers.smooth`. The homogeneous quotient
already retains separatedness and quasi-compactness of its structure map.
At every field-valued base point, `parabolic_atFieldPoint` converts the target's
algebra-valued parabolicity hypothesis to the actual base change.
`proper_fieldBaseChange` and `connectedSpace_fieldBaseChange` prove properness
and connectedness of the actual base-changed quotient. These facts supply every
hypothesis of the explicit properness criterion and hence properness of the
constructed quotient.

`existenceStatement_of_statements` extracts the scheme and projection from this
data. A smooth projection is flat; the homogeneous quotient retains surjectivity,
quasi-compactness and the exact right-coset equivalence on all scheme tests.
The conclusion is the unchanged published `ExistenceStatement.{u}`, conditional
on exactly the five stated inputs.

The construction retains every ring, including the zero ring and non-Noetherian
rings, arbitrary universe `u`, every field algebra structure, and every test
scheme, including nonreduced tests. Its provenance is internal: it combines the
existing actual ambient-map, scheme quotient, fibre and smoothness interfaces.
It adds no literature assertion and leaves the proofs of the five explicit
inputs as separate obligations.
