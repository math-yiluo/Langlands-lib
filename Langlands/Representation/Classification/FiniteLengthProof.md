# Finite length of admissible finitely generated GL representations

Author: Worker 122.

`Langlands.glAdmissibleFiniteLength.{uF,uV}` proves the exact existing
`Langlands.GLAdmissibleFiniteLengthStatement.{uF,uV}`. For every prime,
actual finite extension of `Q_p`, positive rank, and complex representation,
admissibility and finite generation over the actual GL group algebra imply
finite length over that group algebra. The field and representation-carrier
universes are independent. The field has its canonical module topology.
The proof applies to zero representations and imposes no central-character,
irreducibility, unitarity or finite-vector-space-dimension hypothesis.

The exported helper `Langlands.Parabolic.normalizedJacquetFiniteLength`
also proves finite length of every standard normalized Jacquet module of an
admissible finitely generated ambient GL representation. Its conclusion is
over the actual standard product-Levi group algebra. It allows arbitrary
compatible topological data and every rank, including zero. Both hypotheses
refer to the ambient GL representation. This helper does not assert finite
length for arbitrary representations of a product Levi without hypotheses.

## Algebraic transport and complementary summands

The internal namespace `Langlands.FiniteLengthAssembly` assembles existing
Library and Mathlib APIs. For a surjective homomorphism of acting monoids,
`length_comp_surjective` identifies the two actual group-algebra submodule
lattices. It composes the published
`CuspidalSupport.JacquetLength.compSubrepresentationOrderIso` with Mathlib's
subrepresentation/submodule order isomorphisms. Invariance under the source
monoid is exactly invariance under the target monoid by surjectivity.
Equality of Krull dimensions gives equality of module lengths, including
the infinite value. `Module.length_ne_top_iff` yields finite-length transport
in both directions. Intertwiners become maps of the actual group-algebra
modules through `IntertwiningMap.equivLinearMapAsModule`; Mathlib transfers
finite generation through surjections and finite length through surjections
or injections.

For complementary invariant subspaces `S` and `Q`, `complementaryProjection`
is the actual linear projection onto `S` along `Q`. To prove equivariance,
decompose a vector into its two components, use their invariance, and apply
the projection's identity and zero formulas. The projection is surjective,
so finite generation passes from the ambient representation to either
summand. The inclusion of `S` and projection onto `Q` give a short exact
sequence: the latter's kernel is the former's range. Published additivity
of `repLength` then combines finite length of the two summands.

## Reduction to proper refined Jacquet modules

`normalizedJacquet_eq_twist` compares two published presentations of the
same normalized standard Jacquet action. Surjectivity of the quotient map
reduces equality to a vector representative; both formulas are the same
inverse positive half-modulus scalar times the actual Levi action. This
equality transfers the published
`Parabolic.normalizedJacquetAdmissibility` theorem to `T.normalizedJacquet`.
The inclusion of an invariant Levi subspace also transfers admissibility
by the published injective-intertwiner theorem.

`finiteLength_of_refinedJacquet` applies the published
`CuspidalSupport.leviQuasicuspidalDecomposition` to an admissible finitely
generated smooth product-Levi representation `A`. It obtains complementary
invariant subspaces `S` and `Q`: `S` is quasicuspidal, and every quasicuspidal
smooth subquotient of `Q` is zero. Inclusion gives admissibility of `S`;
complementary projection gives its finite generation. The published
`CuspidalSupport.leviQuasicuspidalFiniteLength` consequently gives finite
length of `S`.

For each proper refinement, the normalized refined Jacquet map of the
projection onto `Q` is surjective. Indeed, choose a representative of a
target quotient class, lift it through that projection, and take its class.
Thus any finite-length bound for the refined Jacquet module of `A` passes
to the corresponding module of `Q`. The published
`CuspidalSupport.refinedJacquetFiniteLengthDetection` gives finite length
of `Q`. Combining summands gives finite length of `A`.

`finiteLength_normalizedJacquet_of_refinements` specializes this reduction
to a standard normalized Jacquet module of an admissible finitely generated
ambient GL representation. Its smoothness and admissibility are published
results; its finite generation is supplied by the published
`Parabolic.normalizedJacquetFiniteGeneration`. Only the finite lengths of
its proper iterated Jacquet modules remain to be established locally.

## Strong induction and recovery of GL

Fix the ambient representation `rho`. The exported Jacquet-length helper
proves the conclusion simultaneously for every block shape `B` by strong
induction on the natural number `n - B.length`, the semisimple rank of its
product Levi. A proper refinement `R` strictly increases the number of
blocks, while the flattened number of blocks remains at most `n`.
`refinement_measure_lt` therefore proves strict decrease of this measure.

The induction hypothesis gives finite length of the standard normalized
Jacquet module for `B.flatten R`. The published
`Parabolic.flattenedJacquetQuotient` supplies an actual surjective
intertwiner from this module to the iterated normalized Jacquet module
pulled back along `Geometric.flattenedLeviEquiv`. Finite length passes
through the surjection. The algebraic transport lemma then removes this
pullback along the surjective Levi equivalence. This supplies every
proper-refinement premise of the preceding reduction and closes the
induction. There is no assumed finite length at any stage. The induction
also covers the empty block family and the absence of proper refinements.

For positive `n`, choose the shape consisting of one block of size `n`.
Its half-modulus is one, its unipotent radical is trivial, and its Levi
embedding is surjective. The actual Jacquet quotient map is consequently
an injective intertwiner from the original action pulled back along that
embedding to the one-block normalized Jacquet action. The helper gives
finite length of the latter; injection and surjective-monoid transport
recover finite length of the original GL representation. Finally,
`PadicField.canonicalTopologicalData_topology` identifies the supplied
canonical topological data with the canonical topology in the target.

## Source correspondence and provenance

The exact target is the GL specialization of Silberger, *Introduction to
Harmonic Analysis on Reductive p-adic Groups* (1979), Theorem 5.4.1.6,
printed pp.291–292 / PDF pp.297–298. The registered original is
`silberger-1979-harmonic-analysis`, content SHA-256
`b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`.
The statement and proof were read directly. No source-specific errata note
is present in the current public notes.

Silberger reduces central action, splits off the supercuspidal factors,
uses admissibility and finite generation of proper Jacquet modules,
and bounds the remaining length by exact Jacquet functors. The Lean proof
implements that final decomposition-and-rank-induction structure using the
published general quasicuspidal decomposition and quasicuspidal finite-length
theorems. It does not reproduce the cyclic or scalar-central-character
reductions. The refined detection theorem supplies the exactness-and-length
argument; its paired Markdown explains its internally derived formulation
and its motivation in Bernstein–Zelevinsky (1977), section 2.14(2).
The [decomposition proof](../CuspidalSupport/LeviQuasicuspidalDecompositionProof.md)
and [quasicuspidal length proof](../CuspidalSupport/QuasicuspidalFiniteLengthProof.md)
record the source routes of those imported inputs.

The transport lemmas, complementary-projection calculations, refinement
measure and one-block recovery are internal derived content. The complete
induction uses the published actual normalized quotient, without assuming
transitivity, equivariance or finite length as a theorem-valued input.
All dependencies are imported by Lean name. The target pair and its import
closure are unchanged. No downstream induced finite-type theorem, segment
classification, general finite-length induction theorem or extra project
axiom is used.
