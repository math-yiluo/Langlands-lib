# Renard C.I: proof of the nilpotent maximum's numerical base cases

Worker 16 proves
`Langlands.Renard.nilpotentDimensionBaseCases.{u}` with exactly the published
type `Langlands.Renard.NilpotentDimensionBaseCasesStatement.{u}`.
The statement and the actual maximum construction are imported unchanged.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, Appendix C.I, printed
pp.275–276 / one-based PDF281–282. Its registered source ID is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Worker 16 read both pages and visually checked the formulas. Renard opens
the proof on p.275 with the one-generator bound from Cayley–Hamilton,
and explicitly uses `φ_l(1) = 1` for every `l` at the start of p.276.
The zero-dimensional, empty-tuple and arbitrary-carrier conclusions are
derived extensions specifying the full domain of the published construction.
The one-generator conclusion remains an upper bound.

The supplementary registered source
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read on PDF18–19. Its C.I entries concern inequalities and exponents
in the older 2010 proof, printed pp.317–318. They do not change the two
base assertions above; the 2026 edition governs this proof.

## Implemented proof

The proof uses the actual `nilpotentGeneratedMaxDimension l V`, the natural
supremum of the attainable dimensions of
`Algebra.adjoin ℂ (Set.range a)`. It uses the construction's proved
attainment theorem rather than assuming an attaining tuple or any base formula.

The private helper `one_le_nilpotent_max` proves that this maximum is at
least one on every nontrivial carrier. Choose an attaining tuple with
`nilpotentGeneratedMaxDimension_attained`. Its unital adjoin is a nontrivial
finite-dimensional complex algebra, so `Module.finrank_pos` gives the lower
bound. In particular, the identity already supplies a nonzero element in
this algebra.

For a carrier of complex dimension one, `nilpotent_max_finrank_one`
deduces nontriviality from the dimension hypothesis and combines that lower
bound with the published ambient bound
`nilpotentGeneratedMaxDimension_le`. Its right side is `1^2 = 1`.
This argument applies to every natural generator count; it does not
require classifying the individual nilpotent operators.

For one generator, `nilpotent_max_one_generator` again chooses an actual
attaining tuple. `Set.range_unique` identifies the range of its `Fin 1`
indexing with the singleton consisting of its unique entry. The proof
then imports
`Langlands.CommutingDimension.singleton_dimension ℂ V` from
`Langlands.Algebra.CommutingDimensionHelpers`.
Worker 307 authored this published theorem: powers below the minimal
polynomial's degree span the unital adjoin; the minimal polynomial divides
the characteristic polynomial, whose degree is the dimension of `V`.
The present module applies that theorem without copying its proof and
without using the final sharp estimate for several generators.

For no generators, `nilpotent_max_zero_generators` splits on whether the
carrier dimension is zero. In that case it reuses
`nilpotentGeneratedMaxDimension_eq_zero_of_finrank_eq_zero`.
Otherwise the carrier is nontrivial; the attaining tuple has empty range,
`Algebra.adjoin_empty` identifies its adjoin with the scalar subalgebra,
and `Subalgebra.finrank_bot` gives dimension one.

The public theorem assembles these results with the existing zero-dimensional
law for arbitrary carriers. For the four canonical clauses, it reuses
`nilpotentGeneratedPhi_zero` and specializes the remaining results directly
to `Fin k → ℂ`, simplifying its complex finrank to `k`.
It does not invoke the separately published carrier-transport theorem.

## Scope and authorship

All four arbitrary-carrier clauses quantify over every `V : Type u` with
explicit `AddCommGroup V`, `Module ℂ V` and `FiniteDimensional ℂ V`
instances. The four canonical clauses cover all natural indices.
There is no additional hypothesis on the generator count, the space, or
the individual tuple entries. Nontriviality is derived locally where needed;
the final theorem retains zero spaces, empty tuples, zero entries, repeated
entries and redundant generators. The unital adjoin includes scalars and
the identity without counting an additional generator.

Worker 16 authored the adapter proof. The imported statement originated
with Worker 709 and was published by Worker 1200, who also authored the
actual maximum and its construction laws. Worker 307's imported
Cayley–Hamilton dimension theorem is credited above. These published
results are reused by Lean name.

Carrier transport, monotonicity, the actual ideal-power filtration,
complement generation, restriction injection, the algebra splitting,
the floor recurrence, the final dimension estimate and completion of
Appendix C.I remain separate work.
