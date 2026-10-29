# Flattened normalized upper Jacquet comparison

Authors: Worker 485 (proof draft), adapting Worker 429's published opposite
comparison proof; Worker 1027 (submission and audit).

`Langlands.Parabolic.flattenedJacquetComparison` proves the published
`FlattenedJacquetComparisonStatement.{uK,uF,uV}` from
`Langlands.Representation.Parabolic.FlattenedJacquetComparisonStatement`. Its
two clauses are the literal equality of the composed and flattened upper
radicals over every commutative ring, and the representative-preserving
equivalence of the actual normalized upper Jacquet representations over every
p-adic field. The ring, field and representation-carrier universes are
independent.

## Radical equality

`flattenedUnipotentComparison` proves the first clause by antisymmetry. The
published `BlockShape.flatten_unipotentSubgroup_le` gives the inclusion of the
flattened radical in the composed one.

For the reverse inclusion (private `composed_le_flattened`), `mem_leviPreimage_iff`
puts an element of the composed radical in the coarse upper parabolic and puts
its Levi projection in the refined radical. By `mem_refinedUnipotent`, each
coarse diagonal block then lies in its inner upper radical. If a flattened block
precedes another, then by `flattenBlockEquiv_lt_iff` either the coarse blocks
are strictly ordered or the coarse blocks agree and the inner blocks are
strictly ordered. Coarse upper triangularity (`mem_parabolic_iff`) or inner
upper triangularity, read through `leviProjection_apply`, gives the required
zero entry below the diagonal. The identity fine diagonal blocks come from the
inner radical. `flatten_index` identifies the flattened matrix coordinates with
the nested ones. This adapts the finite coordinate argument for the opposite
radical, with the zero-entry order reversed.

## Normalized quotient comparison

Transport along a subgroup equality is a linear equivalence of the ambient
coinvariant quotients that sends each class `[v]` to `[v]` (private
`quotientCongr`). Composing it with the inverse of the published
`BlockShape.jacquetModuleEquiv` reaches the standard upper Jacquet carrier of the
flattened shape, and `jacquetModuleEquiv_mk` keeps the formula
`composedJacquetMk B S ρ v ↦ (B.flatten S).jacquetMk ρ v`.

The published full modulus identity `T.composedLeviModulus_flattened` passes
through the positive square-root character and the complex unit map, so the
composed half modulus pulled back along `flattenedLeviEquiv` equals the standard
half modulus of the flattened shape. Every quotient vector has an original
representative. On representatives, `normalizedComposedJacquet_mk`,
`normalizedJacquet_mk_eq_inv_halfModulus`, this half-modulus equality and
`flattenedLeviEquiv_embedding`, which identifies the ambient matrices, prove
that the linear equivalence intertwines the two actions of the full flattened
Levi. The resulting `Representation.Equiv` and its representative formula are
the witness of the second clause.

## Scope

Rank zero, empty or trivial refinement families and zero modules are included.
There is no smoothness, admissibility, finite-length, irreducibility, positive
rank or nonzero-representation hypothesis, and no supplied subgroup equality,
modulus equality or normalization certificate. This is an internal consequence
of published finite matrix, quotient and character constructions; no external
theorem is cited for this comparison. Intrinsic natural transitivity, tensor
identification and segment-specific Jacquet calculations are not proved here.

## Independence audit

The transitive project import closure has 61 modules: this proof module, the
published statement module, `Parabolic.FlattenedRefinementModulusCalculation`
and 58 further published modules. Both files of each of the 60 dependency pairs
agree byte for byte with Library commit
`ced4d7320042961d7464496781184a2ce8f9a762`. A scan of the closure's Lean and
Markdown files for the excluded task IDs and result names found no forward
special square-integrability, ordered conversion, square-integrable or regular
exhaustion, Langlands or strong-head analytic classification, tempered-block
uniqueness, multisegment exhaustion, ordered strong-head existence, quotient
coverage, segment-head product irreducibility, generic segment-product
uniqueness or multisegment socle exhaustion result. Zelevinsky mentions in the
dependency Markdown are citations of Bernstein and Zelevinsky (1977) for
conventions. No derivative formula, analytic result of Zelevinsky (1980)
section 9.3 or conjecture of section 9.17 is used. From the imported
`CuspidalSupport.MinimalJacquetProof` the proof uses only the coordinate
inclusion `flatten_unipotentSubgroup_le` and the flattened-index lemmas
`flatten_index` and `flattenBlockEquiv_lt_iff`. The opposite comparison proof is
not imported.
