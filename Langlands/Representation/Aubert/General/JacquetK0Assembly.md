# Conditional longest-representative assembly on actual exact K0

This internal construction packages the finite assembly step of the Jacquet
equation in Aubert's Theorem 1.7(2). It is conditional on explicit geometric
expansion and representation comparison inputs. It does not prove the
published `RationalJacquetCompatibilityStatement`.

The subgroup families `P`, `M`, `U` are subgroups of an actual locally compact
nonarchimedean group. The maps act on the exact finite-length smooth complex
Grothendieck groups with all short-exact-sequence relations, at carrier
universe `max uG uV`. Label, group, and carrier universes remain independent.
Every standard subset, including the empty and full subsets, is retained.

`transportedLeviJacquetTerm` composes ambient normalized Jacquet restriction
to `M Jprime`, one normalized induction-after-Jacquet term inside that closed
Levi, and the specified actual conjugation transport to `M J`. The inside-Levi
families are literally the `subgroupOf` restrictions at `leviIndex Jprime K`;
the index is `K : Finset Jprime`. `sum_transportedLeviJacquetTerm` distributes
the signed sum and obtains `C.comp (DLprime.comp rJprime)`, with the original
integer signs and the forward-conjugation action on representations
`x ↦ σ(g⁻¹ x g)`.

`jacquetGeometricTerm` is the actual geometric map for `r_J i_I`, composed
with actual ambient `r_I`. Its minimality indices are exactly `J,I`.
`jacquetGeometricSum` constructs the signed sum over all `I` and their
minimal double-coset representatives, for any section of the actual
normalizer quotient. `jacquetK0_comp_alternatingOperator_eq_geometricSum`
uses the supplied `GeometricK0ExpansionStatement` at `(J,I)` and distributes
composition over finite sums. It proves no geometric lemma.

`JacquetGeometricTermReduction` is a named Prop-valued input requiring each
actual composite term to equal `F w (simpleImage actual w I ∩ J)`. Here `F`
is a family of integer-linear maps from the actual ambient K0 to that of
`M J`. It is explicit adapter data; this file does not construct it from
normalized functors or prove its required factorization.
`jacquetGeometricSum_eq_weightedExpansion` applies this comparison and
converts subtype sums to the bounded finite sums of the published weighted
construction.

`JacquetLongestTermReduction` is a second named Prop-valued input. At
`longestRep actual J`, it compares `F`, indexed by the simple image of
`leviIndex (associatedSubset actual J) K`, with the corresponding actual
`transportedLeviJacquetTerm`. The target subset is exactly
`associatedSubset actual J`, and every normalizer lift `n` of the specified
longest representative is allowed. Actual associated-Levi conjugation
supplies the transport membership witness; it does not supply the
representation comparison.

`jacquetCompatibility_of_geometricExpansion` combines those inputs with
`jacquetWeightedExpansion_eq_longest` and
`signed_sum_associatedFinsetEquiv`. The first theorem cancels all
representatives except the specified longest one. The second reindexes the
surviving sum by the literal finite subsets of the associated Levi and
preserves cardinalities. The survivor comparison and distribution lemma
give `rJ.comp D = C.comp (DLprime.comp rJprime)`.

The geometric expansion, construction and comparison of common normalized
terms, normalized transitivity, restricted parabolic and radical transport,
and the survivor comparison remain substantive proof obligations. They are
not added to the exact rational-point target. This conditional helper
provides no final evidence for that target until all its extra inputs are
proved at the target's scope.

Provenance is internal composition of the published actual exact-K0
constructors with intrinsic finite-Coxeter results. The motivating
calculation is Aubert 1995, (1.9) and its continuation, printed
pp.2182–2183. This module's proof bodies use the stated geometric-expansion
input and the two reduction inputs, finite sum laws, and the named
finite-Coxeter theorems. They invoke no classification, character
independence, adjointness, or cuspidal-support theorem. Import-closure
dependencies of the actual map constructors are distinct from these
proof-body dependencies. Aubert Proposition 3.2 and the original defective
application to Theorem 3.6 are unused.
