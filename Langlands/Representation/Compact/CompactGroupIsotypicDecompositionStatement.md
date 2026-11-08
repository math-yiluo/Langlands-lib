# Isotypic decomposition for compact t.d. groups: statement

Author: Worker 6. Module `Langlands.Representation.Compact.CompactGroupIsotypicDecompositionStatement`, namespace `Langlands.Renard.CompactRepresentation`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, IV.1.1, Corollary and the following definitions, printed pp.88–89 / PDF pp.94–95. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## The source

Let `K` be a compact t.d. group and `K̂` the set of equivalence classes of irreducible smooth representations of `K`. The corollary reads: the category `M(K)` is semisimple; more precisely, every smooth representation `(π, V)` of `K` decomposes canonically as `V = ⊕_{(σ, V_σ) ∈ K̂} V(σ)`. Here `V(σ)` is the image of the canonical map `Hom_K(V_σ, V) ⊗ V_σ → V`, `φ ⊗ v ↦ φ(v)`. Each `V(σ)` is a direct sum of irreducible representations in the class of `σ`, and is called the isotypic component of type `σ`.

## The Lean statement

`CompactGroupIsotypicDecompositionStatement` is a statement unit: nothing is proved. It quantifies over `K : Type u` with `[Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]`, and over a smooth representation `π : SmoothRep.{0, u, v} ℂ K`. The conclusion is the conjunction of:

1. `iSupIndep (fun c => CompactCoefficientClass.isotypicSubrepresentation c π)`: the isotypic components are independent in the lattice of subrepresentations of `π`;
2. `⨆ c, CompactCoefficientClass.isotypicSubrepresentation c π = ⊤`: together they span `π`.

So `π` is the internal direct sum of its isotypic components. The index `c` runs over the published `CompactCoefficientClass.{u, v} K`, the isomorphism classes of irreducible smooth representations with compactly supported smooth coefficients, with representatives on carriers in `Type v`. Since `K` is compact, every coefficient has compact support, so these classes are exactly `K̂`. Every irreducible smooth representation of `K` is finite-dimensional (IV.1.1 (i)), hence has a representative in every carrier universe. The published `isotypicSubrepresentation c π` is the supremum of the ranges of all intertwiners from representatives of `c` to `π`. This is the image of `Hom_K(V_σ, V) ⊗ V_σ → V`, and it is a sum of copies of `σ` by construction. Its semisimplicity is part of the published `CompactCoefficientClass.IsotypicSemisimplicityTheorem` statement.

## Remarks

- Semisimplicity of `M(K)` is part (iii) of the companion IV.1.1 Theorem statement (`CompactGroupSmoothStatements`, Worker 6, candidate `c773791e-c369-490c-845d-0e5396953e1f`).
- The multiplicity `m(σ) = dim Hom_K(V_σ, V)` and the formula `m(σ) = dim V(σ) / dim V_σ` are not stated.
- The proof is not formalized here.
