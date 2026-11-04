# Split torus extensions from the one-dimensional unipotent classification

Worker 1496. The module has one theorem,
`Langlands.GroupScheme.solvableSplitExtension_of_oneDimensional`. It proves
`PerfectFieldOneDimensionalUnipotentStatement.{u} → SolvableSplitExtensionStatement.{u}`.
The classification of one-dimensional smooth connected unipotent groups over
perfect fields is an explicit premise. The module itself proves no
unconditional statement.

The Library already proves that premise as `perfectFieldOneDimensionalUnipotent`
(module `Unipotent/OneDimensional/Proof`). The term
`solvableSplitExtension_of_oneDimensional perfectFieldOneDimensionalUnipotent`
therefore proves `SolvableSplitExtensionStatement.{u}` with no premise. The
companion module `Absolute/MaximalRankRadicalTorusIntersectionOfQuotient` uses
it in exactly that form, inside a proof.

This is Milne 2017, Theorem 16.26(a) (printed pp.332–333), in the form of the
published `SolvableSplitExtensionStatement`. The proof is the same as that of
`solvableSplitExtension_of_perfectFieldUnipotentSplit` in
`Absolute/TriangularSplitExtension`. That theorem applies its premise
`PerfectFieldUnipotentSplitStatement` only to the algebraically closed base
field `k` and the kernel `U`. Here the splitness of `U` comes instead from
`Unipotent.algebraicallyClosedSplit_of_oneDimensional`, with the proved
closed-subgroup input `unipotentClosedSubgroup` and the premise.

## Proof

Fix the data of the statement. `H` is smooth, connected and solvable over the
algebraically closed field `k`. The map `i : U ⟶ H` has normal range, and `U`
is smooth, connected and unipotent. `q : H ⟶ D` is a represented fppf quotient
by that range, onto a split torus `D`.

1. `solvableTriangularEmbeddingStatement` (Lie–Kolchin) gives a closed
   embedding `j` of `H` into the upper triangular subgroup scheme of some
   `GL_N`.
2. `Unipotent.algebraicallyClosedSplit_of_oneDimensional unipotentClosedSubgroup hone`
   shows that `U` is split unipotent.
3. `HomogeneousQuotient.fppf_section_of_split_unipotent_torsors` with the
   proved `splitUnipotentAffineTorsorStatement` gives a scheme section `s` of
   `q`.
4. On points, the kernel of `q` is the range of `i`. This is the kernel clause
   of `IsFppfQuotient`.
5. `IsSplitTorus.exists_section_of_triangular` turns the scheme section into a
   group-scheme homomorphism `σ : D ⟶ H` with `σ ≫ q = 𝟙 D`.

The axioms are `propext`, `Classical.choice` and `Quot.sound`. The proof uses
none of `SolvableMaximalTorusSemidirectStatement`,
`MaximalTorusConjugacyStatement` or `SolvableMaximalTorusConjugacyStatement`.
