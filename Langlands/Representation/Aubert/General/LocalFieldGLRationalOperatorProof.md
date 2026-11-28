# Grothendieck transport for the local-field GL operator

`Langlands.Aubert.General.RationalPointFamily.GL.localFieldGLRationalOperatorComparison`
proves `LocalFieldGLRationalOperatorComparisonStatement.{u, v}`. The comparison
uses Aubert's unadjusted sum from Definition 1.5 (1995) on the standard upper
parabolics and normalized functors of Bernstein–Zelevinsky (1977), §§1.7–1.8 and
2.1–2.3. It takes the general dynamic finite-length propositions for
induction and Jacquet restriction as hypotheses.
[Statement and source references](LocalFieldGLRationalOperatorStatement.md)

## Transport for a single block

The proof uses the continuous group isomorphism `e` from the rational points
to the matrix group. For a block shape \(B\), let \(J\) be its image under
`blockRootSubsetEquiv`. The three subgroup comparisons identify the parabolic,
Levi and unipotent radical at \(J\) with the corresponding matrix subgroups.
The Levi comparison gives the continuous isomorphism from the rational-point
Levi to the product of the diagonal blocks. With
`Parabolic.localFieldGeneralLinearModulusCompatibility`,
`localFieldGLFunctors_of_subgroupEquiv` then gives natural isomorphisms for the
normalized induction and Jacquet pullback squares.

`canonicalStandardParabolicFiniteLength` supplies finite-length and
short exact sequence preservation for the two point functors at \(J\).
`matrixMap_of_pullbackSquare` carries these properties to the composite of
each matrix functor with its target pullback, using preservation by the source
pullback and the natural isomorphism. It then reflects the properties through
the target pullback. Surjectivity of the group isomorphism identifies the
invariant-subspace lattices, so finite length is reflected. Pullback keeps the
underlying linear maps, so injectivity, exactness at the middle term and
surjectivity are reflected as well.

Write \(p_G\) and \(p_L\) for the ambient and Levi pullbacks on the exact
finite-length Grothendieck groups. `FiniteLengthGrothendieckGroup.map_comp`
and `map_eq_of_iso` give the equations \(p_G i_B = i_J p_L\) and
\(p_L r_B = r_J p_G\) for the induced maps. `matrixTerm_of_pullbackSquares`
composes them to obtain \(p_G i_B r_B = i_J r_J p_G\).

## Summing over the parabolics

The blockwise preservation proofs give `LocalFieldMatrixParabolicExactLength`.
The Grothendieck maps use these witnesses in arguments of propositional type,
so proof irrelevance gives the same equalities for every witness. The proof
evaluates the linear-map sums on an arbitrary virtual class and reindexes by
`blockRootSubsetEquiv`. Its sign lemma identifies \((-1)^{n-B.\mathrm{length}}\)
with \((-1)^{|J|}\). This proves the required equality on the whole exact
Grothendieck group. The same reindexing includes rank zero, where the unique
block shape corresponds to the empty subset and has coefficient \(+1\).

## Classification dependencies

A traversal of declaration types and values with imports from Library commit
`186f3b2ccb3bfee3f9da8d4478ad38d207e354fa` using
`Lean.ConstantInfo.getUsedConstantsAsSet` reached 26,724 project constants
in 2,168 project modules from the theorem. From the statement it reached
26,138 constants in 2,119 modules. In both traversals, the project roots
were `Langlands`, `FontaineWintenberger`, `Nyll`, `StacksCore` and
`StacksFrontier`. In both, the complete set of constants whose defining
module name has a `Classification` component consists of the following two.

- `Langlands.FiniteLengthAssembly.finiteLength_comp_surjective_iff` is used
  by exact Grothendieck pullback and directly by the reflection argument.
- `Langlands.FiniteLengthAssembly.length_comp_surjective` proves the length
  equality underlying that equivalence by the order isomorphism of invariant
  subspaces under a surjective change of acting monoid.

Both lemmas are in `Langlands.Representation.Classification.FiniteLengthProof`.
The dependency inventory treats the two dynamic propositions as hypotheses of
the comparison.
