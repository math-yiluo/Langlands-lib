# Uniform fixed-vector generation of actual unramified induction

Worker 1598. This is an internal derived statement supporting generic
irreducibility for actual unramified parabolic induction.

`Langlands.Plancherel.UnramifiedUniformGenerationStatement` concerns a locally
compact Hausdorff nonarchimedean group with an actual semidirect decomposition
`P = M U`. The radical and parabolic are closed. Radical unimodularity,
continuity of the actual Levi projection, and a compact open subgroup `K`
satisfying `G = P K` are supplied. The norm-character family is continuous, and
the inducing smooth complex representation `A` has finite length. The group,
norm-family index, and representation-carrier universes are independent.

An opposite subgroup `Ubar` is explicit. It is normalized by `M`, meets `P`
trivially, and has a supplied opposite Iwahori contraction basis with
contracting element `g`, in the precise sense of the published
`Jacquet.HasOppositeIwahoriContractionBasis`.

For every open identity neighbourhood `O`, the conclusion supplies one compact
open subgroup `L₀` contained in `O` and `K`. Every actual positive
Levi-normalized induction `UnramifiedLeviInduction h hU ν χ A` is generated
by its `L₀`-fixed vectors, simultaneously for all unramified characters `χ`.
The conclusion also holds for every open subgroup `H ≤ L₀`. Generation means
that any actual invariant complex subspace containing all `H`-fixed vectors
equals the whole representation. The subgroup is chosen before the parameter.
The full complex unramified character group is used, with no unitary
restriction.

The intended derivation specializes the published
`exists_regularTranslateSpan_eq_top` at each parameter. Its generators are
the fixed vectors in the common compact picture. The published
`compactFixedEquiv` identifies them with actual induced fixed vectors.
Evaluating a regular translate expansion gives a finite complex linear
combination of actual group translates of these vectors. Any invariant
subspace containing the fixed vectors contains every such expansion.
Fixed vectors increase when the subgroup shrinks, giving the last clause.
This paragraph explains the internal provenance; this module supplies a
proposition, not its proof.

The statement does not construct the opposite subgroup, the contraction basis,
or the compact factorization for actual reductive rational points. It does not
assert that the chosen subgroup satisfies the special compact basis conditions
of Renard VI.9.4. Generation of subquotients, uniform detection of irreducible
subquotients, and irreducibility remain separate obligations. No additional
hypothesis is added to the host generic irreducibility statement.
