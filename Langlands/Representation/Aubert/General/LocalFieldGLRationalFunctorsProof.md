# Transport of the actual normalized GL functors: proof

`Langlands.Aubert.General.RationalPointFamily.GL.localFieldGLRationalFunctors`
proves `LocalFieldGLRationalFunctorsStatement.{u, v}` at independent universe
levels `u` (the field) and `v` (the representations), with no further
hypothesis. It is `localFieldGLRationalFunctors_of_modulus` applied to
`Langlands.Parabolic.localFieldGeneralLinearModulusCompatibility`, the proof
of `Langlands.Parabolic.LocalFieldGeneralLinearModulusCompatibilityStatement`.
That statement says that over every `LocalFieldData F`, every rank \(n\) and
every ordered block shape \(B\), the Haar character of conjugation on the
closed radical `B.unipotentSubgroup F`, on the whole parabolic, is
`T.leviModulus B` composed with `B.leviProjection F`. No field, rank,
cocharacter or block shape is singled out; rank zero is covered by the same
argument.

## From the statement to the matched triple

`localFieldGLRationalFunctors_of_modulus` introduces the field, its data `T`,
the rank, the strictly decreasing cocharacter \(\nu\) and the block shape, and
builds exactly the objects of the statement: the rational-point group in the
evaluation topology, the continuous group isomorphism
\(e\) = `GroupScheme.GeneralLinear.rationalPointsContinuousMulEquiv n F` onto
the matrix group, the standard index \(J\) = `blockRootSubsetEquiv F ν hν B`,
the semidirect decomposition `dec` of the standard parabolic and the closedness
`hU` of its radical. The three published comparisons
`parabolic_blockRootSubsetEquiv`, `levi_blockRootSubsetEquiv` and
`unipotent_blockRootSubsetEquiv` say that \(e\) carries the rational-point
parabolic, Levi and radical onto `B.parabolic F`, `B.leviSubgroup F` and
`B.unipotentSubgroup F`. Read memberwise, they are the three subgroup
hypotheses of `localFieldGLFunctors_of_subgroupEquiv`, and the Levi one gives
the same isomorphism
\(e_L\) = `(GroupTransport.subgroupEquiv e hL).trans (B.leviEquivContinuous F).symm`
as the statement.

## The comparison for a matched triple

`localFieldGLFunctors_of_subgroupEquiv` works for any locally compact
nonarchimedean group \(H\) with an actual semidirect decomposition
\(P = M \ltimes U\), \(U\) closed, and any continuous group isomorphism
\(e : H \to \mathrm{GL}_n(F)\) matching \(P, M, U\) memberwise with the block
parabolic, Levi and radical. Write \(\delta\) = `T.leviModulus B`, with open
kernel by `T.isOpen_ker_leviModulus B`, and `hc` for the modulus statement at
\(F, T, n, B\), that is `B.GeneralModulusCompatibility δ`.

*Induction.* `B.generalInductionIso δ hδ hc` is a natural isomorphism from
`Parabolic.productToEmbeddedLevi B` followed by the general normalized
induction of the matrix triple `B.generalSemidirectDecomposition` to
`B.normalizedInductionFunctorOf (B.blockHalfCharacterOf δ hδ)`. The latter is
`T.normalizedParabolicInductionFunctor B` by unfolding. The compatibility `hc`
identifies the general half modulus with the explicit block half modulus, and
the components keep each function (`generalInductionIso_hom_eval` holds by
`rfl`). `GroupTransport.inductionIso` for the two triples and \(e\) is a
natural isomorphism from the matrix-triple induction followed by pullback along
\(e\) to pullback along the Levi restriction of \(e\) followed by the
rational-point induction; its components precompose functions with \(e\). The
proof takes \(\alpha\) to be the inverse of the block comparison, whiskered on
the right by pullback along \(e\), followed by the transport isomorphism
whiskered on the left by `productToEmbeddedLevi B`. Since `productToEmbeddedLevi B` is pullback along the inverse of
`B.leviEquivContinuous F`, its composite with pullback along the Levi
restriction of \(e\) is pullback along \(e_L\) by definition. The component
of \(\alpha\) at \(A\) therefore sends \(f\) to \(x \mapsto f(e(x))\), and
the evaluation equation of the statement holds by `rfl`.

*Jacquet restriction.* `B.generalJacquetIso δ hδ hc` is a natural isomorphism
from `T.normalizedJacquetFunctor B` (by unfolding,
`B.normalizedJacquetFunctorOf δ hδ`) followed by `productToEmbeddedLevi B` to
the general Jacquet functor of the matrix triple. Here `hc` identifies the
general inverse half modulus on the embedded Levi with the explicit one, and
the component sends
`B.jacquetMk A.representation v` to the class of \(v\) in the actual
coinvariant quotient by `B.unipotentSubgroup F` (`generalJacquetIso_hom_mk`).
`GroupTransport.jacquetIso` for the two triples and \(e\) compares the matrix
and rational-point Jacquet functors under pullback along \(e\) and its Levi
restriction, sending the class of \(v\) to the class of the same \(v\) for the
pulled-back action. The proof takes \(\beta\) to be the block comparison
whiskered by pullback along the Levi restriction, followed by the transport.
The class equation of the statement holds by `rfl`.

## Dependencies

A traversal from each root recursively expanded every reached constant of the
project (module roots `Langlands`, `FontaineWintenberger`, `Nyll`,
`StacksCore` and `StacksFrontier`) with
`Lean.ConstantInfo.getUsedConstantsAsSet`, through types and values, and
assigned each constant to its defining module. Lean and Mathlib constants were
not expanded. It was run on 26 November 2026 at Library commit
`cf95b60a0d1a76782b35d915d189d581090e1c62`, in the Library's Lean
environment. A classification module is one whose name has a
`Classification` component, for example the modules under
`Langlands.Representation.Classification`,
`Langlands.AllField.Representation.Classification` and
`Langlands.AllFieldBZ.Representation.Classification`.

| Traversal root | Project constants | Defining project modules | Constants from classification modules |
| --- | ---: | ---: | ---: |
| `localFieldGLRationalFunctors` (type and proof) | 26,153 | 2,102 | 0 |
| `LocalFieldGLRationalFunctorsStatement` | 25,829 | 2,072 | 0 |
| `localFieldGLFunctors_of_subgroupEquiv` | 554 | 50 | 0 |

The counts include compiler-generated auxiliary declarations; 17,054 of the
26,153 constants reached from the theorem have names that are not internal
details in the sense of `Lean.Name.isInternalDetail`. Every reached project
constant is defined in a module under `Langlands`. No declaration from a
classification module is reached, so the proof uses no classification
theorem.

Imports are a separate matter. The import closure of this proof module,
counting the module itself, has 3,424 project modules, eighteen of them under
`Langlands.Representation.Classification`. The import closure of the
statement module has 3,408 project modules and the same eighteen
classification modules. Importing a module does not make its declarations
dependencies.
