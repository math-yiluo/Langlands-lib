# The actual empty normalized product unit

Author: Worker 357.

This module constructs an actual representation equivalence, including its
inverse, from normalized induction for every rank-zero block shape to the
existing binary product unit. It also exposes evaluation formulas, compatibility
with actual induced maps, and the resulting smooth-category isomorphism. It is
internal general induction infrastructure.

## Scope and declarations

Fix an arbitrary prime `p`, `F : PadicField.{uF} p`, the supplied topology
`T : F.TopologicalData`, and `B : GeneralLinear.BlockShape 0`. Let
`V : Fin B.length → Type uV` be any family of complex modules and let `σ i`
be representations of the corresponding block groups on those same carriers.
The field and factor universes `uF` and `uV` are independent. No topology on a
factor carrier, smoothness of `σ`, irreducibility, finite length or admissibility
is required for the representation equivalences.

`B.isEmpty_blockIndex_rankZero` proves that `Fin B.length` is empty. For any
purported block `i`, its positive size gives the local coordinate `0`; applying
`B.index i` produces an impossible element of `Fin 0`.

`T.emptyProductEvaluationEquiv B σ` has type

```lean
(T.normalizedProductInduced B σ).Equiv
  (Representation.trivial ℂ (GeneralLinear 0 F.Carrier) (PiTensorProduct ℂ V))
```

Its source is the existing normalized induction of the actual external tensor,
with the actual half-modulus twist and parabolic inflation. Its target keeps
that actual tensor carrier. The forward map is `f ↦ f(1)` and the inverse maps
`v` to the constant function with value `v`. The two lemmas
`emptyProductEvaluationEquiv_apply` and
`emptyProductEvaluationEquiv_symm_eval` state those formulas. All inverse and
intertwining laws are part of the constructed `Representation.Equiv`.

`T.emptyProductUnitEquiv B σ` has type

```lean
(T.normalizedProductInduced B σ).Equiv
  (T.binaryProductUnit.{uF, max uF uV}).representation
```

The target is the already defined trivial representation on
`ULift.{max uF uV} ℂ`. Thus the source induced carrier and target unit both
belong to `Type (max uF uV)`, while the supplied factors still belong to their
original universe `uV`. This does not replace the carrier of an arbitrary
rank-zero factor in a binary product: it compares the actual induction whose
positive-size block index type has been proved empty.

The lemma `emptyProductUnitEquiv_apply` states that the forward map is

```text
f ↦ ULift.up (PiTensorProduct.isEmptyEquiv (f(1))).
```

The lemma `emptyProductUnitEquiv_symm_eval` states that the inverse at a lifted
scalar `z` is the constant function with value
`PiTensorProduct.isEmptyEquiv.symm z.down`. The empty-index instance used in
these formulas is supplied explicitly by `B.isEmpty_blockIndex_rankZero`.

For any second family `τ` with carriers `W i : Type uV` and any family of
actual intertwiners `f i : (σ i).IntertwiningMap (τ i)`, the lemma
`emptyProductUnitEquiv_naturality` proves

```text
emptyProductUnitEquiv τ (normalizedProductInducedMap f v)
  = emptyProductUnitEquiv σ v.
```

There are no injectivity or surjectivity assumptions on the factor maps. The
empty tensor of those maps induces the identity on the scalar line.

For any supplied smooth family `A` in the original carrier universe,
`T.emptyProductUnitIso B A` is an actual isomorphism

```lean
(T.normalizedProductInductionFunctor B).obj A ≅
  T.binaryProductUnit.{uF, max uF uV}
```

in the existing smooth-representation category. This uses the same actual
representation equivalence and the topology supplied by `T`.

## Implemented proof and provenance

The ambient group `GL_0(F)` is subsingleton by the published group model.
Every element of the actual parabolic is therefore identity, and every ambient
element belongs to that subgroup. The proof identifies the parabolic with the
full subgroup and invokes the published
`Induction.smoothInducedTopEquiv` from `Induction.SingleBlock`. Both the twisted
inducing action and the trivial ambient action evaluate to identity on every
subgroup element, by `map_one`. The target action is smooth by
`BinaryTensor.isSmooth_trivial`.

The reused full-subgroup equivalence is an actual evaluation construction:
its inverse is built with `Induction.smoothFunctionOf`, covariance follows
from the action law, and one open stabilizer fixing the target vector fixes
the entire induced function. Covariance at identity proves the inverse and
intertwining laws. In this application the target action is trivial, so the
inverse function is constant. No induction transitivity, exactness,
classification premise, or assertion about irreducible constituents is used.

The empty tensor is identified with the coefficient field by Mathlib's
`PiTensorProduct.isEmptyEquiv`. Composing with the inverse of
`ULift.moduleEquiv` gives the displayed saturated unit carrier. The two actions
are trivial, so this linear equivalence intertwines. The evaluation formulas
are definitional equalities. For naturality, indexed tensor extensionality
reduces the comparison of the two linear maps to pure tensors; both scalar
images are `1` by `PiTensorProduct.isEmptyEquiv_apply_tprod`. The actual
normalized induced map postcomposes each value by `FiniteTensor.externalMap`,
so evaluating at identity gives the required equality. Finally,
`SmoothRep.mkIso` bundles the equivalence and its inverse in the full smooth
subcategory.

This is internal provenance derived from these published constructions and
Mathlib tensor algebra, with no new literature assertion. Existing
`Classification.OrderedMultisegmentHeadReduction` has a related rank-zero
linear equivalence to the scalar field. Its classification imports are not
used here. The new construction reuses the lower general full-subgroup API,
returns the actual unit representation equivalence, and supplies evaluation,
map compatibility and smooth isomorphism APIs. No existing Library pair is
changed.

## Independence audit and remaining obligations

The recursive inventory below was checked against Library commit
`0ebc0efd383ff160084af3b33ab2b7806f7a1dde`. All 40 inherited project Lean/Markdown
pairs are present, nonempty and unchanged; the 41st project module is this
new pair. The external list records 51 direct external import roots, not a
recursive Mathlib inventory. The scan removes Lean comments and strings and
found no proof holes, missing project imports, excluded task/name patterns,
or classification modules. No derivative or mirabolic representation module
is imported; the group-only mirabolic modules concern matrix subgroups.

The audit also follows the actual proof route, beyond the name scan. The only
substantive imported proof is the elementary full-subgroup evaluation argument
just described. The other used bodies are the actual block/tensor/induction
map definitions, the existing binary unit and trivial smoothness proof,
Mathlib's empty tensor and carrier-lift equivalences, and the full-subcategory
isomorphism constructor. These depend on ordinary linear, group and smooth
vector algebra. The Jacquet-named imported module provides positive-character
infrastructure, not a Jacquet formula. No derivative formula, segment, head,
socle, support, or classification conclusion is invoked.

This respects the unchanged exclusions of host task
`8364e73f-14ec-4d14-8f2b-1555a7c1ce95` and the complete trusted operator
responses `bd71b9185aab5d6eafffb7891bd3a3ca`,
`0edda6122ce65ed7ac51603c37473920`, and
`30144f6f9b59540b88b6d4c1517892d9`, read in full. In particular no conclusion
of tasks `30341ae4-65f2-4a0e-9283-763db01a409e`,
`3bfb61fa-1129-4fc9-83fd-7fcfec22106e`,
`ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`,
`20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`,
`8252833d-c269-41a9-824c-5879e531b23b`,
`52e97845-36bb-457d-b76f-70753334b88c`,
`1cb45da2-7007-4351-a694-594fb148b8d1`,
`cd8ab97c-0b78-4bce-97c4-d307a28159a4`, or
`bf433f0a-921a-428c-b0c0-6475438125ac` is used. The further excluded segment,
head, socle, full Jacquet and derivative conclusions, including Ze80 3.5/9.6
and their proof successors, do not occur as inputs. The operator's permission
for a newly proved support-only bound is not needed by this construction.

This focused unit supplies only the actual empty-product boundary. Binary
cuspidal-family concatenation, support addition, product derivative support
aggregation, nonlinkage survival, the linked converse, and the full
`SegmentHeadProductIrreducibility` criterion remain separate obligations.

## Recursive project inventory

```text
Langlands.Group.GL.Basic
Langlands.Group.GL.BlockModulus
Langlands.Group.GL.Blocks
Langlands.Group.GL.Maps
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicOppositeIntersection
Langlands.Group.GL.NormalizedCharacter
Langlands.Group.GL.OppositeBlocks
Langlands.Group.GL.Padic
Langlands.Group.GL.PadicBlocks
Langlands.Group.GL.RankReindex
Langlands.Group.GL.SingleBlock
Langlands.Group.GL.UpperUnipotent
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.Representation.Category.Basic
Langlands.Representation.Geometric.WeylDefinitions
Langlands.Representation.Induction.BinaryProduct
Langlands.Representation.Induction.BlockFactors
Langlands.Representation.Induction.Definitions
Langlands.Representation.Induction.EmptyProductUnit
Langlands.Representation.Induction.Parabolic
Langlands.Representation.Induction.SingleBlock
Langlands.Representation.Jacquet.PositiveCharacter
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.SmoothPart.BasicProof
Langlands.Representation.Smooth.SmoothPart.BasicStatement
Langlands.Representation.Smooth.SmoothPart.Definitions
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Smooth.Transfer.SubquotientProof
Langlands.Representation.Smooth.Transfer.SubquotientStatement
Langlands.Representation.Tensor.Finite
Langlands.Representation.Tensor.FiniteEquivalences
Langlands.Representation.Tensor.OneFactor
Langlands.Representation.Twist.Definitions
Langlands.Topology.CompactNormCharacter
```

## Direct external import roots

```text
Lean.Elab.Tactic.Omega
Mathlib.Algebra.BigOperators.Fin
Mathlib.Algebra.BigOperators.Group.Finset.Basic
Mathlib.Algebra.CharP.Basic
Mathlib.Algebra.Module.ULift
Mathlib.Algebra.Order.Archimedean.Basic
Mathlib.Algebra.Polynomial.Lifts
Mathlib.Analysis.Normed.Module.FiniteDimension
Mathlib.Analysis.Normed.Unbundled.SpectralNorm
Mathlib.Analysis.Real.Sqrt
Mathlib.Analysis.SpecialFunctions.Pow.Real
Mathlib.Basic.Complex.Basic
Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
Mathlib.CategoryTheory.Pi.Basic
Mathlib.CategoryTheory.Products.Basic
Mathlib.CategoryTheory.Skeletal
Mathlib.Data.Fin.Rev
Mathlib.FieldTheory.Finite.Basic
Mathlib.GroupTheory.DoubleCoset
Mathlib.GroupTheory.GroupAction.ConjAct
Mathlib.LinearAlgebra.Matrix.Block
Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
Mathlib.LinearAlgebra.Matrix.Permutation
Mathlib.LinearAlgebra.Matrix.Reindex
Mathlib.LinearAlgebra.PiTensorProduct.Basic
Mathlib.Logic.Equiv.Fin.Basic
Mathlib.NumberTheory.Padics.LocalField
Mathlib.NumberTheory.Padics.RingHoms
Mathlib.RepresentationTheory.Coinduced
Mathlib.RepresentationTheory.Intertwining
Mathlib.RepresentationTheory.Invariants
Mathlib.RepresentationTheory.Irreducible
Mathlib.RepresentationTheory.Rep.Basic
Mathlib.RepresentationTheory.Subrepresentation
Mathlib.RingTheory.DedekindDomain.IntegralClosure
Mathlib.RingTheory.FiniteLength
Mathlib.RingTheory.RamificationInertia.Basic
Mathlib.RingTheory.Valuation.Integral
Mathlib.Topology.Algebra.ContinuousMonoidHom
Mathlib.Topology.Algebra.Group.Basic
Mathlib.Topology.Algebra.Group.Matrix
Mathlib.Topology.Algebra.Group.Units
Mathlib.Topology.Algebra.Module.FiniteDimension
Mathlib.Topology.Algebra.OpenSubgroup
Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
Mathlib.Topology.Algebra.Valued.NormedValued
Mathlib.Topology.Bases
Mathlib.Topology.Compactness.Compact
Mathlib.Topology.Homeomorph.Lemmas
Mathlib.Topology.Instances.NNReal.Lemmas
Mathlib.Topology.LocallyConstant.Basic
```
