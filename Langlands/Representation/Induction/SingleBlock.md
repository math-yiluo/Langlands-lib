# Evaluation for single-block normalized induction

Author: Worker 163.

This module constructs an actual representation equivalence for normalized
parabolic induction from a shape with one block, together with its block-product
corollary. It is internal infrastructure derived from the published induction,
block geometry, smooth pullback and finite tensor definitions. It does not
introduce a new model of induction or a new group or tensor equivalence.

## Main construction and hypotheses

For a prime `p`, `F : PadicField.{uF} p`, a realization
`T : F.TopologicalData`, a shape `B : BlockShape n` with
`hB : B.length = 1`, and a complex representation
`σ : Representation ℂ (B.Levi F.Carrier) V`, the construction

```lean
T.singleBlockNormalizedInducedEquiv B hB σ hσ
```

has type

```lean
(T.normalizedParabolicInduced B σ).Equiv
  (σ.comp (B.singleBlockLeviEquiv hB F.Carrier).symm.toMonoidHom)
```

Here `hσ` asserts smoothness for `T.leviTopology B`, the actual product
Levi topology. The source is the existing `Induction.SmoothFunctions` space
for the twisted, inflated action. The target carrier is the original `V`.
With `e = B.singleBlockLeviEquiv hB F.Carrier`, the two maps are

```text
f ↦ f(1),                 v ↦ (g ↦ σ(e⁻¹(g)) v).
```

`singleBlockNormalizedInducedEquiv_apply` and
`singleBlockNormalizedInducedEquiv_symm_eval` prove these formulas.
The named `left_inv` and `right_inv` lemmas expose the inverse identities.
`singleBlockNormalizedInducedEquiv_action` states that evaluation carries
right translation by `g` to the action of `σ(e⁻¹(g))`. These are also
intrinsic laws of the constructed `Representation.Equiv`; its inverse is
therefore an intertwiner as well.

The field universe `uF` and the module universe `uV` are independent. The
induced function carrier is in `Type (max uF uV)`, whereas `V : Type uV`.
The construction uses a representation equivalence, which permits these
independent carrier universes. It needs no irreducibility, admissibility,
finite dimension or classification assumption, and no topology on `V`.

## Explicit normalization

The four lemmas

- `singleBlock_leviModulus`,
- `singleBlock_parabolicModulus`,
- `singleBlock_leviHalfModulus`, and
- `singleBlock_parabolicHalfModulus`

are in `Langlands.PadicField.TopologicalData` and prove that the respective
characters evaluate to one at every element. They are conclusions from
`hB`, not additional assumptions on the normalizing character.

The Levi modulus proof expands `T.leviModulus_apply`. Every inner product
is over indices `j` satisfying `i < j`; the published
`B.eq_singleBlockIndex hB` makes such an index pair impossible. The
parabolic modulus follows by its defining inflation. The positive complex
half is one by the published `leviHalfModulus_eq_one`, which identifies
triviality of the positive half with triviality of the full modulus.
Inflation then gives the parabolic half. Thus the actual inducing action
agrees with the Levi action pulled back from the ambient group.

## The inverse is a smooth induced function

The internal general construction
`Langlands.Induction.smoothInducedTopEquiv` works over any commutative
coefficient ring `R`, topological group `G`, and `R`-module `V`. Its inputs
are a subgroup `P` with a proof `P = ⊤`, a representation `σ` of `P`,
a smooth representation `ρ` of `G`, and equalities
`σ p = ρ (p : G)` for every `p : P`. Its output is
`(smoothInduced P σ).Equiv ρ`.

The inverse uses the existing `smoothFunctionOf` constructor with
`f_v(g) = ρ(g)v`. Covariance follows from the homomorphism law and the
specified equality of actions. For each vector, smoothness of `ρ`
provides one open subgroup `K` fixing `v`. Every `k ∈ K` then fixes the
entire function under right translation, since
`ρ(xk)v = ρ(x)(ρ(k)v) = ρ(x)v` for every `x`. This is precisely the uniform
open stabilizer required by `SmoothFunctions`, not just local constancy.
Evaluation is linear. Covariance at the identity, with every `g` viewed
in `P`, proves both the left inverse and intertwining. The identity law
of `ρ` proves the right inverse. The generic `_apply` and `_symm_eval`
lemmas expose both formulas.

For the main specialization, the full-subgroup proof is the published
`B.singleBlock_parabolic_eq_top`. Ambient smoothness is obtained by
`Langlands.isSmooth_comp` along the inverse of the published actual
continuous equivalence `B.singleBlockLeviEquivContinuous hB F.Carrier`.
In particular an open subgroup of the Levi fixing `v` pulls back to an
open subgroup of the ambient general linear group. The realization's
topology, valuation and local-field structure supply the topological-ring
instance used by that continuous equivalence. The explicit half-modulus
lemmas identify the inducing action with this ambient action.

## Unique block and rank transport

The auxiliary lemma
`Langlands.GeneralLinear.BlockShape.singleBlockLeviEquiv_symm_coordinate`
proves, for every block index `i`, that

```lean
(B.singleBlockLeviEquiv hB R).symm g i =
  (GeneralLinear.reindex (R := R)
    (finCongr (B.singleBlock_size hB i))).symm g
```

It holds over every commutative ring `R`. The equality
`B.singleBlock_size hB i : B.size i = n` is the explicit rank transport.
The proof compares matrix entries using the published
`singleBlock_index_val`; it does not construct a substitute Levi
identification.

`B.singleBlockTensorEquiv hB τ i` identifies `B.blockTensor τ` with
`(τ i).comp (Pi.evalMonoidHom _ i)`. It reduces the length to one and the
chosen index to zero, then reuses `FiniteTensor.singletonEquiv τ`.
Its intertwining law follows from the published singleton action formula
and the inverse law of `FiniteTensor.evalOneContinuous` for the actual
product topology. This auxiliary construction assumes a coefficient
topology so that this existing continuous equivalence can be used; it
requires no continuity of ring operations and no module topology.

For a family `τ i` smooth for the actual `T`-induced general linear
topologies, the corollary is

```lean
T.singleBlockNormalizedProductEquiv B hB τ hτ i :
  (T.normalizedProductInduced B τ).Equiv
    ((τ i).comp
      (GeneralLinear.reindex (R := F.Carrier)
        (finCongr (B.singleBlock_size hB i))).symm.toMonoidHom)
```

The proof applies the main equivalence to the external tensor action,
whose smoothness is the published `FiniteTensor.isSmooth_external`.
It then composes with `singleBlockTensorEquiv` and uses the coordinate
identity to identify the resulting action with the displayed rank
transport. The lemma `singleBlockNormalizedProductEquiv_apply` proves
that the forward map is evaluation at the identity followed by the
singleton tensor map. The resulting `Representation.Equiv` includes
both inverse identities and equivariance. The family carrier universe
remains independent of the field universe.

## Provenance and scope

All mathematical inputs are current Library declarations, imported by
module name:

- `Langlands.Group.GL.SingleBlock`: the full parabolic, actual continuous
  Levi equivalence, unique index, full block rank and coordinate formula.
- `Langlands.Representation.Induction.BlockFactors` and its imports:
  actual normalized induction, smooth covariant functions, the external
  block action and the explicit positive modulus characters.
- `Langlands.Representation.Tensor.FiniteEquivalences`: the existing
  singleton tensor and continuous group-evaluation equivalences.
- `Langlands.Representation.Smooth.Transfer.PullbackProof`: smoothness
  under a continuous group homomorphism.

The proof route is the direct evaluation argument described above.
This is an internal consequence of those definitions, not a claim of
formalizing a separately cited external theorem. Existing Library
Lean/Markdown pairs are unchanged. The result supplies the single-block
base case; it makes no claim about induction transitivity or the
classification of representations.
