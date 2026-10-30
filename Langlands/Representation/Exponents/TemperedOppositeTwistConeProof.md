# Pointwise opposite-Jacquet cone bound for a general tempered source

`Langlands.glTemperedOppositeTwistCone` proves the published proposition
`Langlands.GLTemperedOppositeTwistConeStatement.{uF,uV,uM}` at three
independent universes. The statement and all of its imported pairs are
unchanged. The source `A` is an arbitrary analytically tempered
representation. Every positive total rank, one-block shapes, the supplied
Levi conjugation `w`, and arbitrary real vectors `v, b` are retained.

This is internal derived content, adapted by Worker 1008 from Worker 429's
task-pinned unconditional comparison draft, including its earlier block
interpolation calculation. Worker 429 is a coauthor. Worker 349 developed
the same general necessary-exponent composition independently; the
one-block adapter follows Worker 851's published scalar-layer adapter.
The direct analytic estimates are the published work of Workers 819 and
219. The local finite-fixed-space route was planned by Workers 84, 728 and
429. The two local algebra proof prerequisites are imported from their
published modules, separately proved by Workers 189 and 51. This proof
implements the pointwise interface whose source context is documented in
the unchanged statement Markdown; it makes no additional original
literature claim.

The scalar-character helper obtains the unitary central character of the
irreducible, admissible, unitarizable `ω`, twists it by the actual complex
determinant character, and transports it along the inverse Levi
conjugation. The resulting character has open kernel, acts by scalars on
the actual transported candidate, and has real part

```text
j ↦ -(E.size j : ℝ) * v ((blockEquiv hw).symm j).
```

The imaginary parameter contributes norm one.

The actual invariant subspace and surjective intertwiner in the class
occurrence, together with opposite Jacquet admissibility, let
`isDualJacquetExponent_of_scalar_oppositeClassExponent` apply the
published local scalar-subquotient detector. This produces an ordinary
transpose-dual exponent for the same character. The published local
dual-to-primal conversion, specialized by
`oppositeJacquetDualToPrimal`, then supplies a nonzero primal generalized
eigenvector. Neither step assumes irreducibility, finite generation or
finite length of the ambient source, and neither asserts a global finite
spectrum for its full dual.

The published `ScalarLayer.isJacquetExponent_reverse` uses the actual
`oppositeJacquetReverseEquiv`. A linear-map defect-power induction carries
the generalized eigenvector to the upper Jacquet module for the reversed
shape, with its nonzero value and uniform power preserved. The character
reverses tuple labels without inverting their entries. The reversed
character has open kernel by continuous preimage in the original topology.
The proof reuses this scalar-layer reversal theorem, including its
published defect-power transport and block-scalar identity.

`GeneralTemperedExponentNecessity.upperBound` applies the published
general analytic product-Levi helper estimates through the actual
one-block Levi. Nontriviality of the source carrier follows from the
actual Jacquet vector and surjectivity of `jacquetMk`. This yields the
upper exponent bound without an irreducibility premise. Reversing labels
again gives the opposite character's norm bound on tuples with decreasing
absolute values.

For the numerical step, `cone_of_opposite_bound` inverts the character and
the test tuples. The inverse character has the positive, size-weighted
real part. Bounds on constant tuples and their inverses force exact norm
one on diagonal scalars. The published closed-cone characterization then
gives total sum zero and every proper prefix inequality for that weighted
block vector.

`Langlands.Exponents.diagonal_cone_of_weighted_block_cone`, now shared in
`WeightedBlockCone`, expands each block parameter over all its coordinates.
Its proof and supporting numerical lemmas were moved without changing their
statements or arguments. The block-sum and block-prefix identities give the
total and the inequalities at block boundaries. On each block the
parameter is constant, so `MaximalConePolygon.pre_nonneg_of_antitone`
interpolates between the adjacent boundary sums and supplies every
interior cut. The final `blockIndex_apply_eq_blockMap` calculation uses the
same supplied witness `hw` to identify this diagonal function with
`a ↦ v (blockIndex C (w.symm a))`.

No unproved upper exponent criterion, almost-everywhere specialization,
branch continuation or classification conclusion is used. The conclusion
is exactly the pointwise full diagonal cone.

The project Lean service completed a named Lake build of all five modules,
with zero errors and warnings (development check
`cc2569e6-b81f-4036-92f2-ebbb51bfc632`). Its inspection reports the exact
complete theorem type as the constant
`Langlands.GLTemperedOppositeTwistConeStatement` applied to the independent
universe parameters `[uF, uV, uM]`, with no outer assumptions or additional
parameters. The type-expression SHA256 is
`0c9b601ea20822d16ec6975dfcb463f71a8f7d17c40dee65ee054428f061a71a`.

A separate private inspection module performed the complete unapplied
assignment, without supplying any mathematical arguments:

```lean
import Langlands.Representation.Exponents.TemperedOppositeTwistConeProof

universe uF uV uM

example : Langlands.GLTemperedOppositeTwistConeStatement.{uF,uV,uM} :=
  @Langlands.glTemperedOppositeTwistCone.{uF,uV,uM}

set_option pp.universes true in
#check @Langlands.glTemperedOppositeTwistCone

#print axioms Langlands.glTemperedOppositeTwistCone
```

Check `7e152b9f-8e99-44cb-b3f7-3a0dbf58c0a4` completed with zero errors
and warnings. Its full diagnostic output for these commands is:

```text
Langlands.glTemperedOppositeTwistCone.{u_1, u_2, u_3} : Langlands.GLTemperedOppositeTwistConeStatement.{u_1, u_2, u_3}
'Langlands.glTemperedOppositeTwistCone' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are development compilation and inspection results. Independent
semantic acceptance, formal machine exact-target validation and Library
publication are separate requirements.
