# Actual pinned isomorphism for an algebraic scalar tower

Let `k`, `K`, and `L` be fields in an arbitrary common universe, with a scalar
tower `k → K → L` and algebraicity of all three field extensions. Let `G` be an
actual affine `k`-group scheme and `p : SplitPinning G` a supplied complete
split pinning. `SplitPinning.baseChangeTowerIso` constructs an actual
`SplitPinning.Iso` from the pinning obtained by extension first to `K` and then
to `L`, to the pinning obtained by direct extension to `L`.

Its torus isomorphism is `p.baseChangeTowerTorusIso`, its ambient group
isomorphism is `baseChangeTowerGroupIso`, and its root-index equivalence is
`p.baseChangeTowerIndexEquiv`. In particular the latter keeps the original
indices unchanged. The inclusion square, every root and coroot in the full
integral lattices, simple-support membership, and the actual differential on
all chosen simple-root Lie vectors agree under these comparisons. These are
the fields of the output `SplitPinning.Iso`, with no additional compatibility
data supplied by the caller.

## Implemented construction

The generic constructor `SplitPinning.Iso.ofLinear` takes two supplied pinnings
over one field, their actual torus and ambient group isomorphisms, the inclusion
square, the root-index equivalence, the root, coroot and support equations,
and the canonical linear differential equation on the chosen vectors. It
packages precisely those data into `SplitPinning.Iso`; the constructor's vector
equation uses `Lie.targetMapLinear` with the field's canonical bundled
coefficient ring, exactly as required by that structure.

For the scalar-tower specialization, the imported module
`Reductive.PinningScalarCoherence` constructs the three comparison maps and
proves all of these equations. The private `towerAssembly*` definitions apply
`Iso.ofLinear` successively to the specified torus comparison, group comparison,
inclusion square, index equivalence, root equations, coroot equations and
support equivalence. The public `baseChangeTowerIso` supplies the final
root-vector equation. The small intermediate applications keep Lean's kernel
conversion work manageable; they add no mathematical hypotheses or choices.

The affine instances of the pulled-back groups come from the imported
`SplitPinning.towerAffine` construction. The supplied complete pinning retains
its actual connected reductivity, split maximal torus, full reduced root datum
and simple-root trivializations throughout. There is no restriction on the
characteristic, dimension, root rank or central directions.

## Provenance and scope

This is an internal assembly of the actual comparison maps and checked
equations of `Reductive.PinningScalarCoherence`, using the published definition
of `SplitPinning.Iso`. No new external structural theorem is asserted. A
complete pinning is still an input, and the field extensions are algebraic.
The construction does not establish pinning existence, a coherent semilinear
Galois action, effective descent, an adjoint quotient, or the unconditional
quasi-split inner-form existence statement.
