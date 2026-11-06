# Compact visibility of normalized induction

This internal supporting unit proves finite compact visibility for the actual
normalized induction functor. The detecting compact open subgroups of the
Levi are chosen before the inducing representation. No admissibility,
finite generation, finite length, or finite dimensionality is required.

The ambient group is locally compact and nonarchimedean. It has an actual
semidirect decomposition `P = M ⋉ U`, with `M` and `U` closed. The left quotient
`P \ G` is compact. The subgroup `K` is open; its compactness is not required.
The group and inducing carrier universes are independent `uG` and `uV`;
the induced function carrier has universe `max uG uV`.

`FiniteInductionFixedVectorVisibility h hU K` says that a finite set `t`
of group elements and compact open Levi subgroups `L x`, for `x : t`, have
the following property for every smooth complex Levi representation `A`:
nonzero `K`-fixed vectors of its actual normalized induction imply nonzero
`L x`-fixed vectors of `A` for at least one `x`.

## Implemented comparison

`inducingEvaluationNeighborhood h hU K x` intersects two open subgroups
of `M`: the subgroup with `x⁻¹ m x ∈ K`, and the pullback along `M → P`
of the kernel of the actual Haar normalizing character
`HaarModulus.closedHalfCharacter U hU P h.le_normalizer`.
Its openness follows from the existing open-kernel theorem and continuity
of the subgroup inclusion.

`normalizedInduction_eval_mem_fixedVectors` proves that evaluation at `x`
lands in the original Levi fixed vectors for every subgroup `L` of this
neighborhood. The published evaluation law first gives invariance under
the twisted inducing action. On `L` the scalar is one, and the actual
Levi projection is the identity on the Levi inclusion. The proof therefore
recovers invariance under `A.representation` itself.

`exists_compactOpen_inducingEvaluation_subgroup` applies the published
compact open neighborhood basis inside `M`. Closedness of `M` supplies
its local compactness.

`finiteInductionFixedVectorVisibility` takes a finite double-coset cover
from the published compact-left-quotient theorem and chooses one such
compact open subgroup for each representative. Evaluation defines an
injective linear map from the actual induced fixed module into the finite
product of the original Levi fixed modules. Injectivity follows from
the existing fixed evaluation injectivity theorem. A nonzero induced
fixed vector has a nonzero coordinate in this product.

## Provenance and remaining obligations

Worker 1751 derives this unit from the published actual parabolic functor,
its scalar character, the compact open neighborhood basis, and the
compact-left-quotient evaluation API. It is an internal comparison, not
a new assertion attributed to original literature.

The theorem does not establish compactness of an actual rational
parabolic quotient, finiteness of cuspidal inertia classes, a category
decomposition, generator stability, or uniform compression stabilization.
Those inputs and applications remain separate obligations.
