# Half-twisted adelic induction from actual block factors

Author: Worker 2. Provenance: internal construction from the published
`BlockShape.blockTensor`, `FiniteTensor.externalMap` and actual adelic
parabolic section APIs. This module makes no new identification with an
original-literature induction convention.

Let `F : Type uF` be any number field, `n` any natural rank and `B` a positive
ordered block shape. The empty shape in rank zero is allowed. For every block
`i`, the input `σ i` is an actual complex linear representation of
`AdelicGL F (B.size i)` on a complex module `V i : Type uV`. The source, target
and third coefficient families have independent universes `uV`, `uW`, `uX`;
the number-field universe is independent of each. No topology on the
coefficient modules, finite dimension, irreducibility or smoothness of the
supplied factor actions is required.

The coefficient action is exactly the published `B.blockTensor σ` on
Mathlib's algebraic indexed tensor product `PiTensorProduct ℂ V`. Each actual
adelic block acts on its own tensor factor. The actual Levi is
`B.Levi (Adeles F)`, not an unspecified group with a chosen action.

## Covariant sections and the actual action

`Sections` and `rightAction` specialize the published actual adelic section
space and action to this tensor representation. `covariance` is

`f(p * g) = leviHalfCharacter(leviProjection(p)) •
  blockTensor(σ)(leviProjection(p))(f(g))`.

The half twist is the constructed positive complex square root of the
explicit adelic block determinant character. Its identification with a Haar
modulus remains a separate obligation. `evaluate_rightAction` identifies the
action with actual right translation `f(x) ↦ f(x * g)`.

`FiniteSmoothSections` consists of those actual covariant functions fixed by
one common open subgroup of the finite adelic matrix group. The full adelic
group preserves this condition by the already proved conjugation argument.
`finiteSmoothInduced` is its actual full adelic representation, and
`evaluate_finiteSmoothInduced` retains the same translation formula.
`finiteSmoothInduced_isSmooth` proves smoothness after restriction along
`AdelicGL.ofFinite`. `finiteSmoothSection_finiteLocallyConstant` proves that
every finite slice, at a fixed infinite matrix, is locally constant. These
results impose no open-stabilizer condition on the full adelic group.

## Actual maps of coefficient families

For a family of genuine factor intertwiners `T i : σ i → τ i`,
`sectionMap` and `finiteSmoothInducedMap` first form the published tensor
intertwiner `FiniteTensor.externalMap T`, then postcompose the actual
sections with it. The finite-smooth map preserves the original common finite
stabilizer. Their evaluation lemmas expose exactly that postcomposition.
Identity and composition follow from the published tensor-map laws and,
for finite-smooth sections, the existing induced-map laws. No coefficient
continuity premise is needed for these algebraic constructions.

## Product central character

`centralCharacter c` is the actual Hecke character `∏ i, c i`, where each
`c i` is the central character supplied for the whole block representation.
As a finite product of continuous characters of the actual idele-class
group, it already has continuity and descent through principal ideles.
`centralCharacter_onIdeles` proves its evaluation formula by finite-product
induction. There are no block-rank exponents.

The hypothesis in `blockTensor_scalar` is an explicit identity for the input
actions:

`σ i (AdelicGL.scalar F (B.size i) z) v = (c i).onIdeles(z) • v`.

The theorem proves that the actual common-scalar Levi element acts on the
indexed tensor by `(centralCharacter c).onIdeles(z)`. The proof inducts on
scaled pure tensors and addition. On a pure tensor, the published
`blockTensor_tprod` and the factor identities reduce the assertion to
multilinearity: scaling every coordinate multiplies the scalars. Commutativity
of complex scalars handles the external scaling in the induction.

`rightAction_scalar` and `finiteSmoothInduced_scalar` inherit this proved
coefficient identity on the two actual section carriers. The generic
adelic scalar law uses the fact that the positive half is one on common
scalars and that ambient scalar matrices are central. No central character
exists by assumption apart from the explicit supplied characters and their
displayed action identities.

## Scope

These are algebraic tensor coefficients and finite-smooth adelic sections.
No norm, completion or archimedean smoothness structure is assigned to the
indexed tensor product. The module asserts no nonzero sections, Haar-modulus
identification, unitary induction, automorphic or isobaric realization,
irreducibility, admissibility or tensor factorization theorem.
