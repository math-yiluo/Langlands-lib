# Intrinsic smooth subrepresentation of a completed tensor slice

Author: Worker 2.

This module constructs the intrinsic locally smooth subrepresentation of an
actual completed automorphic tensor slice and restricts the original-factor
map to it. The image equation is proved from the published pointwise
smooth-vector recovery law.

## Inputs and actual objects

The number field `F : Type uF` and the local carrier family
`V : FinitePlace F → Type uV` have independent universes. Scalars are complex,
`n` is any natural number, and the original carriers have no topology as
inputs. The construction takes the genuine `FiniteTensorPresentation P`,
its finite exceptional set and integral-fixed reference tensors, and the
supplied invariant positive form `b` on the actual automorphic realization
`S.representation`.

For a finite place `v`, write
`τ = b.completedRepresentation.comp (localInclusion F n v).toMonoidHom`.
Its carrier is the original global form's `b.HilbertCompletion`, and its group
is the actual finite-local general linear group with its published topology.
The slice is `P.sliceHilbertRange b v y`, with the inherited action and
subspace topology.

`sliceHilbertSmoothRange b v y` is the intersection of that slice with
`Langlands.smoothSubrepresentation τ`. It is an actual `Subrepresentation τ`,
so its carrier and action are inherited from the same global completion.
It is defined for every complementary tensor `y`, including zero, without
admissibility or irreducibility assumptions. Smoothness here refers to the
inserted local group.

## Original-factor image and restricted map

For an explicit nonzero-tail proof `hy` and `IsAdmissible (ρ v)`,
`factorHilbertAlgebraicIntertwiner_range` identifies the underlying submodule
of the actual original-factor map's range with

```text
(sliceHilbertRange b v y).toSubmodule ⊓ smoothVectors τ.
```

The proof uses submodule extensionality and the published
`mem_sliceHilbertRange_and_smooth_iff` at each ambient vector. The right side
is definitionally the underlying submodule of `sliceHilbertSmoothRange`.
No algebraic irreducibility assumption is needed.

`factorHilbertSmoothIntertwiner b v y hy hρ` restricts
`factorHilbertAlgebraicIntertwiner b v y hy` to this intrinsic smooth slice.
It is an intertwiner from the given original representation `ρ v` to the
intersection's inherited representation. The construction uses the proved
image equation; it does not choose a substitute target or a substitute map.

## Range-restriction infrastructure and its laws

The internal namespace `Langlands.TensorSmoothRangeAux` treats independently
sized complex modules and a representation of any monoid. Given an actual
intertwiner `f`, a subrepresentation `R`, and equality of their underlying
range submodules, `rangeRestriction` uses `LinearMap.codRestrict` to land in
`R.toSubmodule`. Covariance follows from `f.isIntertwining` by subtype
extensionality.

`rangeRestriction_apply_val` states that forgetting the subtype gives the
original value `f x`; its proof is reflexivity. The theorem
`rangeRestriction_surjective` takes a vector in `R`, transports its membership
along the image equality, extracts the range witness, and applies subtype
extensionality. These laws specialize to the actual
`factorHilbertSmoothIntertwiner` through its defining image equation. There
are no additional specialized evaluation or surjectivity wrappers in this
module.

## Provenance and scope

This is internal construction infrastructure derived from the published
`FiniteTensorHilbertComponent` and the generic smooth-subrepresentation API.
The generic restriction and its laws are proved here. No original-literature
identification is asserted, and published proofs are reused by import.

The construction remains conditional on the genuine tensor presentation and
global positive form. The original-factor restriction additionally retains
its specified place, complementary tensor, nonzero-tail proof and
admissibility hypothesis. Existence of the presentation or form, automorphic
occurrence and global spectral decomposition remain separate obligations.
