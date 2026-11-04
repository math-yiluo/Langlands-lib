# Closed joint Hecke eigenspaces in completed tensor slices

Author: Worker 2.

This internal construction forms the actual simultaneous eigenspace of any
specified family of compact-open corner operators on all fixed vectors of the
actual closed tensor slice in a supplied global positive-form completion.
The prescribed scalars are arbitrary; nonzero eigenspaces are not assumed.

`TensorHilbertHeckeAux.jointEigenspace T c` is the intersection over the index
type of Mathlib's ordinary `Module.End.eigenspace (T i) (c i)`. Its membership
law is exactly all equations `T i x = c i • x`. The index and carrier universes
are independent, including an empty index type, when the intersection is the
whole carrier. No commutation, finite dimension or nonzero vector is needed.
For continuous complex-linear endomorphisms of a normed carrier,
`isClosed_jointEigenspace` proves closedness by Mathlib's closed eigenspace
result and closedness of arbitrary intersections. Completeness is unnecessary.

`mem_jointEigenspace_equiv_iff` transports the equations through a supplied
complex-linear equivalence intertwining each pair of operators. Its forward
implication uses injectivity, and its reverse implication applies the same
equivalence to each equation. `jointEigenspaceEquiv` restricts that exact
equivalence and its inverse to the actual intersections. Both value laws are
reflexive, so the maps retain precisely the underlying equivalence's values.
`jointEigenspace_ne_bot_iff` transports nonzeroness by the induced equivalence;
it does not prove that either eigenspace is nonzero. No topology or norm on the
source of this equivalence is imposed.

`cornerJointEigenspace` applies this construction to the published genuine
algebraic corner action on the entire invariant-subspace fixed space. The
family consists of elements of the same corner, for a specified Borel Haar
measure and compact open subgroup. `cornerJointEigenspace_eq_continuous`
identifies this submodule exactly with the intersection for the unchanged
bounded operators when the original ambient group action preserves the norm.
The equality is reflexive after forgetting continuity.
`cornerJointEigenspace_isClosed` then applies the generic closedness result.

`factorJointCornerEquiv` uses the published `factorFixedEquiv` and
`cornerAction_factor` covariance to identify the original smooth factor's
joint eigenspace with this full fixed-space joint eigenspace. It requires
explicit factor smoothness and a genuine representation equivalence onto the
ambient smooth intersection. It assumes no ambient smoothness, norm on the
original factor, commutativity or eigenvalue existence.

`FiniteTensorPresentation.sliceHilbertJointCornerEigenspace` uses the actual
closed `sliceHilbertRange`, the original completed global action restricted
along actual finite-local GL_n insertion, and the same specified corner.
The generic `cornerJointEigenspace_isClosed` applies to this actual slice:
the existing `completedRepresentation_norm` supplies norm preservation, with
no new analytic hypothesis. No separate concrete closedness wrapper is defined. All natural ranks,
independent field and original-factor universes, arbitrary index universes and
zero tails are included. The presentation, global invariant positive form,
tail, Borel Haar measure and compact open subgroup are genuine supplied data.

`factorHilbertJointCornerEquiv` specializes original-factor recovery through
the existing `factorHilbertSmoothEquiv`. It retains an explicit nonzero tail
and original-factor admissibility, whose smoothness component supplies the
integrated source action. No irreducibility premise is used. The construction
identifies actual subspaces and the original fixed-space map; it makes no
isometry claim for the original factor.

The provenance is an internal derivation from inspected published corner,
bounded-operator and original-factor covariance constructions, together with
Mathlib's ordinary eigenspaces. There is no new identification with original
literature, canonical subgroup or Haar normalization, standard spherical
operator or Satake parameter. Spectral occurrence, eigenspace decomposition,
existence of the supplied presentation or form, and the remaining global
arithmetic and automorphic constructions remain separate obligations.
