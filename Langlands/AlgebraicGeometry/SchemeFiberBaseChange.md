# Actual scheme fibre base change and affine tensor comparison

This is an internal comparison for the fibre condition in Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011),
printed pp. 5–6, Theorem 3.4(2). The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The construction is derived from the universal property of the actual
scheme pullback, using Mathlib's cartesian residue-field fibre square.
It supplies comparisons, rather than the filtered-descent assertion.

For any cartesian square P → X, P → Y, X → Z, Y → Z, and any point y
of Y, `fiberBaseChangeMap` constructs the actual map from the fibre of
P → Y at y to the fibre of X → Z at g(y). The second map is induced by
the actual residue-field map κ(g(y)) → κ(y). `fiberBaseChangeSquare`
proves that these maps form a pullback square. `fiberBaseChangeIso`
identifies the first fibre with the pullback of the second fibre along
Spec κ(y) → Spec κ(g(y)); both projection identities are proved.
These declarations apply to arbitrary schemes in Scheme.{u}, including
nonaffine and nonseparated schemes, with no finiteness or flatness
hypothesis. No field extension is replaced by a chosen abstract model.

`hasPureDimension_fiberBaseChange_iff` transports the existing componentwise
topological dimension predicate across this scheme isomorphism.
`hasPureDimensionFibers_baseChange_iff` quantifies it over all actual
points of Y. They reduce the original fibre question to a scalar-extension
pullback, and do not assert that pure dimension is invariant under that
extension for arbitrary schemes.

For any commutative R-algebra A and prime p of R, `specFiberTensorIso`
extracts the source isomorphism of Mathlib's
`Spec.fiberToSpecResidueFieldIso`. It identifies the actual fibre of
Spec A → Spec R at p with Spec(κ(p) tensor_R A), using the actual ideal
residue field and `Ideal.Fiber` tensor algebra. `hasPureDimension_specFiber_iff`
then applies the published spectrum/minimal-prime comparison. There is
no finite-type, domain, reducedness or nontriviality assumption on A
or R. Empty fibres and zero tensor algebras have a vacuous component
condition, as in the underlying predicates.

`hasPureDimension_pullback_spec_iff` uses Mathlib's actual
`pullbackSpecIso` to identify pure dimension of Spec A ×[Spec R] Spec B
with pure ring dimension of A tensor_R B, for all commutative algebras.
It retains the componentwise condition rather than total dimension.
The proofs use scheme isomorphism invariance and the existing affine
comparison. Preservation and reflection under field extension, the
nonaffine dimension argument, constructibility and unrestricted
filtered fibre descent are separate remaining obligations.
