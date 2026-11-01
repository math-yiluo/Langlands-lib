# Actual connected-component schemes

This derived construction uses the published theorem
`locallyNoetherianConnectedComponentOpen_proof` and Mathlib's restriction of
schemes to open subsets. It supplies geometric prerequisites for the product
extension of a connected-base moduli functor. All schemes and their structure
sheaves are actual Mathlib schemes; restriction retains nilpotents.

For a locally Noetherian scheme `X`, the index is the actual quotient
`ConnectedComponents X`. The open subset `componentOpen X c` is the fiber
`{x | ConnectedComponents.mk x = c}`. Quotient surjectivity identifies it with
`connectedComponent x` for any representative, and the published openness
theorem proves that it is open. `componentScheme X c` is the restriction of
`X` to this open subset, with its actual inclusion `componentι`.

Each component scheme is connected and locally Noetherian. Distinct component
opens are disjoint and their supremum is the whole space.
`componentOpenCover` constructs the resulting actual scheme open cover.
No finiteness of the component set or quasi-compactness is assumed.

`componentMap f` is Mathlib's induced map on topological connected components
for the continuous map underlying `f`. Its formula on point classes, identity,
and composition are proved. For a source component `c` and target component
`d`, `componentHomTo f c d e` restricts `f`, where
`e : componentMap f c = d` identifies the target index. This equality is not an
assumption that a morphism exists: continuity proves the needed containment,
and restriction constructs the morphism.

The inclusion square is proved, and it uniquely determines the factorization
because an open immersion is a monomorphism. Uniqueness proves identity and
composition. `componentHom` selects the image component automatically.
`componentHomTo_eqToHom` proves compatibility with equality transport of a
target index. Thus arbitrary scheme morphisms, including nonflat ones, induce
coherent actual component maps.

On a preconnected scheme, every component open, if indexed, is the whole
scheme; `componentInclusionIso` constructs the canonical isomorphism and proves
that its map is the inclusion. For an empty scheme, `componentIndex_isEmpty`
proves that the actual component index is empty. Consequently products indexed
by these components can have the required empty-product behavior.

These definitions and intrinsic proofs are derived geometric infrastructure,
not a representability theorem or a construction of Shimura scheme levels.
The proof route is exactly the one above: published openness, actual open
restriction, continuity, and monomorphism cancellation. No further literature
assertion is introduced.
