# A primitive for the central defect after local Galois refinement

Let a central isogeny over `F` and a natural cocycle on a normal
coefficient cover `L/F` be given, with central lift data over `L`.
Suppose the cocycle is trivial on the pullback cover over a
characteristic-zero field `K`. Let `M/K` be a finite normal coefficient
extension with compatible embeddings of `K` and `L` over `F`.

`IsCentralIsogeny.HasPrimitiveAfterLocalRefinement` asserts that there
is a finite Galois extension `N/K` containing `M` and a primitive in
the central kernel points over `N` for the restricted multiplication
defect. The theorem `exists_primitive_of_baseChange_isTrivial`
establishes this assertion. It first evaluates the trivializing cochain on the pullback
cover at the point induced by `M`. The corresponding point of the
base-changed target group lifts through the base-changed central
isogeny over `N`. The actual base-change equivalences identify its
image with the extension of the original trivializing point.

Restriction of automorphisms and extension of points commute through
the coefficient tower. Thus the coboundary of the lifted point extends
the restricted cocycle values. Applying central exactness gives the
primitive over `N`. This internal result applies to an extension of a
completion and also to other base fields satisfying its hypotheses.
