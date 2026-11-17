# Isomorphism representatives from uniquely normalized families

This internal construction converts classification data into a full relative
isomorphism representative. Let `a : AutomorphicAction A G`, let `Q` be a scheme
over `S`, and let `e : LocalGroupIso G H Q` be a natural family. Assume that, on
every scheme test `T`, the map sending `(d, q)` to the refinement of `e` at `q`,
precomposed with the action of `d⁻¹`, is bijective onto all natural local
isomorphisms over `T`.

`GroupIsomorphismScheme.ofNormalizedFamily` constructs the representative with
parameter `A.X ⊗ Q`. Its universal family is the refinement of `e` along the
second projection, twisted by the inverse first projection. The refinement
lemma evaluates this family at arbitrary test points. The categorical product
identifies points of the parameter with pairs `(d, q)`, so the assumed bijection
proves the representing property directly.

`ofNormalizedFamily_equivariant` proves that the canonical inverse-precomposition
action multiplies the first coordinate. The proof evaluates on all refinements,
uses `(d * x)⁻¹ = x⁻¹ * d⁻¹`, and applies the action's multiplication law.
`outerOfNormalizedFamily` then uses the published `outerOfProduct` construction,
with the identity product presentation, to obtain the exact outer quotient with
parameter `Q`. This last construction assumes that `A` is flat and
quasi-compact over the base.

The construction is derived from the existing `LocalGroupIso`,
`GroupIsomorphismScheme`, and `outerOfProduct` interfaces. It does not assert the
existence of the input classification data and assumes no prior isomorphism
representative.
