# Localization of the finite rational algebra sheaf over a chart

This internal construction compares actual algebra sheaves on a slice of the
finite rational chart site. Let `K` be a complete ultrametric normed field, `A`
an actual presented affinoid algebra, and `d : RationalChart K A`. There are no
strictness, nontrivial-valuation, reducedness or proper-ideal hypotheses.

`relativeChartFunctor d` sends an object `U` of `Over d`, consisting of an
actual bounded restriction `U.left ⟶ d`, to
`pullback d.baseMap U.left`, a rational chart over the actual localized algebra
`d.algebra`. On arrows it uses `pullbackRestriction d.baseMap f.left`.
The source carries Mathlib's topology `(finiteRationalTopology K A).over d`.
The functor is continuous by composition of the continuous slice forgetful
functor and the previously proved continuous coefficient-pullback functor.

`relativeAlgebraSheaf d` is the continuous direct image of
`algebraSheaf K d.algebra` along that functor. Its value at `U` is the actual
commutative `K`-algebra `(pullback d.baseMap U.left).algebra`, and its restriction
along `f` is the underlying algebra map of
`pullbackRestriction d.baseMap f.left`. Its sheaf property follows from
continuous direct image and the unconditional finite rational sheaf theorem.

`relativeAlgebraSheafIso d` is an isomorphism of sheaves

```text
(algebraSheaf K A).over d ≅ relativeAlgebraSheaf d.
```

At `U` its forward map is `pullbackMap d.baseMap U.left`; its inverse is
`U.hom.relativeInverse`. These are the underlying algebra maps of the already
constructed bounded equivalence `U.hom.relativeEquiv`. That equivalence uses
the rational quotient pushout and uniqueness of bounded maps out of a rational
quotient. Naturality of the forward components is exactly
`pullbackRestriction_comp_pullbackMap`; the component equivalences then give
the isomorphism of presheaves and hence of the bundled sheaves.

The component and inverse formulas are explicit in Lean. For each
`a : d.algebra`, the structural-map equations are

```text
comparison_U (U.hom.restriction a)
  = (pullback d.baseMap U.left).baseMap a,
comparison_U⁻¹ ((pullback d.baseMap U.left).baseMap a)
  = U.hom.restriction a.
```

They are the existing bounded equations
`Restriction.pullbackMap_comp_restriction` and
`Restriction.relativeInverse_comp_baseMap`, evaluated at `a`.
The forward component is also exactly the `U.left` component of the
coefficient sheaf morphism `algebraSheafMap d.baseMap`.

The comparison concerns the stated sheaves on the slice site. It does not
construct an equivalence of sites, identify all rational charts over
`d.algebra` with ambient charts, or supply an analytic atlas. Extension to the
full analytic G-topology, locally ringed spaces, and higher acyclicity remain
separate obligations.

The provenance is internal: Worker 36 applies Mathlib's slice topology and
continuous direct image to the published `RationalChartAlgebraSheaf`,
`RationalChartRelativeComparison`, and `RationalChartCoverBaseChange`
constructions. No additional assertion from the original literature is used
in this categorical comparison.
