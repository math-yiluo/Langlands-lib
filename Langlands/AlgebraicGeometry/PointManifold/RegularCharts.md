# Regular local charts on actual affine points

This internal construction interface separates local analytic output from
algebraic hypotheses. It uses the actual `RingPoint k X k` carrier and its
published global-section evaluation topology throughout. In particular, a
`RegularChart` is an open partial homeomorphism for that topology; topology
agreement is built into the type of this analytic output, rather than requiring
a later transport to a different point space.

A chart has model `Fin d → k`, viewed as a real normed space. Each forward
coordinate is a quotient of two global regular functions, with a nonzero
denominator on the source. Pullback of every global regular function along
the inverse is `ContDiffOn ℝ ∞` on the open target. These are local analytic
properties that must be established by a theorem using algebraic local
standard-smooth or étale presentations and the inverse or implicit function
theorem. They are not the definition of algebraic smoothness and are not
assumed in the eventual smooth-scheme existence theorem.

`RegularAtlas` selects such a chart around each actual point.
`RegularAtlas.chartedSpace` uses precisely those partial homeomorphisms, with
their range as its atlas. No new point carrier, topology, or global charted-space
instance is introduced. The existence of this data for an algebraically smooth
scheme, smooth compatibility of the charts, and the regular-function family
criterion are separate proof obligations.

`RegularAtlas.ofIsEmpty` constructs this data on an empty point space without a
positive-dimension or nonemptiness assumption. The real model dimensions are
proved separately: `d * Module.finrank ℝ k`, hence `d` for real points and `2*d`
for complex points. The model also permits `d = 0`; no nonzero dimension is
assumed anywhere in the definitions.

The provenance is internal. Rational chart coordinates express regular
functions on affine open neighborhoods as fractions of global regular
functions. The intended construction specializes the scheme case underlying
Conrad's Proposition 5.4 (printed pp. 15–16 of the registered December 31, 2011
notes, source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`).
Conrad's proposition supplies the mathematical motivation; these explicit
Lean chart fields and the real smooth family comparison are derived
interfaces, not a transcription of that proposition.
