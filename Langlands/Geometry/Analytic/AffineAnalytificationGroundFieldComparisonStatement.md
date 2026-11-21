# Strong comparison of the two affine ground field extensions

`AffineAnalytification.AffineAnalytificationGroundFieldComparisonStatement`
states a comparison between two actual atlases over `L`. Let `K` and `L` be
complete nontrivially normed ultrametric fields with `NormedAlgebra K L`.
Let `A` be a commutative `K`-algebra with finite polynomial presentation `P`.
The field universes and the universe of `A` are independent. The field
extension is not required to be finite or algebraic.

Write `Q := baseChangePresentation K L P`, the presentation of `L ⊗[K] A`
using the scalar-extended generators. The source `S` is the ground field
extension of the original affine analytification atlas for `P`: its charts
are the scalar-extended original chart algebras and its space is their
actual quotient by common subcharts. The target `T` is the affine
analytification atlas for `Q`, with its own radius exhaustion over `L`.
The two sets of chart indices need not agree.

The target asserts existence of a `CompatibleStrongHom S T` whose underlying
strong map is a full quasi-isomorphism. In particular, its ambient map is
a homeomorphism, and its pullback represents the source image as an affinoid
domain at every admissible pair. The comparison obeys two further conditions:

- On the underlying spaces, its composite with `baseChangeMap K L P` is the
  actual scalar-extension projection of the atlas for `P`.
- At each admissible pair of original chart indices `i` and `j`, the bounded
  pullback sends the target chart's image of `1 ⊗ a` to the image under
  `iota` of the original source chart's image of `a`, for every `a : A`.

The second condition compares the algebra maps, not just values of
multiplicative seminorms. With a proof, the full quasi-isomorphism gives an
isomorphism after saturating these presentations and applying localization.
This statement concerns the extension of the original affine presentation,
not an identification with the extension functor applied to an already
saturated or localized object. It does not yet assert naturality, the
nonaffine scheme and algebraic-space comparisons, or transitivity.

This is a derived statement in the Library's analytic atlas model. Its
source motivation is the usual isomorphism for algebraic schemes recalled
in Conrad–Temkin, *Non-archimedean analytification of algebraic spaces*
(2009), Theorem 2.3.5, printed p. 13 (PDF p. 13), registered as
`conrad-temkin-2009-nonarchimedean-analytification`. Conrad uses ground field
compatibility in the final paragraph of the proof of Proposition 5.11(3),
p. 19 of *Weil and Grothendieck approaches to adelic points* (2011),
registered as `conrad-2011-weil-grothendieck-adelic-points`. The particular
strong map and its chart equations are implementation targets, not claims
that these sources state the result with the Library's two chosen atlases.
