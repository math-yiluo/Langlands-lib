# Geometric reduction of the product-units theorem

This module defines the affine input `Langlands.GroupScheme.UnitsProduct.AffineSplitting`
and proves
`Langlands.GroupScheme.UnitsProduct.geometric_reduction`:
that input implies the unchanged
`Langlands.GroupScheme.UnitsProductDecompositionStatement` in every universe.
The module does not discharge the affine input and is therefore an intermediate
unit of Task 6784, rather than a closed proof of Milne's proposition.

The mathematical source is James S. Milne, *Algebraic Groups* (2017),
Proposition 12.48, printed pages 246–247 (PDF pages 262–263), registered as
`milne-2017-algebraic-groups`, content SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The checked 2017 errata contain no correction to this proposition. The
normalization identity is the one used at the start of Milne's proof. The
conditional interface, categorical restriction lemma and dense-open reduction
are internal infrastructure derived from that identity; they do not assert
Milne's compactification or divisor argument.

`AffineSplitting` quantifies over algebraically closed fields and pairs of
affine integral schemes locally of finite type over their spectra. Every
morphism from their fiber product to the actual multiplicative group scheme
must split as a product of the two pullbacks. Local finite type is sufficient
here: these affine schemes over a field are quasi-compact and separated. The
definition uses the existing cartesian monoidal structure on schemes over the
base and its actual group operation on morphisms to `Gm`.

The implemented proof proceeds as follows.

1. In a cartesian monoidal category with a compatible braided structure and a
   commutative group object, `normalized_of_split` rewrites a split morphism
   using its restrictions to the two axes through chosen points, divided by
   its value at the pair of points. Pullback preserves multiplication;
   the product projections and uniqueness of maps to the terminal object
   reduce the formula to cancellation in a commutative group.
2. `split_of_restriction` forms those axis restrictions on the larger objects.
   If restriction along a product morphism is injective, the normalized
   identity for the restricted morphism proves a global splitting. The
   constant inverse is absorbed into the second factor.
3. `exists_pointed_affine_chart` takes a chart from the scheme's affine cover
   containing an existing point. Its source is nonempty, affine and integral,
   and its structure map is locally of finite type. The published
   `SeparatingLineBundle.exists_rationalPoint_mem_of_isOpen`, applied to the
   empty finite family of opens, supplies a rational point on the chart.
4. `geometric_reduction` applies the affine hypothesis to two such charts.
   The published
   `P2MW.S_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed.solution`
   proves geometric integrality of the first factor. Mathlib's integral
   product instance applies because structure maps to a field are flat and
   universally open and the second factor is locally noetherian.
   The product of the two chart inclusions is an open immersion with nonempty
   source, so its image is dense in the integral product. The multiplicative
   group has separated structure morphism: it is a base change of the
   affine morphism from the spectrum of the integral Laurent polynomial ring.
   Mathlib's `ext_of_isDominant_of_isSeparated` now proves the required
   injectivity of restriction from the reduced product.

The final theorem accepts all hypotheses of the original target. Its proof
needs no extra hypotheses; quasi-compactness and separatedness of the two
input varieties are not needed for this conditional geometric step.
The remaining affine theorem is the substantive missing input.
