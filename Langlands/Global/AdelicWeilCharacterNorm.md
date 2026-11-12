# Adelic evaluation of Weil norm characters

For arbitrary number fields `F` and `L` in a common universe, a specified
algebra `F → L`, and an affine group scheme `G` locally of finite type over
`Spec L`, `AdelicWeilRestriction.normCharacter` is the actual ground-field
character of `AffineWeil.groupScheme F L G` associated to any original
`L`-rational algebraic character of `G`. It uses the constructed actual
`AffineWeil.normCharacter`, restriction of the original morphism followed
by the determinant norm. The original group need not be commutative,
connected or reductive.

`character_normCharacter_apply` proves that evaluating the transferred
character at any ground-field adelic Weil point is exactly the original
full idele norm of the original character evaluated after the fixed
canonical `adelicPointsEquiv`. More explicitly,

`character F (AffineWeil.groupScheme F L G) (normCharacter F L G χ) g`

equals

`ideleNorm (character L G χ (adelicPointsEquiv F L G g))`.

Every map in this identity is the original actual map, and every infinite
and finite place is retained. `character_normCharacter` expresses the
same identity as equality of idele-valued group homomorphisms.

The proof combines the all-affine-test determinant norm-character formula,
the full adelic determinant/local norm comparison on units, and
naturality of actual character evaluation under the canonical tensor map.
The first formula rewrites the transferred character to a tensor unit
norm. The second replaces that determinant norm by the original full
idele norm after `numberFieldAdeleTensorEquiv`. Finally,
`characterUnits_naturality` identifies the tensor-map image of the original
tensor-valued character with the original character of the canonical
adelic Weil image.

This is internal derived content using those proved constructions.
It does not compare normalized
idelic absolute values or classify all characters of a Weil restriction,
and does not prove the norm-one subgroup equality or quotient compactness.
