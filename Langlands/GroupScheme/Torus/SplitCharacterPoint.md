# Character values and the universal point of a split torus

This internal module works with an actual commutative group scheme `T` over
`Spec k`, for a field `k : Type u` in arbitrary universe, and with test algebras
`A : Type u` over `k`. All declarations are in namespace
`Langlands.GroupScheme.SplitCharacterPoint`.

## Character values

`value χ s : Aˣ` is the value of a character `χ : characterLattice T` at an affine
point `s : Lie.AffinePoints T.toGrp A`. It is the unit attached by the Library's
`Gm.affineUnitsEquiv` to the composite point `s ≫ χ` of the multiplicative group.

- `value_add`, `value_zero`: values of a sum of characters multiply, and the zero
  character has value one. `valueHom s` packages `χ ↦ value χ s` as a
  homomorphism from `Multiplicative (characterLattice T)`.
- `value_affineMap`: for an algebra map `f : A →ₐ[k] B`, the value at the
  coefficient change `Lie.affineMap T.toGrp f s` is `f` applied to the value at
  `s`. This is the Library's naturality `Gm.affineUnitsEquiv_naturality`.
- `value_comp_hom`: for a homomorphism `f : T'.toGrp ⟶ T.toGrp`, the value of
  `χ` at `s ≫ f` is the value of the restricted character
  `characterRestrict f χ` at `s`.

## Split tori

Assume `hT : IsSplitTorus T.toGrp`. `splitIndex hT` and `splitIso hT` are a chosen
finite index type `I` and isomorphism `T.toGrp ≅ splitTorus (Spec k) I`.

- `ext_of_isSplitTorus`: two points of `T` over the same algebra are equal when
  every character takes the same value at them. Under the isomorphism, the
  coordinates of a point of `𝔾_m^I` are the values of the restricted coordinate
  characters `splitTorus.proj`, and the Library's
  `splitTorus.algebraPointsEquiv` identifies a point with its coordinates.
- `monomialUnit χ` is the unit `single χ 1` of the group algebra
  `AddMonoidAlgebra k (characterLattice T)`. `monomialUnitHom T` is the
  corresponding monoid homomorphism.
- `universalPoint hT` is the point of `T` over this group algebra whose
  coordinates in the chosen splitting are the monomials of the coordinate
  characters `coordinateCharacter hT i`, the restrictions of `splitTorus.proj i`
  along the splitting.
- `value_universalPoint`: every character `χ` takes the value `monomialUnit χ` at
  `universalPoint hT`. The proof is `value_isoPoint`, stated for any splitting
  `e`. The character `χ` restricted along `e⁻¹` is the sum
  `∑ mᵢ • proj i` with `m` given by the Library's
  `splitTorus.characterLatticeEquiv` (`eq_sum_proj`). Restricting back along `e`
  writes `χ` as `∑ mᵢ • isoCoordinateCharacter e i`
  (`sum_isoCoordinateCharacter`, using `characterRestrict_hom_inv`). Values of an
  integral combination are the corresponding products of values
  (`value_sum_zsmul`). The coordinate values are the prescribed monomials
  (`value_proj_symm`), and the products of monomials are again monomials
  (`prod_monomialUnit_zpow`).
- `pointLift s` is the algebra map from the group algebra to `A` sending each
  monomial `single χ r` to `r` times the value of `χ` at `s`
  (`pointLift_single`). It is Mathlib's `AddMonoidAlgebra.lift` of `valueHom s`.
- `affineMap_pointLift`: every point `s` of a split torus over every algebra `A`
  is the coefficient change of `universalPoint hT` along `pointLift s`. Both points
  have the same character values, so `ext_of_isSplitTorus` applies.

## Provenance

This is internal infrastructure, with no literature claim of its own. It
combines the Library's split-torus coordinates
(`Langlands.GroupScheme.Torus.UniversalPoint`), its computation of the character
lattice of `𝔾_m^I` (`splitTorus.characterLatticeEquiv` in
`Langlands.GroupScheme.Torus.Lattice`), the actual multiplicative-group point
equivalence, and Mathlib's universal property of group algebras. It is the
standard description of a split torus as the spectrum of the group algebra of its
characters, specialised to what the torus restriction of class functions needs.
The module does not construct an isomorphism of coordinate algebras.
