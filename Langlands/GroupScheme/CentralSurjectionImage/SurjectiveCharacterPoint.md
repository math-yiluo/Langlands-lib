# Points of infinite order for surjective characters

Author: Worker 1387.

This internal module, in the namespace
`Langlands.GroupScheme.CentralSurjectionImage`, works over a field `k : Type u`.

- `characterValue_id`: the identity character of `𝔾_m` evaluates a point to
  its unit under `Gm.affinePointsEquiv`.
- `X_pow_ne_one`: no positive power of the variable is `1` in
  `FractionRing (Polynomial k)`, by comparing degrees.
- `exists_isAlgClosed_compositum`: field maps `F → A` and `F → B` admit
  compatible maps of `A` and `B` into one algebraically closed field. Take an
  algebraic closure of a residue field of the nonzero ring `A ⊗[F] B`.
- `exists_point_of_surjective`: let `Z` be a commutative group scheme over `k`
  and `χ` a rational character with surjective underlying morphism of schemes.
  Then some point `x` of `Z` over an algebraically closed field `K` has no
  positive power of `χ(x)` equal to `1`. Here `L = FractionRing (Polynomial k)`.
  The point `y` of `𝔾_m` over `L` with value `X` maps the closed point of
  `Spec L` to some `s`; surjectivity gives `z` with `χ(z) = s`. Write
  `y = Spec(α) ≫ fromSpecResidueField s` (Mathlib's
  `descResidueField_stalkClosedPointTo_fromSpecResidueField`). Compare it with
  `fromSpecResidueField z ≫ χ`, using `SpecMap_residueFieldMap_fromSpecResidueField`
  and `residueFieldCongr_fromSpecResidueField`. Then embed `κ(z)` and `L`
  compatibly over `κ(s)` into an algebraically closed field `K`, made a
  `k`-algebra through `L`. This gives a point `x` of `Z` over `K` with
  `x ≫ χ = y_K`, so `χ(x)` is the image of `X`.
- `exists_gm_characterRestrict_ne_zero_of_surjective`: suppose `Z` is affine and
  locally of finite type over `k`, and `χ` has surjective underlying morphism of
  schemes. Then some cocharacter `𝔾_m ⟶ Z` over `k` restricts `χ`
  nontrivially. This combines the previous item with
  `exists_gm_characterRestrict_ne_zero_of_point` (from `CocharacterFromPoint`).
  No smoothness, connectedness or multiplicative-type hypothesis is imposed.

The last result is the standard fact that a commutative affine algebraic group
mapping onto `𝔾_m` contains a cocharacter with nonzero image. The proof here is
internal and derived; no literature result is attributed to it.
