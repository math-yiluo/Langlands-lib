# Norm characters and the integer centralizer valuation

Author: Worker 1045.

This internal module relates the published norm character
`Langlands.Plancherel.TorusNormKernel.normCharacter` to the integer
centralizer valuation `Langlands.Geometry.Building.IntegerValuation.centralizerValuation`.
All statements hold at an arbitrary universe `u`.

The setting is a finite field extension `E / k` (`FiniteDimensional k E`), a
commutative group scheme `S` and a group scheme `Z` over `Spec k`, both with
affine underlying schemes, and a homomorphism `s : S.toGrp ⟶ Z`. Let `α` be a
rational character of the base change `Z_E = baseChanged k E Z` and
`a : characterLattice S` a character of `S`. The main hypothesis `hα` says that
the restriction of `α` along the base change `s_E` of `s` is the base change to
`E` of the `k`-character of `S` corresponding to `a`:

```text
characterRestrict (s_E) α = baseChange_E ((equivCharacterLattice S).symm a).
```

Under `hα`, with `ν = centralizerValuation v s h` built from a valuation
`v : Valuation k (WithZero (Multiplicative ℤ))` and a proof `h` that `Cartan.restrictionEvaluation s` is
bijective, the main formula is

```text
order v (N_{E/k}(α(z_E))) = [E : k] * ⟨a, ν(z)⟩      for every z ∈ Z(k).
```

Here `order v` is the real order `-log v` used by `KPApartmentData`, `z_E` is
`GaloisPointComparison.rationalExtend k E Z z`, and `⟨a, ν(z)⟩` is
`RealTorusSpace.eval S a (ν z).toAdd`. The formula uses no valuation on `E`, no
Galois or henselian hypothesis and no centralizer or reductivity hypothesis
beyond the bijectivity `h`. If the order of `v` extends to an additive
valuation `w` of `E` with `w(x) = order v (N_{E/k}(x)) / [E : k]` on units, the left side of `characterNormOrder_eq_eval` is `w(α(z_E))`, so
the integer centralizer valuation also computes the valuations of characters
that are only defined over `E`. This module does not construct such a `w`.

## Declarations

In namespace `Langlands.Plancherel.TorusNormKernel`, with `F E` fields,
`Algebra F E`, and `H T` group schemes over `Spec F`:

- `pointE_comp f y`: for `f : H ⟶ T` and a point `y` of `H` with coefficients in
  an `E`-algebra `D`, `pointE` of the image point `y ≫ f` is `pointE y`
  followed by the base change of `f`.
- `valueE_characterRestrict f χ y`: the value `valueE` of the restriction of an
  `E`-character `χ` of `T_E` along the base change of `f` at `y` is the value of
  `χ` at the image point `y ≫ f`.
- `valueE_baseChange χ y`: for an `F`-character `χ` of `T`, the value of its base
  change at `y` is the affine unit `Gm.affineUnitsEquiv (y ≫ χ)`.
- `affineUnitsEquiv_nsmul n χ A y`: over any commutative ring, the affine unit
  value of `n • χ` at `y` is the `n`-th power of the value of `χ`.
- `normCharacter_characterRestrict f χ` (needs `FiniteDimensional F E` and
  affine `H`, `T`): norm characters commute with restriction,
  `characterRestrict f (normCharacter χ) = normCharacter (characterRestrict f_E χ)`.
- `normCharacter_baseChange χ` (needs `FiniteDimensional F E` and affine `T`):
  `normCharacter (baseChange_E χ) = Module.finrank F E • χ`, as rational
  characters, not only on rational points.

In namespace `Langlands.Geometry.Building.IntegerValuation`, in the setting
above:

- `characterRestriction_normCharacter s hα`:
  `Cartan.characterRestriction s (normCharacter α) = Module.finrank k E • a`.
- `order_normCharacter v s h hα z`:
  `order v (rationalCharacterEval (normCharacter α) z) =
  Module.finrank k E * RealTorusSpace.eval S a (centralizerValuation v s h z).toAdd`.
- `order_norm_rationalCharacterEval v s h hα z`: the same right-hand side
  equals `order v` of the unit
  `Units.map (Algebra.norm k) (rationalCharacterEval α (rationalExtend k E Z z))`.
- `characterNormOrder v α z : ℝ`, a `def`: that order of the norm unit divided
  by `Module.finrank k E`. It depends only on `v`, `α` and `z`.
- `characterNormOrder_eq_eval v s h hα z`:
  `characterNormOrder v α z = RealTorusSpace.eval S a (centralizerValuation v s h z).toAdd`.

## Proofs

Both character identities are proved by the published extensionality theorem
`rationalCharacters_ext_affinePoints`: rational characters of an affine group
scheme agree if they agree on points with coefficients in every algebra `A`.
Both sides are compared after the injective map `Gm.affineUnitsEquiv`.

1. `pointE_comp` follows from injectivity of `baseChangePointsEquiv`, the
   characterization `baseChangePointsEquiv_pointE`, and
   `baseChangePointsEquiv_comp`. `valueE_characterRestrict` unfolds
   `valueE_apply` and applies `pointE_comp`.
2. `valueE_baseChange` combines the published
   `rationalCharacters.characterEval_baseChange` with
   `baseChangePointsEquiv_pointE` and `characterEval_naturality`.
   `affineUnitsEquiv_nsmul` uses `characterEval_zsmul`.
3. For naturality, the published `normCharacter_affinePoints` writes both sides
   as the tensor norm of a value on `T(E ⊗ A)`. `valueE_characterRestrict`
   identifies the two values, because the point map along
   `A → E ⊗ A` commutes with composition by `f`.
4. For base change, `normCharacter_affinePoints` and `valueE_baseChange` reduce
   the left side to the tensor norm of the image of `y ≫ χ` under
   `A → E ⊗ A`. By `Gm.affineUnitsEquiv_naturality` this image is the scalar
   `1 ⊗ (y ≫ χ)`, so the published `Langlands.Algebra.tensorNorm_scalar` gives
   its `[E : k]`-th power. `affineUnitsEquiv_nsmul` identifies the right side.
5. `characterRestriction_normCharacter` unfolds
   `Cartan.characterRestriction` as `equivCharacterLattice` after
   `characterRestrict`, then applies naturality, `hα`, the base-change formula
   and additivity of the lattice equivalence.
6. `order_normCharacter` rewrites the left side with the published
   `centralizerValuation_spec`, so it becomes `eval` of
   `characterRestriction s (normCharacter α)` at `ν(z)`. Step 5 makes this
   `eval S ([E : k] • a)`. Linearity of the pairing, through
   `RealTorusSpace.eval_eq_pair`, gives the product.
7. `order_norm_rationalCharacterEval` applies the published
   `normCharacter_eval`: the value of `normCharacter α` at `z` is the field norm
   of the value of `α` at `z_E`.
8. `characterNormOrder_eq_eval` divides step 7 by `[E : k]`, which is nonzero
   by `Module.finrank_pos`.

## Provenance and scope

This is a derived module assembled from existing Library declarations. It has
no independent literature assertion or source citation. The norm-character
construction and its evaluation formula are published in
`Langlands.Representation.Plancherel.TorusNormKernel.NormCharacter`. The integer
centralizer valuation and its defining property `centralizerValuation_spec` are
published in `Langlands.Geometry.Building.IntegerCentralizer`.

It is a partial contribution toward task 8ffe0456 (quasi-split apartments over
henselian integer-valued fields). It provides the character-valuation part of
the compatibility between centralizer and root-group valuations. It does not
construct root-group coordinates, prove their equivariance under the
centralizer, construct an extension of `v` to `E` or any apartment, or prove
`IntegerValuation.IsOmegaCompatible`.
