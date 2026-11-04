# Finite-Galois fields of definition of actual cocharacters

Module `Langlands.GroupScheme.Torus.CocharacterFiniteGaloisDescent`, namespace
`Langlands.GroupScheme.CocharacterDatum`.

Let `k : Type u` be a field and let `Z` be an affine commutative group scheme
over `Spec k`. All fields and exponent groups in this module belong to the same
arbitrary universe. Write `Z_K` for the actual scheme pullback to `Spec K`.

For an additive commutative group `Λ` and a field extension `K/k`,
`baseChangedHomEquivMultiplicativePoints` is an equivalence

```text
Hom(D_K(Λ), Z_K) ≃ multiplicativePoints Z K Λ.
```

It composes the published actual-homomorphism/universal-point equivalence over
`K` with the actual pullback point equivalence. The corresponding
`gmHomEquivMultiplicativePoints` uses the standard isomorphism from `Gm_K` to
`D_K(PUnit → ℤ)`. Both equivalences send the zero homomorphism to the identity
point, as proved by the two `_zero` lemmas. These equivalences require no finite
type or finite extension assumption. They use the chosen diagonalizable
presentation; no compatibility with a separately chosen source base-change
isomorphism is claimed.

Assume in addition that the structure morphism of `Z` is locally of finite type.
For compatible fields `k → F → L`, with `L/F` Galois, the theorem
`IsMult.exists_finiteGalois_coeffMap_eq` says that any multiplicative point
`x` of `Z(L[Λ])` has a finite Galois intermediate field `N` of `L/F` and a
multiplicative point `y` of `Z(N[Λ])` whose coefficient extension is exactly
`x`. Here `L[Λ]` denotes `AddMonoidAlgebra L Λ`. The proof first invokes the
published finite-dimensional coefficient descent, then enlarges its intermediate
field to its normal closure inside `L`. Normality and separability of `L/F`
make this closure Galois, and finite dimensionality is preserved. Coefficient-map
composition preserves both the point and its multiplicativity. The extension
`L/F` itself need not be finite, and `Λ` need not be torsion free.

For the vanishing results, assume

```text
for every commutative group scheme T over k, if T is a torus,
then every f : T → Z has SubgroupFunctor.range f = ⊥.
```

The theorem `gm_hom_eq_zero_of_finiteGalois` kills every actual cocharacter
`Gm_K → Z_K` for finite Galois `K/k`. Indeed, `Res_{K/k}(Gm)` is a torus, so the
hypothesis makes the actual Weil transfer have bottom range and hence equal
zero. The transfer-detection theorem then makes the original cocharacter zero.
This result does not require the finite type assumption.

With the locally finite type assumption restored,
`multiplicativePoint_eq_one_of_isGalois` kills every multiplicative point over
`L[PUnit → ℤ]` for an arbitrary Galois extension `L/k`. Descend the point to a
finite Galois intermediate field `N`, reconstruct its actual cocharacter using
`gmHomEquivMultiplicativePoints`, and apply finite-Galois vanishing. The zero
comparison makes the descended point the identity, and coefficient extension
then gives the original point equal to the identity.

Finally, `gm_hom_eq_zero_of_isGalois` applies the same equivalence and its zero
comparison to conclude that every actual cocharacter `Gm_L → Z_L` is zero.
No smoothness, connectedness, perfectness, characteristic or cardinality
hypothesis is imposed in this module.

This is an internal deduction from the published coefficient descent and actual
point equivalences, Mathlib's finite normal closure construction, and the actual
Weil transfer and its detection theorem. It does not prove unipotence or assert
that all tori remain absent after arbitrary base change. The parent
`NoTorusUnipotentStatement` remains a separate proof obligation.
