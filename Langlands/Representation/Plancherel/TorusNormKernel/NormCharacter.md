# Norms of characters after a finite field extension

Author: Worker 1505.

This is a derived construction for the
[torus norm-kernel compactness proof](../TorusNormKernelCompactnessProof.md).
Declarations are in the namespace `Langlands.Plancherel.TorusNormKernel`.

Let `F` and `E` be fields in one universe `u`, with `Algebra F E`. Let `T` be an
actual group scheme over `Spec F`, and `T_E` its actual base change
`GaloisPointComparison.baseChanged F E T`. From an actual character
`χ : rationalCharacters T_E`, the module constructs a rational character
`normCharacter χ : rationalCharacters T` of `T` over `F`. Its main property is:

```text
normCharacter_eval :
  (rationalCharacterEval (normCharacter χ) t : F)
    = Algebra.norm F (rationalCharacterEval χ (rationalExtend F E T t) : E)
```

for every rational point `t`, where `rationalExtend` is the published extension
of rational points to `T_E`. This requires `[FiniteDimensional F E]` and
`[IsAffine T.X.left]`. No Galois, separability, splitting or torus hypothesis
is used.

## Values on coefficient points

For an `E`-algebra `D` with a compatible `F`-algebra structure:

- `specRestrictIso F E D` identifies `Spec D` over `Spec E`, regarded over
  `Spec F`, with `Spec D` over `Spec F` (identity on schemes).
- `pointE F E D T` is the multiplicative equivalence between points of `T`
  with coefficients in `D` and points of `T_E` with coefficients in `D`. It is
  this isomorphism of test objects followed by the inverse of the published
  pullback adjunction `baseChangePointsEquiv`. `pointE_naturality` proves
  compatibility with every `E`-algebra map `D → D'`, using the adjunction
  naturality `baseChangePointsEquiv_naturality`.
- `valueE χ D` applies `χ` to `pointE` and reads off the unit of `D` by
  `Gm.affineUnitsEquiv`. `valueE_naturality` follows from `pointE_naturality`,
  `affinePointsTarget_naturality` and `Gm.affineUnitsEquiv_naturality`.

## The homomorphism to the Weil restriction

Assume `T` is affine. The published `AffineCoordinates` interface gives a
corepresented point functor of `T` and an isomorphism
`AffineCoordinates.groupSchemeIso T` to `T`. `coordinatePoints C` turns its
`C`-points into actual `C`-points of `T`, naturally in `C`
(`coordinatePoints_naturality`).

- `weilApp χ C` sends a coordinate point to
  `valueE χ (E ⊗[F] C)` of its image under `C → E ⊗[F] C`. This is a unit of
  `E ⊗[F] C`, a point of the published functor `WeilGm.functor F E` of
  `Res_{E/F} 𝔾ₘ`. `weilApp_naturality` proves compatibility with `C → C'`:
  the two algebra maps `C → E ⊗ C'` agree, and `valueE_naturality` applies
  along `lTensor E φ`.
- `weilNatTrans χ` is the resulting natural transformation of group-valued
  functors. `weilHom χ : T ⟶ WeilGm.groupScheme F E` is
  `(groupSchemeIso T).inv` followed by the published
  `Corepresented.groupSchemeMap`.
- `normCharacter χ` is `weilHom χ` followed by the published norm homomorphism
  `WeilGm.norm F E : Res_{E/F} 𝔾ₘ ⟶ 𝔾ₘ`.

## Evaluation

- `weilNorm_affinePoints`: on an affine test `Spec A`, the Weil norm is
  `tensorNormUnits` of the corepresented coordinates. The proof combines
  `WeilGm.norm_points` on the test `Spec A` with the published comparison
  `Corepresented.map_affineSectionsIso_pointsEquiv` and
  `affineSectionsIso_hom_ringHom`, which identify relative global sections of
  `Spec A` with `A`. It also uses `tensorNormUnits_naturality`.
- `normCharacter_affinePoints`: for an `A`-point `y` of `T`, the value of
  `normCharacter χ` is `tensorNormUnits` of `valueE χ (E ⊗[F] A)` at `y`
  extended to `E ⊗[F] A`. It uses `Corepresented.groupSchemeMap_affinePoints`
  and cancels `groupSchemeIso`.
- `rationalCoeffEquiv_comp`, `rationalCoeffEquiv_eq_comp`,
  `pointE_baseChangeCoeffEquiv` and `valueE_baseChangeCoeffEquiv` compare the
  rational-point conventions. On rational points of `T_E`, `valueE χ E` of the
  published `baseChangeCoeffEquiv` is `rationalCharacterEval χ`. The proof
  checks the two projections into the actual pullback and uses the published
  `gm_units_rationalCoeffEquiv`.
- `normCharacter_eval` takes `A = F`. The point `y₀ = rationalCoeffEquiv t`
  extended to `E ⊗[F] F` and then along `E ⊗[F] F ≃ₐ[E] E`
  (`Algebra.TensorProduct.rid`) is `GaloisPoint.extend y₀`, which corresponds
  to `rationalExtend t`. The tensor norm of `E ⊗[F] F` over `F` is the field
  norm of `E` over `F`, by `Algebra.norm_eq_of_algEquiv` for
  `Algebra.TensorProduct.lid` and a tensor induction.

Provenance: internal derived construction. It combines the published
Weil-restriction group scheme `Res_{E/F} 𝔾ₘ` and its determinant norm, the
`Corepresented` group-scheme maps from natural transformations, the
`AffineCoordinates` model of affine groups, the base-change point adjunction,
and the published Galois point comparisons. The mathematical idea is the
standard norm of a character over a finite extension (see the statement page
of `TorusNormKernelCompactnessStatement`). This implementation uses the
determinant norm of `E ⊗[F] -` and needs no Galois descent of characters.
