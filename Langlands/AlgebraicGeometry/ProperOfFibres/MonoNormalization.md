# Finite normalization of a monomorphism of finite type out of an integral scheme

Module `Langlands.AlgebraicGeometry.ProperOfFibres.MonoNormalization`, namespace
`Langlands.AlgebraicGeometry.ProperOfFibres`.

This module is a step of the general properness criterion used for relative parabolic quotients.
Combined with Mathlib's Zariski main theorem it says: a quasi-compact monomorphism of finite type
`j : X ⟶ Y` out of an integral scheme, over a target whose affine rings of sections are finitely
generated over `ℤ`, factors as an open immersion `X ⟶ X'` followed by a *finite* morphism
`X' ⟶ Y`, where `X'` is the relative normalization of `Y` in `X`.

## Main statement

`isFinite_fromNormalization`. Let `j : X ⟶ Y` be a morphism of schemes (one universe `u`) with
`[Mono j] [LocallyOfFiniteType j] [QuasiCompact j]`, let `X` be integral (`[IsIntegral X]`), and
assume `hY`: for every affine open `U` of `Y`, the ring `Γ(Y, U)` is a finitely generated
`ℤ`-algebra. Then `j.fromNormalization : j.normalization ⟶ Y` is finite (`IsFinite`).

The relative normalization `j.normalization`, `j.toNormalization` and `j.fromNormalization` are
Mathlib's (`Mathlib.AlgebraicGeometry.Normalization`); `j` is quasi-separated because a
monomorphism is separated (Mathlib instance). With the same hypotheses on `j`, Mathlib's Zariski
main theorem instance makes `j.toNormalization` an open immersion (a monomorphism locally of finite
type is locally quasi-finite); this module does not restate that instance.

## Helper results

* `finite_integralClosure_of_forall_exists_mul_eq` (algebra). Let `A` be a finitely generated
  `ℤ`-algebra and `C` a domain which is an `A`-algebra, such that every `c : C` satisfies
  `c * b = a` (images in `C`) for some `a, b : A` with the image of `b` nonzero. Then the integral
  closure of `A` in `C` is a finite `A`-module.
* `surjective_residueFieldMap`: for `[Mono j] [LocallyOfFiniteType j]`, every residue field map
  `κ(j x) ⟶ κ(x)` is surjective.
* `surjective_stalkMap_genericPoint`: if moreover `X` is integral, the stalk map at the generic
  point of `X` is surjective.
* `exists_mul_eq_app`: if moreover `U` is an affine open of `Y` whose preimage contains the generic
  point, every `c : Γ(X, j⁻¹ U)` satisfies `c * j.app U b = j.app U a` for some `a, b : Γ(Y, U)`
  with `j.app U b ≠ 0`.

## Proof as implemented

1. **Algebraic finiteness.** Let `S` be the image of `A` in `C` (a subalgebra, a domain, finitely
   generated over `ℤ` as a quotient of `A`) and `L` the fraction field of `C`. The hypothesis shows
   that `L` is a fraction field of `S` (`IsFractionRing.of_field`): any element of `L` is `x / y`
   with `x, y ∈ C`, and both are quotients of elements of `S`. The Library theorem
   `Langlands.AlgebraicGeometry.NoetherianApproximation.integerFiniteTypeNormalization` (a
   finitely generated domain over `ℤ` has finite normalization in its fraction field), transported
   along `FractionRing S ≃ₐ[S] L` (`integralClosure_map_algEquiv`), makes `integralClosure S L` a
   finite `S`-module, hence a finite `A`-module (`S` is a quotient of `A`). The integral closure of
   `A` in `C` embeds `A`-linearly into it (via `C ⟶ L`, using `IsIntegral.tower_top`), and `A` is
   noetherian, so it is a finite `A`-module (`Module.Finite.of_injective`).
2. **Residue fields.** Let `x ∈ X`. The extension `κ(j x) ⟶ κ(x)` is separable, because a
   monomorphism locally of finite type is formally unramified (its diagonal is an isomorphism) and
   Mathlib provides `Algebra.IsSeparable` for residue field extensions of formally unramified
   morphisms. It is purely inseparable because a monomorphism is universally injective
   (`tfae_universallyInjective`). A separable purely inseparable extension is trivial
   (`IsPurelyInseparable.surjective_algebraMap_of_isSeparable`).
3. **Stalk at the generic point.** For integral `X`, the stalk at the generic point `η` is a field,
   so `X.residue η` is injective; surjectivity of the residue field map and of `Y.residue` gives
   surjectivity of the stalk map, by `Scheme.residue_residueFieldMap`.
4. **Fractions.** For affine `U` with `η ∈ j⁻¹ U`, the stalk of `Y` at `j η` is a localization of
   `Γ(Y, U)` (`IsAffineOpen.isLocalization_stalk`). Writing the preimage under the stalk map of
   the germ of `c` as `a / b`, the elements `c * j.app U b` and `j.app U a` have the same germ at
   `η`, so they are equal (`germ_injective_of_isIntegral`); `j.app U b ≠ 0` because its germ is a
   unit.
5. **Main theorem.** `j.fromNormalization` is affine (it is integral, Mathlib instance). For affine
   `U`, Mathlib's `fromNormalization_app` writes `j.fromNormalization.app U` as the algebra map
   `Γ(Y, U) ⟶ integralClosure Γ(Y, U) Γ(X, j⁻¹ U)` followed by an isomorphism
   (`normalizationObjIso`), so it suffices that this integral closure is a finite module. If
   `η ∈ j⁻¹ U`, then `Γ(X, j⁻¹ U)` is a domain and steps 1 and 4 apply with `hY U`. Otherwise
   `j⁻¹ U` is empty (a nonempty open contains the generic point), so `Γ(X, j⁻¹ U)` is the zero
   ring and the integral closure is trivially finite.

## Provenance

Internal. The algebraic core is the classical finiteness of normalization for finitely generated
domains over `ℤ` (Nagata), used through the published Library theorem named above. The
scheme-theoretic part (a monomorphism of finite type has trivial residue field extensions, so the
relative normalization in this birational situation is finite) is standard. The proof is a direct
assembly of Mathlib results and that Library theorem; no source assertion is assumed.
