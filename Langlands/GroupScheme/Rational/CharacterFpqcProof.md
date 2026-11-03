# Nonzero characters of split tori are fpqc quotients

This file proves `Langlands.GroupScheme.RelativeRoot.CharacterFpqcStatement`
([`RootSubgroupStructureStatement`](RootSubgroupStructureStatement.md)) as the theorem
`Langlands.GroupScheme.RelativeRoot.characterFpqc`, at every universe `u`. Let `k` be a field
and `S` a commutative group scheme over `Spec k` whose underlying group scheme is a split
torus. Let `a` be a nonzero element of `characterLattice S`. Then the underlying scheme morphism
of `CommGroupScheme.groupHom a : S → 𝔾_m` is quasi-compact, flat and surjective. The
character need not be primitive, and `k` may have any characteristic. The proof uses nothing
beyond the hypotheses of the statement.

The statement is the quotient `S / ker(a) ≅ 𝔾_m` of KP §2.6.3 (printed p. 94). The Lean
proof does not construct the kernel or the quotient. It identifies `a` with the morphism of
diagonalizable group schemes induced by an injective lattice map, and uses the helper module
[`DiagonalizableFaithfullyFlat`](../Torus/DiagonalizableFaithfullyFlat.md).

## The lattice map `n ↦ n • m`

All declarations of this section and the next two are in
`Langlands.GroupScheme.RelativeRoot.CharacterFpqc`.

- `scaleHom m : (PUnit → ℤ) →+ (I → ℤ)` sends `f` to `f () • m` (`scaleHom_apply`). The
  source `ℤ` is written as `PUnit → ℤ` so that it is a type in universe `u`, as `D(Λ)` needs.
- `scaleHom_injective`: if `m ≠ 0` then `scaleHom m` is injective, since `ℤ^I` is torsion
  free (Mathlib's `smul_left_injective`).

## Points of the comparison isomorphisms

- `splitIso_hom_points`: on `T`-points, the published splitting
  `Diagonalizable.splitIso R b : D(Λ) ≅ 𝔾_m^J` (for `b : Λ ≃+ ℤ^J`) sends a point `x` to the
  family `Diagonalizable.splitPointsEquiv R b T x` of units. This is the published
  `isoOfPointModels_hom` for the point models that define `splitIso`.
- `gmIso_inv_points`: on `T`-points, the inverse of the published
  `splitTorus.gmIso S : 𝔾_m ≅ 𝔾_m^{PUnit}` reads off the only coordinate. This is the
  published `isoOfPointModels_inv` for the point models that define `gmIso`, evaluated at the
  only index.

## Characters of split tori as maps of diagonalizable group schemes

- `splitIso_hom_comp_characterLatticeEquiv_symm k I m`: let `I` be a finite type with
  decidable equality and `m : I → ℤ`. Let `χ_m : 𝔾_m^I → 𝔾_m` be the character
  `(splitTorus.characterLatticeEquiv k I).symm m`. Then `splitIso ≫ χ_m` equals the composite
  `D(ℤ^I) → D(PUnit → ℤ) ≅ 𝔾_m^{PUnit} ≅ 𝔾_m` of `Diagonalizable.restrictMap (scaleHom m)`,
  the splitting `splitIso` of `D(PUnit → ℤ)`, and `gmIso.inv`. Both splittings use
  `AddEquiv.refl`.

  The proof compares `T`-points (`hom_ext_points`) after applying the injective map
  `Gm.pointsEquiv`. Write a `T`-point `x` of `D(ℤ^I)` as a character `ψ` of `ℤ^I` with values
  in `Γ(T, 𝒪_T)ˣ`. On the left, the published `pointsEquiv_characterLatticeEquiv_symm`
  computes the image as `∏ i, tᵢ ^ mᵢ`, where `t` is the family of units of `x` under
  `splitIso`. On the right, `gmIso_inv_points`, `splitIso_hom_points` and
  `Diagonalizable.pointsEquiv_restrictMap` compute the image as `ψ(1 • m) = ψ(m)`. These agree
  because `ψ` is recovered from `t` by the published `Diagonalizable.charEquiv`, whose inverse
  sends `t` to the character `n ↦ ∏ i, tᵢ ^ nᵢ`.

## The theorem

`characterFpqc` proves `CharacterFpqcStatement.{u}` as follows. Let `S` be given with an
isomorphism `e : S ≅ 𝔾_m^I` for a finite type `I` (the hypothesis `IsSplitTorus S.toGrp`), and
let `a ≠ 0`.

1. Let `χ` be the character `e.inv ≫ a` of `𝔾_m^I`. Then `a = e.hom ≫ χ`.
2. Let `m := splitTorus.characterLatticeEquiv k I χ`, so that
   `χ = (characterLatticeEquiv k I).symm m`. If `m = 0` then `χ = 0` and `a = 0`. So `m ≠ 0`.
3. By `splitIso_hom_comp_characterLatticeEquiv_symm`, `groupHom a` equals
   `E₁.hom ≫ restrictMap (scaleHom m) ≫ E₂.hom` for isomorphisms of group schemes
   `E₁ : S ≅ D(ℤ^I)` and `E₂ : D(PUnit → ℤ) ≅ 𝔾_m`. So its underlying scheme morphism is the
   composite of the underlying scheme morphisms of these three maps.
4. The underlying scheme morphisms of `E₁.hom` and `E₂.hom` are isomorphisms, because functors
   preserve isomorphisms.
5. `k` is a nonzero ring and `scaleHom m` is injective (`scaleHom_injective`). So the
   underlying scheme morphism of `restrictMap (scaleHom m)` is flat and surjective
   (`Diagonalizable.flat_and_surjective_restrictMap`). It is
   `Spec.map (mapDomainRingHom (scaleHom m))` (`Diagonalizable.restrictMap_left`), a morphism
   of affine schemes, hence affine and therefore quasi-compact.
6. Isomorphisms are quasi-compact, flat and surjective, and the three properties are stable
   under composition. Mathlib's instances for composites conclude.
