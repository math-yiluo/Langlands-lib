# Lifting and descending points of group schemes along field extensions

This module proves three facts about points of affine-test group schemes over a field `k`.
All three concern a field extension `L/K` over `k`. They are helpers for
`Langlands.GroupScheme.Torus.InducedQuotientPointSurjectivityProof`. All declarations are in
namespace `Langlands.GroupScheme.FieldPoints`.

Notation: for a `k`-algebra `A`, `Lie.AffinePoints H A` is the group of morphisms
`Spec A ⟶ H` over `Spec k`. `Lie.affineMap H φ` is restriction along a `k`-algebra map `φ`.

## Provenance

The content is internal and derived from standard scheme theory.

- The lift is the usual construction of a point with values in a common extension of
  residue fields.
- The descent statements are fpqc descent of morphisms along `Spec L → Spec K`. Mathlib
  provides it as the effective-epimorphism property of quasi-compact, faithfully flat
  morphisms of schemes.

## `exists_field_lift`

```text
theorem exists_field_lift {H G : GroupScheme (Spec (CommRingCat.of k))} (p : H ⟶ G)
    (hp : Surjective p.hom.hom.left) (g : Lie.AffinePoints G K) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Algebra k L) (_ : IsScalarTower k K L)
      (h : Lie.AffinePoints H L),
        h ≫ p.hom.hom = Lie.affineMap G (IsScalarTower.toAlgHom k K L) g
```

If the underlying scheme morphism of `p` is surjective, every `K`-point of `G` lifts to an
`L`-point of `H` for some field extension `L/K`.

*Proof.*

1. Let `x` be the image of the closed point under `g`. By surjectivity, choose `z ∈ H` with
   `p(z) = x`.
2. `g` factors through `Spec κ(x)` via a field map `α : κ(x) → K`
   (`Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField`).
3. `p` induces `β : κ(x) → κ(z)` (`residueFieldMap`).
4. The Library lemma `CentralSurjectionImage.exists_isAlgClosed_compositum` gives a field
   `L` with maps `a : κ(z) → L` and `b : K → L` such that `a ∘ β = b ∘ α`. Give `L` the
   algebra structures induced by `b`.
5. The point `Spec L → Spec κ(z) → H` lies over `Spec k`. Its composite with `p` is the
   restriction of `g`.

## `effectiveEpi_specMap` and `affineMap_injective`

`effectiveEpi_specMap K L` says that `Spec L → Spec K` is an effective epimorphism of
schemes. The Library lemma `fieldExtension_fpqc` says that this morphism is surjective, flat
and quasi-compact. Mathlib's instance in `Mathlib.AlgebraicGeometry.Sites.Fpqc` then applies.

`affineMap_injective H` says that restriction `H(K) → H(L)` is injective. Two points with
equal restrictions have equal underlying morphisms after precomposition with the
epimorphism `Spec L → Spec K`.

## `exists_affineMap_eq`

```text
theorem exists_affineMap_eq (H : GroupScheme (Spec (CommRingCat.of k)))
    (x : Lie.AffinePoints H L)
    (hx : Lie.affineMap H (includeLeft.restrictScalars k) x =
      Lie.affineMap H (includeRight.restrictScalars k) x) :
    ∃ y : Lie.AffinePoints H K, Lie.affineMap H (IsScalarTower.toAlgHom k K L) y = x
```

Here `includeLeft` and `includeRight` are the two maps `L →ₐ[K] L ⊗[K] L`. A point over `L`
whose two restrictions to `L ⊗[K] L` agree comes from a unique point over `K`. Uniqueness is
`affineMap_injective`.

*Proof.* Let `π : Spec L → Spec K`. To apply `EffectiveEpi.desc`, take any scheme `Z` and
morphisms `g₁, g₂ : Z → Spec L` with `g₁ ≫ π = g₂ ≫ π`; we must show `g₁ ≫ x = g₂ ≫ x`.

1. The pair `(g₁, g₂)` factors through the fibre product
   `Spec L ×_{Spec K} Spec L ≅ Spec (L ⊗[K] L)` (`pullbackSpecIso`). Under this
   isomorphism the projections become the spectra of the two inclusions.
2. The hypothesis `hx` therefore gives `g₁ ≫ x = g₂ ≫ x`.
3. `EffectiveEpi.desc` gives `d : Spec K → H` with `π ≫ d = x`.
4. `d` lies over `Spec k`. To see this, cancel the epimorphism `π` and use the scalar tower
   `k → K → L`.
