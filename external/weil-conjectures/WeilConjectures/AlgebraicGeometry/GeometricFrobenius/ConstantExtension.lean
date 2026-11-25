/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius.Points

/-!
# Geometric fibers over a finite constant field extension

Let `k₀ → k₁` be an extension of fields and `Y` a scheme over `k₁`, viewed as a scheme over `k₀`
through `Spec k₁ ⟶ Spec k₀`. For a `k₀`-embedding `θ : k̄₀ ↪ k̄₁` of the algebraic closures, the
geometric fibers `Ȳ₁ = Y ×_{k₁} k̄₁` and `Ȳ₀ = Y ×_{k₀} k̄₀` are related by the morphism

`ι = 𝟙 Y × Spec θ : Ȳ₁ ⟶ Ȳ₀`.

If `k₁` is finite of degree `m` over the finite field `k₀`, then `ι` intertwines the geometric
Galois Frobenius `Fr₁` of `Ȳ₁` with the `m`-th power of the geometric Galois Frobenius `Fr₀` of
`Ȳ₀`: `ι ≫ Fr₀ᵐ = Fr₁ ≫ ι`. This is the scheme-theoretic input for restricting Weil sheaves
along a finite constant field extension (blueprint:
`lemma-geometric-constituents-after-constant-extension`).

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.geometricFiberExtensionMap`: the morphism `ι : Ȳ₁ ⟶ Ȳ₀`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.geometricFiberExtensionMap_comp_geometricGaloisFrobenius_pow`:
  `ι ≫ Fr₀^{m n} = Fr₁ⁿ ≫ ι`.
- `AlgebraicGeometry.Scheme.Hom.degreeOver_eq_finrank_mul_degreeOver`: the degree of a point
  over `k₀` is `m` times its degree over `k₁`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry

variable {k₀ k₁ : Type u} [Field k₀] [Field k₁] [Algebra k₀ k₁]

/-- There is a `k₀`-embedding of the algebraic closure of `k₀` into that of an extension `k₁`. -/
theorem nonempty_algHom_algebraicClosure :
    Nonempty (AlgebraicClosure k₀ →ₐ[k₀] AlgebraicClosure k₁) :=
  ⟨IsAlgClosed.lift⟩

/-- The square of spectra

```
  Spec k̄₁ --Spec θ--> Spec k̄₀
     |                  |
     v                  v
  Spec k₁ ----------> Spec k₀
```

commutes for a `k₀`-embedding `θ : k̄₀ ↪ k̄₁`. -/
theorem spec_map_algHom_comp_specAlgebraicClosure
    (θ : AlgebraicClosure k₀ →ₐ[k₀] AlgebraicClosure k₁) :
    Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ (Scheme.specAlgebraicClosure k₀).hom =
      (Scheme.specAlgebraicClosure k₁).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁)) := by
  simp only [Scheme.specAlgebraicClosure, Over.mk_hom, ← Spec.map_comp]
  congr 1
  ext c
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  exact IsScalarTower.algebraMap_apply k₀ k₁ (AlgebraicClosure k₁) c

namespace Scheme.Hom

variable {Y : Scheme.{u}} (f₁ : Y ⟶ Spec (.of k₁)) (f₀ : Y ⟶ Spec (.of k₀))
  (hf : f₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁)) = f₀)
  (θ : AlgebraicClosure k₀ →ₐ[k₀] AlgebraicClosure k₁)

/-- The morphism `ι = 𝟙 Y × Spec θ : Y ×_{k₁} k̄₁ ⟶ Y ×_{k₀} k̄₀` between the geometric fibers of a
`k₁`-scheme `Y` over `k₁` and over `k₀`, for a `k₀`-embedding `θ : k̄₀ ↪ k̄₁`.
(blueprint: `lemma-geometric-constituents-after-constant-extension`) -/
def geometricFiberExtensionMap : f₁.geometricFiber ⟶ f₀.geometricFiber :=
  pullback.map f₁ (Scheme.specAlgebraicClosure k₁).hom f₀ (Scheme.specAlgebraicClosure k₀).hom
    (𝟙 Y) (Spec.map (CommRingCat.ofHom θ.toRingHom))
    (Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁))) (by rw [Category.id_comp, hf])
    (spec_map_algHom_comp_specAlgebraicClosure θ).symm

/-- `ι` lies over `Y`: `ι ≫ p₀ = p₁`. -/
@[reassoc (attr := simp)]
theorem geometricFiberExtensionMap_comp_geometricFiberProj :
    geometricFiberExtensionMap f₁ f₀ hf θ ≫ f₀.geometricFiberProj = f₁.geometricFiberProj :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- `ι` lies over `Spec θ`: `ι ≫ a₀ = a₁ ≫ Spec θ`. -/
@[reassoc (attr := simp)]
theorem geometricFiberExtensionMap_comp_geometricFiberToAlgebraicClosure :
    geometricFiberExtensionMap f₁ f₀ hf θ ≫ f₀.geometricFiberToAlgebraicClosure =
      f₁.geometricFiberToAlgebraicClosure ≫ Spec.map (CommRingCat.ofHom θ.toRingHom) :=
  pullback.lift_snd _ _ _

end Scheme.Hom

section Frobenius

variable [Finite k₀] [Finite k₁]

omit [Finite k₀] in
/-- The cardinality of a finite extension `k₁` of degree `m` of a finite field `k₀` is
`#k₀ ^ m`. -/
theorem natCard_eq_natCard_pow_finrank : Nat.card k₁ = Nat.card k₀ ^ Module.finrank k₀ k₁ :=
  have : Module.Finite k₀ k₁ := Module.Finite.of_finite
  Module.natCard_eq_pow_finrank

omit [Algebra k₀ k₁] [Finite k₀] [Finite k₁] in
/-- A ring homomorphism `θ : k̄₀ ⟶ k̄₁` between algebraic closures of finite fields with
`#k₁ = #k₀ ^ m` intertwines the `m n`-th power of the geometric Frobenius of `k̄₀` over `k₀` with
the `n`-th power of the geometric Frobenius of `k̄₁` over `k₁`. -/
theorem _root_.FiniteField.map_geometricFrobeniusAlgEquivOfAlgebraic_pow_mul_apply [Fintype k₀]
    [Fintype k₁] {m : ℕ} (hm : Fintype.card k₁ = Fintype.card k₀ ^ m)
    (θ : AlgebraicClosure k₀ →+* AlgebraicClosure k₁) (n : ℕ) (x : AlgebraicClosure k₀) :
    θ ((FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k₀ (AlgebraicClosure k₀) ^ (m * n)) x) =
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k₁ (AlgebraicClosure k₁) ^ n) (θ x) := by
  have h := AlgEquiv.apply_symm_apply
    (FiniteField.frobeniusAlgEquivOfAlgebraic k₀ (AlgebraicClosure k₀) ^ (m * n)) x
  rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate] at h
  dsimp only at h
  rw [FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_eq_inv,
    FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_eq_inv, inv_pow, inv_pow, AlgEquiv.aut_inv,
    AlgEquiv.aut_inv, AlgEquiv.eq_symm_apply, AlgEquiv.coe_pow,
    FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
  dsimp only
  rw [← map_pow, hm, ← pow_mul, h]

/-- The `k₀`-embedding `θ : k̄₀ ↪ k̄₁` intertwines the powers of the geometric Frobenii:

```
            σ₁ⁿ
  Spec k̄₁ -------> Spec k̄₁
     |                |
  Spec θ           Spec θ
     v                v
  Spec k̄₀ -------> Spec k̄₀
          σ₀^{m n}
```
with `m = [k₁ : k₀]`. -/
@[reassoc]
theorem specGeometricFrobenius_pow_hom_comp_spec_map_algHom
    (θ : AlgebraicClosure k₀ →ₐ[k₀] AlgebraicClosure k₁) (n : ℕ) :
    (specGeometricFrobenius k₁ ^ n).asIso.hom ≫ Spec.map (CommRingCat.ofHom θ.toRingHom) =
      Spec.map (CommRingCat.ofHom θ.toRingHom) ≫
        (specGeometricFrobenius k₀ ^ (Module.finrank k₀ k₁ * n)).asIso.hom := by
  let := Fintype.ofFinite k₀
  let := Fintype.ofFinite k₁
  have hm : Fintype.card k₁ = Fintype.card k₀ ^ Module.finrank k₀ k₁ := by
    simpa only [Nat.card_eq_fintype_card] using natCard_eq_natCard_pow_finrank (k₀ := k₀) (k₁ := k₁)
  rw [specGeometricFrobenius_pow_hom, specGeometricFrobenius_pow_hom, ← Spec.map_comp,
    ← Spec.map_comp]
  congr 1
  ext x
  exact (FiniteField.map_geometricFrobeniusAlgEquivOfAlgebraic_pow_mul_apply hm θ.toRingHom n
    x).symm

namespace Scheme.Hom

variable {Y : Scheme.{u}} (f₁ : Y ⟶ Spec (.of k₁)) (f₀ : Y ⟶ Spec (.of k₀))
  (hf : f₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁)) = f₀)
  (θ : AlgebraicClosure k₀ →ₐ[k₀] AlgebraicClosure k₁)

/-- The morphism `ι : Ȳ₁ ⟶ Ȳ₀` intertwines the powers of the geometric Galois Frobenii:
`ι ≫ Fr₀^{m n} = Fr₁ⁿ ≫ ι`, with `m = [k₁ : k₀]`.
(blueprint: `lemma-geometric-constituents-after-constant-extension`) -/
@[reassoc]
theorem geometricFiberExtensionMap_comp_geometricGaloisFrobenius_pow (n : ℕ) :
    geometricFiberExtensionMap f₁ f₀ hf θ ≫
        (f₀.geometricGaloisFrobenius ^ (Module.finrank k₀ k₁ * n)).asIso.hom =
      (f₁.geometricGaloisFrobenius ^ n).asIso.hom ≫ geometricFiberExtensionMap f₁ f₀ hf θ := by
  ext
  · simp
  · simp only [Category.assoc,
      geometricGaloisFrobenius_pow_hom_comp_geometricFiberToAlgebraicClosure,
      geometricFiberExtensionMap_comp_geometricFiberToAlgebraicClosure_assoc,
      geometricFiberExtensionMap_comp_geometricFiberToAlgebraicClosure,
      geometricGaloisFrobenius_pow_hom_comp_geometricFiberToAlgebraicClosure_assoc,
      specGeometricFrobenius_pow_hom_comp_spec_map_algHom]

/-- The morphism `ι : Ȳ₁ ⟶ Ȳ₀` intertwines the geometric Galois Frobenius of `Ȳ₁` with the
`m`-th power of that of `Ȳ₀`, `m = [k₁ : k₀]`: `ι ≫ Fr₀ᵐ = Fr₁ ≫ ι`. -/
@[reassoc]
theorem geometricFiberExtensionMap_comp_geometricGaloisFrobenius_pow_finrank :
    geometricFiberExtensionMap f₁ f₀ hf θ ≫
        (f₀.geometricGaloisFrobenius ^ Module.finrank k₀ k₁).asIso.hom =
      f₁.geometricGaloisFrobenius.asIso.hom ≫ geometricFiberExtensionMap f₁ f₀ hf θ := by
  simpa using geometricFiberExtensionMap_comp_geometricGaloisFrobenius_pow f₁ f₀ hf θ 1

end Scheme.Hom

end Frobenius

section Points

variable [Finite k₁]

/-- A `k₀`-embedding `θ : k̄₀ ↪ k̄₁` of algebraic closures is bijective, `k̄₁` being algebraic over
`k₀`. -/
theorem bijective_algHom_algebraicClosure (θ : AlgebraicClosure k₀ →ₐ[k₀] AlgebraicClosure k₁) :
    Function.Bijective θ := by
  have : Module.Finite k₀ k₁ := Module.Finite.of_finite
  have : Algebra.IsIntegral k₀ (AlgebraicClosure k₁) := Algebra.IsIntegral.trans k₁
  let := θ.toRingHom.toAlgebra
  have : IsScalarTower k₀ (AlgebraicClosure k₀) (AlgebraicClosure k₁) :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (θ.commutes c).symm
  exact IsAlgClosed.ringHom_bijective_of_isIntegral θ.toRingHom fun y ↦
    (Algebra.IsIntegral.isIntegral (R := k₀) y).tower_top

/-- The isomorphism `Spec θ : Spec k̄₁ ≅ Spec k̄₀` induced by a `k₀`-embedding `θ : k̄₀ ↪ k̄₁` of
algebraic closures, which is bijective. -/
def specAlgHomAlgebraicClosureIso (θ : AlgebraicClosure k₀ →ₐ[k₀] AlgebraicClosure k₁) :
    Spec (.of (AlgebraicClosure k₁)) ≅ Spec (.of (AlgebraicClosure k₀)) :=
  Scheme.Spec.mapIso
    (RingEquiv.ofBijective θ.toRingHom (bijective_algHom_algebraicClosure θ)).toCommRingCatIso.op

@[simp]
theorem specAlgHomAlgebraicClosureIso_hom (θ : AlgebraicClosure k₀ →ₐ[k₀] AlgebraicClosure k₁) :
    (specAlgHomAlgebraicClosureIso θ).hom = Spec.map (CommRingCat.ofHom θ.toRingHom) :=
  rfl

namespace Scheme.Hom

variable {Y : Scheme.{u}} (f₁ : Y ⟶ Spec (.of k₁)) (f₀ : Y ⟶ Spec (.of k₀))
  (hf : f₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁)) = f₀)

omit [Finite k₁] in
include hf in
/-- The embedding of `k₀` into a residue field of `Y` factors through `k₁`. -/
theorem residueFieldAlgebraMap_eq_comp_algebraMap (y : Y) :
    f₀.residueFieldAlgebraMap y = (f₁.residueFieldAlgebraMap y).comp (algebraMap k₀ k₁) := by
  subst hf
  have h := specMap_residueFieldAlgebraMap
    (f₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁))) y
  rw [← Category.assoc, ← f₁.specMap_residueFieldAlgebraMap, ← Spec.map_comp] at h
  exact congrArg CommRingCat.Hom.hom (Spec.map_inj.1 h)

include hf in
/-- The degree over `k₀` of a point with finite residue field is `[k₁ : k₀]` times its degree
over `k₁`. -/
theorem degreeOver_eq_finrank_mul_degreeOver {y : Y} (hy : y ∈ Y.finitePoints) :
    f₀.degreeOver y = Module.finrank k₀ k₁ * f₁.degreeOver y := by
  let := (f₁.residueFieldAlgebraMap y).toAlgebra
  let := (f₀.residueFieldAlgebraMap y).toAlgebra
  have : IsScalarTower k₀ k₁ (Y.residueField y) := IsScalarTower.of_algebraMap_eq fun c ↦ by
    change f₀.residueFieldAlgebraMap y c = _
    rw [residueFieldAlgebraMap_eq_comp_algebraMap f₁ f₀ hf]
    rfl
  have : Finite (Y.residueField y) := hy
  have : Module.Finite k₁ (Y.residueField y) := Module.Finite.of_finite
  have : Module.Finite k₀ k₁ := Module.Finite.of_finite
  exact (Module.finrank_mul_finrank k₀ k₁ (Y.residueField y)).symm

include hf in
/-- The residue cardinality of a point with finite residue field does not depend on the base
field `k₀` or `k₁`. -/
theorem residueCard_eq_residueCard {y : Y} (hy : y ∈ Y.finitePoints) :
    f₀.residueCard y = f₁.residueCard y := by
  have : Finite k₀ := Finite.of_injective _ (algebraMap k₀ k₁).injective
  rw [residueCard, residueCard, degreeOver_eq_finrank_mul_degreeOver f₁ f₀ hf hy, pow_mul,
    natCard_eq_natCard_pow_finrank (k₀ := k₀) (k₁ := k₁)]

variable (θ : AlgebraicClosure k₀ →ₐ[k₀] AlgebraicClosure k₁)

/-- The geometric point of `Ȳ₀ = Y ×_{k₀} k̄₀` obtained from a geometric point `s` of
`Ȳ₁ = Y ×_{k₁} k̄₁` through `Spec θ : Spec k̄₁ ≅ Spec k̄₀` and `ι : Ȳ₁ ⟶ Ȳ₀`, that is
`(Spec θ)⁻¹ ≫ s ≫ ι`. -/
def geometricFiberExtensionPoint
    (s : Spec (.of (AlgebraicClosure k₁)) ⟶ f₁.geometricFiber) :
    Spec (.of (AlgebraicClosure k₀)) ⟶ f₀.geometricFiber :=
  (specAlgHomAlgebraicClosureIso θ).inv ≫ s ≫ geometricFiberExtensionMap f₁ f₀ hf θ

/-- The transported geometric point lies over the same point of `Y`. -/
theorem geometricFiberExtensionPoint_comp_geometricFiberProj_base
    (s : Spec (.of (AlgebraicClosure k₁)) ⟶ f₁.geometricFiber) :
    (geometricFiberExtensionPoint f₁ f₀ hf θ s ≫ f₀.geometricFiberProj).base
        (IsLocalRing.closedPoint (AlgebraicClosure k₀)) =
      (s ≫ f₁.geometricFiberProj).base (IsLocalRing.closedPoint (AlgebraicClosure k₁)) := by
  rw [geometricFiberExtensionPoint, Category.assoc, Category.assoc,
    geometricFiberExtensionMap_comp_geometricFiberProj, Scheme.Hom.comp_apply]
  exact congrArg _ (Subsingleton.elim _ _)

variable [Finite k₀]

/-- If a geometric point `s` of `Ȳ₁` satisfies `s ≫ Fr₁ⁿ = σ₁ⁿ ≫ s`, then the transported
geometric point `t` of `Ȳ₀` satisfies `t ≫ Fr₀^{m n} = σ₀^{m n} ≫ t`, `m = [k₁ : k₀]`. -/
theorem geometricFiberExtensionPoint_comp_geometricGaloisFrobenius_pow
    {s : Spec (.of (AlgebraicClosure k₁)) ⟶ f₁.geometricFiber} {n : ℕ}
    (hs : s ≫ (f₁.geometricGaloisFrobenius ^ n).asIso.hom =
      (specGeometricFrobenius k₁ ^ n).asIso.hom ≫ s) :
    geometricFiberExtensionPoint f₁ f₀ hf θ s ≫
        (f₀.geometricGaloisFrobenius ^ (Module.finrank k₀ k₁ * n)).asIso.hom =
      (specGeometricFrobenius k₀ ^ (Module.finrank k₀ k₁ * n)).asIso.hom ≫
        geometricFiberExtensionPoint f₁ f₀ hf θ s := by
  have h := specGeometricFrobenius_pow_hom_comp_spec_map_algHom θ n
  rw [← specAlgHomAlgebraicClosureIso_hom θ, ← Iso.inv_comp_eq, ← Category.assoc,
    ← Iso.eq_comp_inv] at h
  rw [geometricFiberExtensionPoint, Category.assoc, Category.assoc,
    geometricFiberExtensionMap_comp_geometricGaloisFrobenius_pow, reassoc_of% hs,
    reassoc_of% h]

/-- The geometric point of `Ȳ₀` transported from the geometric point of `Ȳ₁` over a point `y`
with finite residue field is fixed by `Fr₀^{deg₀ y}` up to `σ₀^{deg₀ y}`, where
`deg₀ y = [k₁ : k₀] deg₁ y` is the degree over `k₀`. -/
theorem geometricFiberExtensionPoint_geometricFiberPointOfFinitePoint_comp (y : Y.finitePoints) :
    geometricFiberExtensionPoint f₁ f₀ hf θ (f₁.geometricFiberPointOfFinitePoint y) ≫
        (f₀.geometricGaloisFrobenius ^ (Module.finrank k₀ k₁ * f₁.degreeOver y.1)).asIso.hom =
      (specGeometricFrobenius k₀ ^ (Module.finrank k₀ k₁ * f₁.degreeOver y.1)).asIso.hom ≫
        geometricFiberExtensionPoint f₁ f₀ hf θ (f₁.geometricFiberPointOfFinitePoint y) :=
  geometricFiberExtensionPoint_comp_geometricGaloisFrobenius_pow f₁ f₀ hf θ
    (f₁.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow y)

omit [Finite k₀] in
/-- The geometric point of `Ȳ₀` transported from the geometric point of `Ȳ₁` over a point `y`
with finite residue field lies over `y`. -/
theorem geometricFiberExtensionPoint_geometricFiberPointOfFinitePoint_base (y : Y.finitePoints) :
    (geometricFiberExtensionPoint f₁ f₀ hf θ (f₁.geometricFiberPointOfFinitePoint y) ≫
      f₀.geometricFiberProj).base (IsLocalRing.closedPoint (AlgebraicClosure k₀)) = y.1 :=
  (geometricFiberExtensionPoint_comp_geometricFiberProj_base f₁ f₀ hf θ _).trans
    (f₁.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base y)

end Scheme.Hom

end Points

end AlgebraicGeometry
