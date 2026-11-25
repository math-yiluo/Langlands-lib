/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism.Point
public import WeilConjectures.EtaleCohomology.Purity.Smooth.WeilDatum
public import WeilConjectures.SixFunctors.Etale.Derived.PointUnit
public import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius

/-!
# The Frobenius scalars of the Tate datum

Let `k` be a separably closed field, `Y = Spec k`, `h` an endomorphism of `Y` and `Λ` a
coefficient ring with a Tate twist datum (`AlgebraicGeometry.Etale.HasTateTwist`). Over `Y`
the twists are trivial, `Λ_Y(r) ≅ Λ_Y`, and the endomorphisms of `Λ_Y` are the scalars `Λ`, so
`H⁰(Y, Λ(r)) = Hom(Λ_Y, Λ_Y(r))` is free of rank one over `Λ`. The Frobenius operator of the
Tate datum `τ_r : Lh^* Λ_Y(r) ≅ Λ_Y(r)` (`AlgebraicGeometry.Etale.tateWeilDatum`) is therefore
the multiplication by a scalar `c_r ∈ Λ`
(`AlgebraicGeometry.Etale.tateFrobeniusScalar`). Since the products
`Λ_Y(m) ⊗ Λ_Y(m') ≅ Λ_Y(m + m')` are Weil pairings for the Tate data, these scalars are
multiplicative, `c_{m + m'} = c_m c_{m'}`; each of them is a unit, so `c_r = c_1 ^ r`.

This is the formal half of the normalization `prose-10-21`: geometric
Frobenius acts on `Λ(r)` by `q^{-r}`, which comes down to `c_1 = q⁻¹`; that value is computed for
the genuine Tate twist in `WeilConjectures.EtaleCohomology.TateTwist.FrobeniusNormalization`.

## Main definitions

- `AlgebraicGeometry.Etale.tateFrobeniusScalar`: the scalar `c_r`.

## Main statements

- `AlgebraicGeometry.Etale.frobeniusOperator_tateWeilDatum_eq_smul`: `F x = c_r • x`.
- `AlgebraicGeometry.Etale.tateFrobeniusScalar_add`: `c_{m + m'} = c_m c_{m'}`.
- `AlgebraicGeometry.Etale.frobeniusOperator_tateWeilDatum_eq_zpow_smul`: `F x = c_1 ^ r • x`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace Etale

open Scheme

section Unit

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}} [ConnectedSpace X]

/-- On a connected scheme, every `Λ`-linear endomorphism of `Hom(Λ_X, M)` for an object
`M ≅ Λ_X` is the multiplication by a scalar: `Hom(Λ_X, M) ≅ End(Λ_X) = Λ` is free of rank one. -/
theorem exists_linearMap_eq_smul_of_iso_unit {M : DerivedCategoryModule Λ X}
    (e : M ≅ 𝟙_ (DerivedCategoryModule Λ X))
    (L : (𝟙_ (DerivedCategoryModule Λ X) ⟶ M) →ₗ[Λ] (𝟙_ (DerivedCategoryModule Λ X) ⟶ M)) :
    ∃ c : Λ, ∀ x, L x = c • x := by
  have hb := (bijective_smul_id_unit Λ X).2
  have hx (x : 𝟙_ (DerivedCategoryModule Λ X) ⟶ M) : ∃ a : Λ, x = a • e.inv := by
    obtain ⟨a, ha⟩ := hb (x ≫ e.hom)
    refine ⟨a, ?_⟩
    rw [← Category.comp_id x, ← e.hom_inv_id, ← Category.assoc, ← ha, Linear.smul_comp,
      Category.id_comp]
  obtain ⟨c, hc⟩ := hx (L e.inv)
  refine ⟨c, fun x ↦ ?_⟩
  obtain ⟨a, rfl⟩ := hx x
  rw [map_smul, hc, smul_smul, smul_smul, mul_comm]

/-- On a connected scheme, a scalar `a` with `a • 𝟙 = 0` on an object `M ≅ Λ_X` vanishes. -/
theorem eq_zero_of_smul_id_eq_zero_of_iso_unit {M : DerivedCategoryModule Λ X}
    (e : M ≅ 𝟙_ (DerivedCategoryModule Λ X)) {a : Λ} (ha : a • 𝟙 M = 0) : a = 0 := by
  refine (bijective_smul_id_unit Λ X).1 ?_
  simp only
  rw [zero_smul, ← e.inv_hom_id, ← Linear.comp_smul, ← Category.id_comp e.hom,
    ← Linear.smul_comp, ha, zero_comp, comp_zero]

/-- On a connected scheme, an isomorphism `x : Λ_X ⟶ M` is not torsion: `a • x = 0` forces
`a = 0`. -/
theorem eq_zero_of_smul_eq_zero_of_isIso {M : DerivedCategoryModule Λ X}
    (x : 𝟙_ (DerivedCategoryModule Λ X) ⟶ M) [IsIso x] {a : Λ} (ha : a • x = 0) : a = 0 :=
  eq_zero_of_smul_id_eq_zero_of_iso_unit (asIso x).symm (by
    rw [← cancel_epi x, Linear.comp_smul, Category.comp_id, ha, comp_zero])

/-- On a connected scheme, a scalar `a` such that `a • 𝟙` is an isomorphism of `Λ_X` is a
unit. -/
theorem isUnit_of_isIso_smul_id {a : Λ} (ha : IsIso (a • 𝟙 (𝟙_ (DerivedCategoryModule Λ X)))) :
    IsUnit a := by
  obtain ⟨b, hb⟩ := (bijective_smul_id_unit Λ X).2 (inv (a • 𝟙 (𝟙_ (DerivedCategoryModule Λ X))))
  refine isUnit_iff_exists_inv.2 ⟨b, (bijective_smul_id_unit Λ X).1 ?_⟩
  simp only at hb ⊢
  rw [one_smul, ← smul_smul, ← Category.id_comp (b • 𝟙 _), ← Linear.smul_comp, hb,
    IsIso.hom_inv_id]

/-- The degreewise pairing of an isomorphism `Q : A ⊗ᴸ B ≅ C` on two isomorphisms
`x : Λ_X ≅ A[i]`, `y : Λ_X ≅ B[j]` is an isomorphism `Λ_X ≅ C[i + j]`. -/
instance isIso_degreewisePairing {A B C : DerivedCategoryModule Λ X}
    (Q : ((derivedTensor _ X).obj A).obj B ⟶ C) [IsIso Q] (i j : ℤ)
    (x : 𝟙_ (DerivedCategoryModule Λ X) ⟶ A⟦i⟧) (y : 𝟙_ (DerivedCategoryModule Λ X) ⟶ B⟦j⟧)
    [IsIso x] [IsIso y] : IsIso (degreewisePairing Q i j x y) := by
  rw [degreewisePairing_apply]
  infer_instance

end Unit

variable (Λ : Type (u + 1)) [CommRing Λ] [HasTateTwist Λ] {k : Type u} [Field k] [IsSepClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))] (h : Spec (.of k) ⟶ Spec (.of k))

/-- The product `Λ_X(m) ⊗ Λ_X(m') ≅ Λ_X(m + m')` of the Tate twisting objects
(`AlgebraicGeometry.Etale.HasTateTwist.twistObjectAddIso`). -/
noncomputable def tateObjectAddIso (X : Scheme.{u}) [HasInvertibleExponent Λ X] (m m' : ℤ) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (tateObject Λ X m)).obj (tateObject Λ X m') ≅
      tateObject Λ X (m + m') :=
  HasTateTwist.twistObjectAddIso X m m'

/-- The products `Λ_X(m) ⊗ Λ_X(m') ≅ Λ_X(m + m')` of a Tate twist datum are Weil pairings for the
Tate data `τ_m`, `τ_{m'}` and `τ_{m + m'}`: this is the compatibility of the pullback
identifications with the products
(`AlgebraicGeometry.Etale.HasTateTwist.leftDerivedUpperStar_map_twistObjectAddIso`). -/
theorem isWeilPairing_tateObjectAddIso {X : Scheme.{u}} [HasInvertibleExponent Λ X]
    (g : X ⟶ X) (m m' : ℤ) :
    IsWeilPairing g (tateWeilDatum Λ g m).hom (tateWeilDatum Λ g m').hom
      (tateWeilDatum Λ g (m + m')).hom (tateObjectAddIso Λ X m m').hom := by
  have := HasTateTwist.leftDerivedUpperStar_map_twistObjectAddIso (Λ := Λ) g m m'
  rw [IsWeilPairing, IsWeilMorphism, tensorWeilDatum, Category.assoc, Category.assoc]
  exact this

/-- Over a separably closed field the Frobenius operator of the Tate datum `τ_r` is the
multiplication by a scalar. -/
theorem exists_frobeniusOperator_tateWeilDatum_eq_smul (r : ℤ) :
    ∃ c : Λ, ∀ x : 𝟙_ (DerivedCategoryModule Λ (Spec (.of k))) ⟶ tateObject Λ _ r,
      frobeniusOperator h (tateWeilDatum Λ h r).hom x = c • x :=
  exists_linearMap_eq_smul_of_iso_unit (nonempty_tateObject_iso_unit Λ k r).some _

/-- The *Frobenius scalar* `c_r ∈ Λ` of the Tate datum over a separably closed field: the
Frobenius operator of `τ_r : Lh^* Λ(r) ≅ Λ(r)` on `H⁰(Spec k, Λ(r)) = Hom(Λ, Λ(r))`, a free
`Λ`-module of rank one, is the multiplication by `c_r`
(`AlgebraicGeometry.Etale.frobeniusOperator_tateWeilDatum_eq_smul`). For the geometric Frobenius
of `k̄` over `𝔽_q` it is `q^{-r}` (`prose-10-21`). -/
noncomputable def tateFrobeniusScalar (r : ℤ) : Λ :=
  (exists_frobeniusOperator_tateWeilDatum_eq_smul Λ h r).choose

/-- The Frobenius operator of the Tate datum `τ_r` is the multiplication by the Frobenius scalar
`c_r`. -/
theorem frobeniusOperator_tateWeilDatum_eq_smul (r : ℤ)
    (x : 𝟙_ (DerivedCategoryModule Λ (Spec (.of k))) ⟶ tateObject Λ _ r) :
    frobeniusOperator h (tateWeilDatum Λ h r).hom x = tateFrobeniusScalar Λ h r • x :=
  (exists_frobeniusOperator_tateWeilDatum_eq_smul Λ h r).choose_spec x

/-- The Frobenius scalar `c_r` is determined by any non-torsion class `x ∈ H⁰(Spec k, Λ(r))`
whose image under the Frobenius operator is `a • x`. -/
theorem tateFrobeniusScalar_eq_of_frobeniusOperator_eq_smul {r : ℤ}
    (x : 𝟙_ (DerivedCategoryModule Λ (Spec (.of k))) ⟶ tateObject Λ _ r)
    (hx : ∀ b : Λ, b • x = 0 → b = 0) {a : Λ}
    (ha : frobeniusOperator h (tateWeilDatum Λ h r).hom x = a • x) :
    tateFrobeniusScalar Λ h r = a := by
  rw [frobeniusOperator_tateWeilDatum_eq_smul] at ha
  exact sub_eq_zero.1 (hx _ (by rw [sub_smul, ha, sub_self]))

/-- The Frobenius scalars are units: the Frobenius operator sends a generator
`Λ ≅ Λ(r)` of `H⁰(Spec k, Λ(r))` to the isomorphism `ε⁻¹ ≫ Lh^* x ≫ τ_r`. -/
theorem isUnit_tateFrobeniusScalar (r : ℤ) : IsUnit (tateFrobeniusScalar Λ h r) := by
  obtain ⟨e⟩ := nonempty_tateObject_iso_unit Λ k r
  have hF := frobeniusOperator_tateWeilDatum_eq_smul Λ h r e.inv
  rw [frobeniusOperator_apply] at hF
  apply isUnit_of_isIso_smul_id (X := Spec (.of k))
  have : tateFrobeniusScalar Λ h r • 𝟙 (𝟙_ (DerivedCategoryModule Λ (Spec (.of k)))) =
      ((leftDerivedUpperStarUnitIso _ h).inv ≫ (L((h)^*[ModuleCat.{u + 1} Λ])).map e.inv ≫
        (tateWeilDatum Λ h r).hom) ≫ e.hom := by
    rw [hF, Linear.smul_comp, e.inv_hom_id]
  rw [this]
  infer_instance

/-- **The Frobenius scalars are multiplicative**, `c_{m + m'} = c_m c_{m'}`: the products
`Λ(m) ⊗ Λ(m') ≅ Λ(m + m')` are Weil pairings
(`AlgebraicGeometry.Etale.isWeilPairing_tateObjectAddIso`), so their degreewise pairings
intertwine the Frobenius operators, and the pairing of two generators is a generator. -/
theorem tateFrobeniusScalar_add (m m' : ℤ) :
    tateFrobeniusScalar Λ h (m + m') = tateFrobeniusScalar Λ h m * tateFrobeniusScalar Λ h m' := by
  obtain ⟨e⟩ := nonempty_tateObject_iso_unit Λ k m
  obtain ⟨e'⟩ := nonempty_tateObject_iso_unit Λ k m'
  have hx₀ : IsIso (e.inv ≫ (shiftFunctorZero' (DerivedCategoryModule Λ (Spec (.of k))) (0 : ℤ)
      rfl).inv.app (tateObject Λ _ m)) := inferInstance
  have hy₀ : IsIso (e'.inv ≫ (shiftFunctorZero' (DerivedCategoryModule Λ (Spec (.of k))) (0 : ℤ)
      rfl).inv.app (tateObject Λ _ m')) := inferInstance
  set x := e.inv ≫ (shiftFunctorZero' (DerivedCategoryModule Λ (Spec (.of k))) (0 : ℤ)
      rfl).inv.app (tateObject Λ _ m) with hxdef
  set y := e'.inv ≫ (shiftFunctorZero' (DerivedCategoryModule Λ (Spec (.of k))) (0 : ℤ)
      rfl).inv.app (tateObject Λ _ m') with hydef
  have hx : frobeniusOperator h (shiftWeilDatum h (tateWeilDatum Λ h m).hom 0) x =
      tateFrobeniusScalar Λ h m • x := by
    rw [← cancel_mono ((shiftFunctorZero' _ (0 : ℤ) rfl).hom.app _),
      frobeniusOperator_shiftWeilDatum_comp_shiftFunctorZero', Linear.smul_comp,
      frobeniusOperator_tateWeilDatum_eq_smul]
  have hy : frobeniusOperator h (shiftWeilDatum h (tateWeilDatum Λ h m').hom 0) y =
      tateFrobeniusScalar Λ h m' • y := by
    rw [← cancel_mono ((shiftFunctorZero' _ (0 : ℤ) rfl).hom.app _),
      frobeniusOperator_shiftWeilDatum_comp_shiftFunctorZero', Linear.smul_comp,
      frobeniusOperator_tateWeilDatum_eq_smul]
  have hP := (isWeilPairing_tateObjectAddIso Λ h m m').degreewisePairing_frobeniusOperator 0 0
    x y
  rw [hx, hy, LinearMap.map_smul₂, map_smul, smul_smul] at hP
  have hz := isIso_degreewisePairing (tateObjectAddIso Λ (Spec (.of k)) m m').hom 0 0
    x y
  refine (sub_eq_zero.1 (eq_zero_of_smul_eq_zero_of_isIso
    (degreewisePairing (tateObjectAddIso Λ (Spec (.of k)) m m').hom 0 0 x y ≫
      (shiftFunctorZero' _ (0 + 0 : ℤ) (add_zero 0)).hom.app _) ?_)).symm
  have := hP =≫ (shiftFunctorZero' _ (0 + 0 : ℤ) (add_zero 0)).hom.app _
  rw [frobeniusOperator_shiftWeilDatum_comp_shiftFunctorZero', Linear.smul_comp] at this
  rw [sub_smul, this]
  rw [frobeniusOperator_tateWeilDatum_eq_smul]
  rw [sub_self]

/-- The Frobenius scalar of the zero twist is `1`. -/
theorem tateFrobeniusScalar_zero : tateFrobeniusScalar Λ h 0 = 1 := by
  have h0 := tateFrobeniusScalar_add Λ h 0 0
  rw [add_zero] at h0
  exact (isUnit_tateFrobeniusScalar Λ h 0).mul_left_cancel (by rw [mul_one, ← h0])

/-- The Frobenius scalar `c_1` as a unit of `Λ`. -/
noncomputable def tateFrobeniusUnit : Λˣ :=
  (isUnit_tateFrobeniusScalar Λ h 1).unit

/-- The unit `c_1` is the Frobenius scalar of `Λ(1)`. -/
theorem val_tateFrobeniusUnit : (tateFrobeniusUnit Λ h : Λ) = tateFrobeniusScalar Λ h 1 :=
  IsUnit.unit_spec _

/-- The Frobenius scalars are the powers of `c_1`: `c_r = c_1 ^ r`. -/
theorem tateFrobeniusScalar_eq_zpow (r : ℤ) :
    tateFrobeniusScalar Λ h r = ((tateFrobeniusUnit Λ h ^ r : Λˣ) : Λ) := by
  induction r using Int.induction_on with
  | zero => rw [zpow_zero, Units.val_one, tateFrobeniusScalar_zero]
  | succ n ih =>
    rw [tateFrobeniusScalar_add, ih, zpow_add_one, Units.val_mul, val_tateFrobeniusUnit]
  | pred n ih =>
    have h₁ := tateFrobeniusScalar_add Λ h (-(n : ℤ) - 1) 1
    rw [sub_add_cancel, ih, ← val_tateFrobeniusUnit] at h₁
    rw [zpow_sub_one, Units.val_mul, h₁, mul_assoc, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, mul_one]

/-- Blueprint `definition-weil-structure--1` (the formal part of the twist normalization of
`prose-10-21`): over a separably closed field, the Frobenius operator
of the Tate datum `τ_r` on `H⁰(Spec k, Λ(r))` is the multiplication by `c_1 ^ r`, for the unit
`c_1` by which it acts on `Λ(1)`. -/
theorem frobeniusOperator_tateWeilDatum_eq_zpow_smul (r : ℤ)
    (x : 𝟙_ (DerivedCategoryModule Λ (Spec (.of k))) ⟶ tateObject Λ _ r) :
    frobeniusOperator h (tateWeilDatum Λ h r).hom x =
      ((tateFrobeniusUnit Λ h ^ r : Λˣ) : Λ) • x := by
  rw [frobeniusOperator_tateWeilDatum_eq_smul, tateFrobeniusScalar_eq_zpow]

end Etale

end AlgebraicGeometry
