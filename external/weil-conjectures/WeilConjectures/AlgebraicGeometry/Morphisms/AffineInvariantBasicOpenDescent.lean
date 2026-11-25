/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import WeilConjectures.AlgebraicGeometry.Morphisms.AffineTorsorSplitAction

/-! # Invariant morphisms on an affine basic open

## References

* Stacks Project, Tag 03SF, affine stabilizer quotient calculation
* Stacks Project, Tag 03SF, affine calculation for the stabilizer quotient
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- An invariant morphism to an affine scheme factors uniquely through the fixed subring. -/
theorem affine_invariant_basic_open_descent
    (H : CommRingCat.{u}) (C : Type u) [CommRing C] [Algebra H C] [IsDomain C]
    (h : H) (hne : algebraMap H C h ≠ 0)
    (G : Type u) [Group G] (ρ : G → C →ₐ[H] C) (K : Subgroup G)
    {Z : Scheme.{u}} [IsAffine Z]
    (a : Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C h)) ⟶ Z)
    (ha : ∀ ζ : K, fixedPunctureDeck H C h G ρ ζ.val ≫ a = a) :
    let F := (⨅ ζ : K, AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C)
    let U : (Spec (CommRingCat.of F)).Opens := PrimeSpectrum.basicOpen (algebraMap H F h)
    let q := (Spec.map (CommRingCat.ofHom F.val.toRingHom)).resLE
      U (PrimeSpectrum.basicOpen (algebraMap H C h)) (by
        change PrimeSpectrum.basicOpen (algebraMap H C h) ≤
          PrimeSpectrum.basicOpen (algebraMap H C h)
        rfl)
    ∃! s : Scheme.Opens.toScheme (X := Spec (CommRingCat.of F)) U ⟶ Z, q ≫ s = a := by
  classical
  dsimp only
  let F := (⨅ ζ : K, AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C)
  let hc := algebraMap H C h
  let hf := algebraMap H F h
  let LC := Localization.Away hc
  let LF := Localization.Away hf
  let e : LF →+* LC := Localization.awayMap F.val.toRingHom hf
  have : IsLocalization.Away (F.val.toRingHom hf) LC := by
    change IsLocalization.Away hc LC
    infer_instance
  have hfhc : (hf : C) = hc := rfl
  have einj : Function.Injective e := by
    apply Localization.awayMap_injective_iff.mpr
    intro a ha
    have ha0 : a = 0 := Subtype.ext ha
    exact ⟨0, by simp [ha0]⟩
  have cinj : Function.Injective (algebraMap C LC) :=
    IsLocalization.injective LC (powers_le_nonZeroDivisors_of_noZeroDivisors hne)
  let v (ζ : K) : LC →+* LC := IsLocalization.Away.lift hc
    (g := (algebraMap C LC).comp (ρ ζ.val).toRingHom) (by
      change IsUnit (algebraMap C LC (ρ ζ.val (algebraMap H C h)))
      rw [AlgHom.commutes]
      exact IsLocalization.Away.algebraMap_isUnit hc)
  have veq (ζ : K) (c : C) : v ζ (algebraMap C LC c) =
      algebraMap C LC (ρ ζ.val c) := IsLocalization.Away.lift_eq _ _ _
  have vden (ζ : K) : v ζ (algebraMap C LC hc) = algebraMap C LC hc := by
    rw [veq]
    exact congrArg (algebraMap C LC) ((ρ ζ.val).commutes h)
  have emap (c : F) : e (algebraMap F LF c) = algebraMap C LC c.val :=
    IsLocalization.map_eq _ c
  have erange (y : LC) (hy : ∀ ζ : K, v ζ y = y) : ∃ w : LF, e w = y := by
    obtain ⟨n, c, hcy⟩ := IsLocalization.Away.surj hc y
    have hcfix : c ∈ F := by
      change c ∈ ⨅ ζ : K, AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C)
      simp only [Algebra.mem_iInf, AlgHom.mem_equalizer, AlgHom.id_apply]
      intro ζ
      apply cinj
      have he : y * algebraMap C LC hc ^ n = algebraMap C LC (ρ ζ.val c) := by
        have he := congrArg (v ζ) hcy
        rw [map_mul, map_pow, vden, hy ζ, veq] at he
        exact he
      exact he.symm.trans hcy
    let cF : F := ⟨c, hcfix⟩
    let w : LF := algebraMap F LF cF * (IsLocalization.Away.invSelf hf) ^ n
    refine ⟨w, ?_⟩
    apply (IsLocalization.Away.algebraMap_pow_isUnit hc n).mul_right_cancel
    have heinv : e (IsLocalization.Away.invSelf hf) * algebraMap C LC hc = 1 := by
      have he := congrArg e (IsLocalization.Away.mul_invSelf (S := LF) hf)
      simpa only [map_mul, map_one, emap, hfhc, mul_comm] using he
    dsimp only [w]
    rw [map_mul, map_pow, emap, mul_assoc, ← mul_pow, heinv, one_pow, mul_one]
    exact hcy.symm
  let U : (Spec (CommRingCat.of F)).Opens := PrimeSpectrum.basicOpen hf
  let V : (Spec (CommRingCat.of C)).Opens := PrimeSpectrum.basicOpen hc
  let q := (Spec.map (CommRingCat.ofHom F.val.toRingHom)).resLE U V (by
    change PrimeSpectrum.basicOpen hc ≤ PrimeSpectrum.basicOpen hc
    rfl)
  let ec := basicOpenIsoSpecAway (R := CommRingCat.of C) hc
  let ef := basicOpenIsoSpecAway (R := CommRingCat.of F) hf
  have hec : ec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap C LC)) = V.ι :=
    basicOpenIsoSpecAway_hom_SpecMap (R := CommRingCat.of C) hc
  have hef : ef.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap F LF)) = U.ι :=
    basicOpenIsoSpecAway_hom_SpecMap (R := CommRingCat.of F) hf
  have eqnat : q ≫ ef.hom = ec.hom ≫ Spec.map (CommRingCat.ofHom e) := by
    apply (cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap F LF)))).mp
    have hq : q ≫ U.ι = V.ι ≫ Spec.map (CommRingCat.ofHom F.val.toRingHom) :=
      Hom.resLE_comp_ι _ _
    rw [Category.assoc, hef, hq]
    have he : CommRingCat.ofHom (algebraMap F LF) ≫ CommRingCat.ofHom e =
        CommRingCat.ofHom F.val.toRingHom ≫ CommRingCat.ofHom (algebraMap C LC) := by
      ext c
      exact emap c
    rw [Category.assoc, ← Spec.map_comp, he, Spec.map_comp, ← Category.assoc, hec]
  have vnat (ζ : K) : fixedPunctureDeck H C h G ρ ζ.val ≫ ec.hom =
      ec.hom ≫ Spec.map (CommRingCat.ofHom (v ζ)) := by
    apply (cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap C LC)))).mp
    rw [Category.assoc, hec]
    have hd : fixedPunctureDeck H C h G ρ ζ.val ≫ V.ι =
        V.ι ≫ Spec.map (CommRingCat.ofHom (ρ ζ.val).toRingHom) :=
      Hom.resLE_comp_ι _ _
    rw [hd]
    have hv : CommRingCat.ofHom (algebraMap C LC) ≫ CommRingCat.ofHom (v ζ) =
        CommRingCat.ofHom (ρ ζ.val).toRingHom ≫
          CommRingCat.ofHom (algebraMap C LC) := by
      ext c
      exact veq ζ c
    rw [Category.assoc, ← Spec.map_comp, hv, Spec.map_comp, ← Category.assoc, hec]
  let φ : Γ(Z, ⊤) →+* LC := (Spec.preimage (ec.inv ≫ a ≫ Z.isoSpec.hom)).hom
  have hφ : Spec.map (CommRingCat.ofHom φ) = ec.inv ≫ a ≫ Z.isoSpec.hom :=
    Spec.map_preimage _
  have hφfix (ζ : K) (r : Γ(Z, ⊤)) : v ζ (φ r) = φ r := by
    have hv : Spec.map (CommRingCat.ofHom (v ζ)) ≫ ec.inv =
        ec.inv ≫ fixedPunctureDeck H C h G ρ ζ.val := by
      apply (cancel_epi ec.hom).mp
      simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
        using congrArg (fun f ↦ f ≫ ec.inv) (vnat ζ).symm
    have he : Spec.map (CommRingCat.ofHom φ ≫ CommRingCat.ofHom (v ζ)) =
        Spec.map (CommRingCat.ofHom φ) := by
      rw [Spec.map_comp, hφ, ← Category.assoc _ ec.inv, hv, Category.assoc,
        ← Category.assoc (fixedPunctureDeck H C h G ρ ζ.val), ha ζ]
    exact congrArg (fun f : Γ(Z, ⊤) ⟶ CommRingCat.of LC ↦ f r) (Spec.map_injective he)
  have hφrange : ∀ r, ∃ w : LF, e w = φ r := fun r ↦ erange (φ r) (fun ζ ↦ hφfix ζ r)
  choose ψ hψ using hφrange
  let φF : Γ(Z, ⊤) →+* LF :=
    { toFun := ψ
      map_one' := einj (by rw [hψ, map_one, map_one])
      map_mul' := fun r s ↦ einj (by simp only [map_mul, hψ])
      map_zero' := einj (by rw [hψ, map_zero, map_zero])
      map_add' := fun r s ↦ einj (by simp only [map_add, hψ]) }
  let s := ef.hom ≫ Spec.map (CommRingCat.ofHom φF) ≫ Z.isoSpec.inv
  have hs : q ≫ s = a := by
    dsimp only [s]
    rw [← Category.assoc q, eqnat, Category.assoc, ← Spec.map_comp_assoc]
    have he : CommRingCat.ofHom φF ≫ CommRingCat.ofHom e = CommRingCat.ofHom φ := by
      ext r
      exact hψ r
    rw [he, hφ]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  refine ⟨s, hs, ?_⟩
  intro s' hs'
  let φ' := Spec.preimage (ef.inv ≫ s' ≫ Z.isoSpec.hom)
  have hφ' : Spec.map φ' = ef.inv ≫ s' ≫ Z.isoSpec.hom := Spec.map_preimage _
  have he' : φ' ≫ CommRingCat.ofHom e = CommRingCat.ofHom φ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ', hφ]
    apply (cancel_epi ec.hom).mp
    rw [← Category.assoc, ← eqnat]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc q, hs']
  have hφF : φ' = CommRingCat.ofHom φF := by
    ext r
    apply einj
    exact (congrArg (fun f : Γ(Z, ⊤) ⟶ CommRingCat.of LC ↦ f r) he').trans (hψ r).symm
  apply (cancel_mono Z.isoSpec.hom).mp
  apply (cancel_epi ef.inv).mp
  dsimp only [s]
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    using hφ'.symm.trans (congrArg Spec.map hφF)

end AlgebraicGeometry.Scheme
