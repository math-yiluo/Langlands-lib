/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proj.ProjScalarExtensionTwistData
import WeilConjectures.AlgebraicGeometry.Proj.ProjScalarExtensionTwistSectionRestriction
import WeilConjectures.AlgebraicGeometry.Proj.ProjScalarExtensionTwistLocalizationProduct

/-! Multiplication part of the normalized scalar-extension twist laws. -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

/- The chartwise fraction calculation proves this product clause. -/
theorem scalarExtension_twist_multiplication
    {A B : Type u} [CommRing A] [CommRing B]
    {σ τ : Type u} [SetLike σ A] [AddSubgroupClass σ A]
    [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (ψ : 𝒜 →+*ᵍ ℬ) (r : Proj ℬ ⟶ Proj 𝒜)
    (θ : ∀ j : ℤ, (tensorPullback r).obj (twist 𝒜 j) ≅ twist ℬ j)
    (hθ : IsScalarExtensionTwistComparison ψ r θ) :
    ∀ (i j : ℤ) (U : (Proj 𝒜).Opens)
      (s : Γ(twist 𝒜 i, U)) (t : Γ(twist 𝒜 j, U))
      (v : Γ(twist 𝒜 (i + j), U)),
      (∀ x : U, (v.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
        (s.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) * t.1 x) →
      ∀ x : r ⁻¹ᵁ U,
        ((scalarExtensionTwistSection r θ (i + j) U v).1 x :
          Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
        ((scalarExtensionTwistSection r θ i U s).1 x :
          Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) *
        (scalarExtensionTwistSection r θ j U t).1 x := by
  intro i j U s t v hv x
  have hs := s.2 ⟨_, x.2⟩
  obtain ⟨V, hyV, e, ai, ak, hik, a, b, hb, hsval⟩ := hs
  let sV : Γ(twist 𝒜 i, V) := (twist 𝒜 i).presheaf.map e.op s
  let xV : r ⁻¹ᵁ V := ⟨x.1, hyV⟩
  have hVb : V ≤ basicOpen 𝒜 (b : A) := by
    intro y hy
    exact hb ⟨y, hy⟩
  have hsfrac : ∀ y : V, (sV.1 y : Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) *
      Localization.mk (b : A) 1 = Localization.mk (a : A) 1 := by
    intro y
    change (s.1 (e y) : Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) *
      Localization.mk (b : A) 1 = Localization.mk (a : A) 1
    have hsy := hsval y
    change (s.1 (e y) : _) = _ at hsy
    rw [hsy, HomogeneousLocalization.degreePart.coe_mk]
    rw [Localization.mk_mul]
    simpa using localization_mk_mul_denominator
      (P := y.1.asHomogeneousIdeal.toIdeal) (a := (a : A)) (b := (b : A)) (hb := hb y)
  have hsf := hθ i ai ak a b a.2 b.2 hik V hVb sV hsfrac
    (1 : Γ(Proj ℬ, r ⁻¹ᵁ V)) xV
  have hsres := scalarExtensionTwistSection_restrict r θ i U V e.le s xV
  have hsres' : (scalarExtensionTwistSection r θ i V sV).1 xV =
      (scalarExtensionTwistSection r θ i U s).1 x := by
    have he : homOfLE e.le = e := Subsingleton.elim _ _
    simpa [sV, xV, he] using hsres
  obtain ⟨W, hyW, ew, aj, al, hjl, c, d, hd, htval⟩ :=
    t.2 ⟨r.base x.1, x.2⟩
  let W' := V ⊓ W
  have hW' : W' ≤ U := (Opens.infLELeft V W).le.trans e.le
  let ewS : W' ⟶ U := Opens.infLELeft V W ≫ e
  let ewT : W' ⟶ U := Opens.infLERight V W ≫ ew
  let sW : Γ(twist 𝒜 i, W') := (twist 𝒜 i).presheaf.map ewS.op s
  let tW : Γ(twist 𝒜 j, W') := (twist 𝒜 j).presheaf.map ewS.op t
  have heST : ewS = ewT := Subsingleton.elim _ _
  have hWb : W' ≤ basicOpen 𝒜 (b : A) := by
    intro y hy
    exact hb ⟨y, hy.1⟩
  have hWd : W' ≤ basicOpen 𝒜 (d : A) := by
    intro y hy
    exact hd ⟨y, hy.2⟩
  have hsWfrac : ∀ y : W',
      (sW.1 y : Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) *
          Localization.mk (b : A) 1 = Localization.mk (a : A) 1 := by
    intro y
    have hsy := hsval ((Opens.infLELeft V W) y)
    change (s.1 (ewS y) : _) = _ at hsy
    change (s.1 (ewS y) : Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) *
        Localization.mk (b : A) 1 = _
    rw [hsy, HomogeneousLocalization.degreePart.coe_mk]
    rw [Localization.mk_mul]
    simpa using localization_mk_mul_denominator
      (P := y.1.asHomogeneousIdeal.toIdeal) (a := (a : A)) (b := (b : A))
      (hb := hb ⟨y, (Opens.infLELeft V W).le y.2⟩)
  have htWfrac : ∀ y : W',
      (tW.1 y : Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) *
          Localization.mk (d : A) 1 = Localization.mk (c : A) 1 := by
    intro y
    have hty := htval ((Opens.infLERight V W) y)
    change (t.1 (ewT y) : _) = _ at hty
    change (t.1 (ewT y) : Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) *
        Localization.mk (d : A) 1 = _
    rw [hty, HomogeneousLocalization.degreePart.coe_mk]
    rw [Localization.mk_mul]
    simpa using localization_mk_mul_denominator
      (P := y.1.asHomogeneousIdeal.toIdeal) (a := (c : A)) (b := (d : A))
      (hb := hd ⟨y, (Opens.infLERight V W).le y.2⟩)
  let xW : r ⁻¹ᵁ W' := ⟨x.1, show r.base x.1 ∈ W' from ⟨hyV, hyW⟩⟩
  have hsfW := hθ i ai ak a b a.2 b.2 hik W' hWb sW hsWfrac
    (1 : Γ(Proj ℬ, r ⁻¹ᵁ W')) xW
  have htfW := hθ j aj al c d c.2 d.2 hjl W' hWd tW htWfrac
    (1 : Γ(Proj ℬ, r ⁻¹ᵁ W')) xW
  let vW : Γ(twist 𝒜 (i + j), W') :=
    (twist 𝒜 (i + j)).presheaf.map ewS.op v
  have hWbd : W' ≤ basicOpen 𝒜 (b * d : A) := by
    rw [Proj.basicOpen_mul]
    exact le_inf hWb hWd
  have hvWfrac : ∀ y : W',
      (vW.1 y : Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) *
          Localization.mk (b * d : A) 1 = Localization.mk (a * c : A) 1 := by
    intro y
    have hvy := hv (ewS y)
    change (v.1 (ewS y) : Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) *
        Localization.mk (b * d : A) 1 = _
    rw [hvy]
    have hsy := hsWfrac y
    have hty := htWfrac y
    change (sW.1 y : Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) *
        (tW.1 y : Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) *
        Localization.mk (b * d : A) 1 = _
    have hmk : (Localization.mk (b * d : A) 1 :
        Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) =
        (Localization.mk (b : A) 1 :
          Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) *
          Localization.mk (d : A) 1 := by
      simpa using (Localization.mk_mul (M := A)
        (S := y.1.asHomogeneousIdeal.toIdeal.primeCompl) (b : A) (d : A) 1 1).symm
    calc
      _ = ((sW.1 y : Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) *
          Localization.mk (b : A) 1) *
          ((tW.1 y : Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) *
            Localization.mk (d : A) 1) := by
        rw [hmk]
        ring
      _ = Localization.mk (a : A) 1 * Localization.mk (c : A) 1 := by
        rw [hsWfrac y, htWfrac y]
      _ = Localization.mk (a * c : A) 1 := by
        have hmkAC : (Localization.mk (a * c : A) 1 :
            Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) =
            (Localization.mk (a : A) 1 :
              Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) *
              Localization.mk (c : A) 1 := by
          simpa using (Localization.mk_mul (M := A)
            (S := y.1.asHomogeneousIdeal.toIdeal.primeCompl) (a : A) (c : A) 1 1).symm
        exact hmkAC.symm
  have hvfW := hθ (i + j) (ai + aj) (ak + al) (a * c) (b * d)
    (SetLike.mul_mem_graded a.2 c.2) (SetLike.mul_mem_graded b.2 d.2) (by omega)
    W' hWbd vW hvWfrac (1 : Γ(Proj ℬ, r ⁻¹ᵁ W')) xW
  have hunit_b : IsUnit (Localization.mk (ψ b) 1 :
      Localization.AtPrime xW.1.asHomogeneousIdeal.toIdeal) := by
    let tb : Γ(twist 𝒜 (-(ak : ℤ)), W') :=
      ⟨fun y ↦ HomogeneousLocalization.degreePart.mk
          (⟨1, SetLike.one_mem_graded 𝒜⟩ : 𝒜 0) ⟨(b : A), b.2⟩ (hWb y.2) (by omega),
        ProjectiveSpectrum.Twist.isLocallyFraction_mk (by omega)
          (⟨1, SetLike.one_mem_graded 𝒜⟩ : 𝒜 0) ⟨(b : A), b.2⟩
          (fun y ↦ hWb y.2)⟩
    have htb (y : W') :
        (tb.1 y : Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) *
          Localization.mk (b : A) 1 = Localization.mk (1 : A) 1 := by
      have hby : (b : A) ∉ y.1.asHomogeneousIdeal.toIdeal := hWb y.2
      change Localization.mk (1 : A) ⟨(b : A), hby⟩ *
          Localization.mk (b : A) 1 = _
      simp only [Localization.mk_mul, one_mul, mul_one, Localization.mk_one]
      exact Localization.mk_self ⟨(b : A), hby⟩
    have H := hθ (-(ak : ℤ)) 0 ak 1 b (SetLike.one_mem_graded 𝒜) b.2
      (by omega) W' hWb tb htb 1 xW
    apply isUnit_iff_exists_inv'.mpr
    refine ⟨(scalarExtensionTwistSection r θ (-(ak : ℤ)) W' tb).1 xW, ?_⟩
    have hOne : ((1 : Γ(Proj ℬ, r ⁻¹ᵁ W')).1 xW).val = 1 :=
      HomogeneousLocalization.val_one
    simpa only [one_smul, hOne, map_one, Localization.mk_one, mul_one] using H
  have hunit_d : IsUnit (Localization.mk (ψ d) 1 :
      Localization.AtPrime xW.1.asHomogeneousIdeal.toIdeal) := by
    let td : Γ(twist 𝒜 (-(al : ℤ)), W') :=
      ⟨fun y ↦ HomogeneousLocalization.degreePart.mk
          (⟨1, SetLike.one_mem_graded 𝒜⟩ : 𝒜 0) ⟨(d : A), d.2⟩ (hWd y.2) (by omega),
        ProjectiveSpectrum.Twist.isLocallyFraction_mk (by omega)
          (⟨1, SetLike.one_mem_graded 𝒜⟩ : 𝒜 0) ⟨(d : A), d.2⟩
          (fun y ↦ hWd y.2)⟩
    have htd (y : W') :
        (td.1 y : Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) *
          Localization.mk (d : A) 1 = Localization.mk (1 : A) 1 := by
      have hdy : (d : A) ∉ y.1.asHomogeneousIdeal.toIdeal := hWd y.2
      change Localization.mk (1 : A) ⟨(d : A), hdy⟩ *
          Localization.mk (d : A) 1 = _
      simp only [Localization.mk_mul, one_mul, mul_one, Localization.mk_one]
      exact Localization.mk_self ⟨(d : A), hdy⟩
    have H := hθ (-(al : ℤ)) 0 al 1 d (SetLike.one_mem_graded 𝒜) d.2
      (by omega) W' hWd td htd 1 xW
    apply isUnit_iff_exists_inv'.mpr
    refine ⟨(scalarExtensionTwistSection r θ (-(al : ℤ)) W' td).1 xW, ?_⟩
    have hOne : ((1 : Γ(Proj ℬ, r ⁻¹ᵁ W')).1 xW).val = 1 :=
      HomogeneousLocalization.val_one
    simpa only [one_smul, hOne, map_one, Localization.mk_one, mul_one] using H
  have hsEq :
      ((scalarExtensionTwistSection r θ i W' sW).1 xW :
        Localization.AtPrime xW.1.asHomogeneousIdeal.toIdeal) *
          Localization.mk (ψ (b : A)) 1 = Localization.mk (ψ (a : A)) 1 := by
    have hOne : ((1 : Γ(Proj ℬ, r ⁻¹ᵁ W')).1 xW).val = 1 :=
      HomogeneousLocalization.val_one
    rw [hOne] at hsfW
    simpa [one_smul, map_one, Localization.mk_one] using hsfW
  have htEq :
      ((scalarExtensionTwistSection r θ j W' tW).1 xW :
        Localization.AtPrime xW.1.asHomogeneousIdeal.toIdeal) *
          Localization.mk (ψ (d : A)) 1 = Localization.mk (ψ (c : A)) 1 := by
    have hOne : ((1 : Γ(Proj ℬ, r ⁻¹ᵁ W')).1 xW).val = 1 :=
      HomogeneousLocalization.val_one
    rw [hOne] at htfW
    simpa [one_smul, map_one, Localization.mk_one] using htfW
  have hvEq :
      ((scalarExtensionTwistSection r θ (i + j) W' vW).1 xW :
        Localization.AtPrime xW.1.asHomogeneousIdeal.toIdeal) *
          (Localization.mk (ψ (b : A)) 1 * Localization.mk (ψ (d : A)) 1) =
        Localization.mk (ψ (a : A)) 1 * Localization.mk (ψ (c : A)) 1 := by
    have hOne : ((1 : Γ(Proj ℬ, r ⁻¹ᵁ W')).1 xW).val = 1 :=
      HomogeneousLocalization.val_one
    rw [hOne] at hvfW
    simpa [one_smul, map_one, Localization.mk_one, map_mul,
      Localization.mk_mul] using hvfW
  obtain ⟨vb, hvb⟩ := isUnit_iff_exists_inv.mp hunit_b
  obtain ⟨vd, hvd⟩ := isUnit_iff_exists_inv.mp hunit_d
  have hbdinv :
      (Localization.mk (ψ (b : A)) 1 * Localization.mk (ψ (d : A)) 1) *
          (vb * vd) = 1 := by
    calc
      _ = (Localization.mk (ψ (b : A)) 1 * vb) *
          (Localization.mk (ψ (d : A)) 1 * vd) := by ring
      _ = 1 := by rw [hvb, hvd, one_mul]
  have hprod :
      ((scalarExtensionTwistSection r θ (i + j) W' vW).1 xW :
        Localization.AtPrime xW.1.asHomogeneousIdeal.toIdeal) *
          (Localization.mk (ψ (b : A)) 1 * Localization.mk (ψ (d : A)) 1) =
        (((scalarExtensionTwistSection r θ i W' sW).1 xW :
          Localization.AtPrime xW.1.asHomogeneousIdeal.toIdeal) *
            ((scalarExtensionTwistSection r θ j W' tW).1 xW :
              Localization.AtPrime xW.1.asHomogeneousIdeal.toIdeal)) *
          (Localization.mk (ψ (b : A)) 1 * Localization.mk (ψ (d : A)) 1) := by
    calc
      _ = Localization.mk (ψ (a : A)) 1 * Localization.mk (ψ (c : A)) 1 := hvEq
      _ = (((scalarExtensionTwistSection r θ i W' sW).1 xW :
          Localization.AtPrime xW.1.asHomogeneousIdeal.toIdeal) *
            Localization.mk (ψ (b : A)) 1) *
          (((scalarExtensionTwistSection r θ j W' tW).1 xW :
            Localization.AtPrime xW.1.asHomogeneousIdeal.toIdeal) *
              Localization.mk (ψ (d : A)) 1) := by rw [hsEq, htEq]
      _ = _ := by ring
  have hlocal :
      ((scalarExtensionTwistSection r θ (i + j) W' vW).1 xW :
        Localization.AtPrime xW.1.asHomogeneousIdeal.toIdeal) =
        ((scalarExtensionTwistSection r θ i W' sW).1 xW :
          Localization.AtPrime xW.1.asHomogeneousIdeal.toIdeal) *
          ((scalarExtensionTwistSection r θ j W' tW).1 xW :
            Localization.AtPrime xW.1.asHomogeneousIdeal.toIdeal) := by
    calc
      _ = (((scalarExtensionTwistSection r θ (i + j) W' vW).1 xW :
          Localization.AtPrime xW.1.asHomogeneousIdeal.toIdeal) *
          (Localization.mk (ψ (b : A)) 1 * Localization.mk (ψ (d : A)) 1)) *
          (vb * vd) := by
            rw [mul_assoc, hbdinv, mul_one]
      _ = _ := by rw [hprod]
      _ = _ := by rw [mul_assoc, hbdinv, mul_one]
  have hsresW := scalarExtensionTwistSection_restrict r θ i U W' ewS.le s xW
  have htresW := scalarExtensionTwistSection_restrict r θ j U W' ewS.le t xW
  have hvresW := scalarExtensionTwistSection_restrict r θ (i + j) U W' ewS.le v xW
  have hsresW' : (scalarExtensionTwistSection r θ i W' sW).1 xW =
      (scalarExtensionTwistSection r θ i U s).1 x := by
    have he : homOfLE ewS.le = ewS := Subsingleton.elim _ _
    simpa [sW, xW, he] using hsresW
  have htresW' : (scalarExtensionTwistSection r θ j W' tW).1 xW =
      (scalarExtensionTwistSection r θ j U t).1 x := by
    have he : homOfLE ewS.le = ewS := Subsingleton.elim _ _
    simpa [tW, xW, he] using htresW
  have hvresW' : (scalarExtensionTwistSection r θ (i + j) W' vW).1 xW =
      (scalarExtensionTwistSection r θ (i + j) U v).1 x := by
    have he : homOfLE ewS.le = ewS := Subsingleton.elim _ _
    simpa [vW, xW, he] using hvresW
  rw [← hvresW', ← hsresW', ← htresW']
  exact hlocal

end AlgebraicGeometry.Proj
