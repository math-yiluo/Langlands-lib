/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Canonical
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearCombination

/-! # Local equations of the projective-line diagonal

Source: blueprint lemma-class-diagonal-projective-line, the four product-chart equations.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProjectiveSpace

private lemma appLE_eq_of_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (U V e) : f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h
  rfl

private lemma chart_hom_ext {n : Type u} {S X : Scheme.{u}}
    {f g : X ⟶ ℙ(n; S)} (i : n)
    (hf : ⊤ ≤ f ⁻¹ᵁ standardOpen n S i) (hg : ⊤ ≤ g ⁻¹ᵁ standardOpen n S i)
    (hS : f ≫ ℙ(n; S) ↘ S = g ≫ ℙ(n; S) ↘ S)
    (hr : ∀ k, f.appLE _ ⊤ hf (coordRatio n S i k) =
      g.appLE _ ⊤ hg (coordRatio n S i k)) : f = g := by
  let Z := Spec (CommRingCat.of (ULift.{u} ℤ))
  let b : S ⟶ Z := specULiftZIsTerminal.from S
  have hpre : (map n b) ⁻¹ᵁ standardOpen n Z i = standardOpen n S i := by
    simp only [standardOpen, ← Scheme.Hom.comp_preimage, map_toProjInt]
  have hf' : (f ≫ map n b) ⁻¹ᵁ standardOpen n Z i = ⊤ := by
    rw [Scheme.Hom.comp_preimage, hpre]
    exact top_le_iff.mp hf
  have hg' : (g ≫ map n b) ⁻¹ᵁ standardOpen n Z i = ⊤ := by
    rw [Scheme.Hom.comp_preimage, hpre]
    exact top_le_iff.mp hg
  have he : f ≫ map n b = g ≫ map n b := by
    apply hom_ext_of_preimage_standardOpen_eq_top i hf' hg'
    · exact specULiftZIsTerminal.hom_ext _ _
    · intro k
      have hmap := map_appLE_coordRatio b i k hpre.ge
      have h₁ := congrArg (fun x ↦ f.appLE _ ⊤ hf x) hmap
      have h₂ := congrArg (fun x ↦ g.appLE _ ⊤ hg x) hmap
      rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE] at h₁ h₂
      exact h₁.trans ((hr k).trans h₂.symm)
  apply hom_ext n S hS
  have := congrArg (fun h ↦ h ≫ toProjInt n Z) he
  simpa only [Category.assoc, map_toProjInt] using this

private lemma pull_ratio_mul {n : Type u} {S X : Scheme.{u}} (f : X ⟶ ℙ(n; S))
    (i j k : n) (hi : ⊤ ≤ f ⁻¹ᵁ standardOpen n S i)
    (hj : ⊤ ≤ f ⁻¹ᵁ standardOpen n S j) :
    f.appLE _ ⊤ hi (coordRatio n S i k) =
      f.appLE _ ⊤ hj (coordRatio n S j k) *
        f.appLE _ ⊤ hi (coordRatio n S i j) := by
  have h := congrArg
    (fun x ↦ f.appLE (standardOpen n S i ⊓ standardOpen n S j) ⊤
      (le_inf hi hj) x)
    (map_coordRatio_eq_mul (inf_le_left : standardOpen n S i ⊓ standardOpen n S j ≤ _)
      inf_le_right k)
  simpa only [map_mul, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE] using h

private lemma chart_det_zero {S X : Scheme.{u}} (f : X ⟶ ProjectiveLine S)
    (i j : ULift.{u} (Fin 2))
    (hi : ⊤ ≤ f ⁻¹ᵁ standardOpen (ULift.{u} (Fin 2)) S i)
    (hj : ⊤ ≤ f ⁻¹ᵁ standardOpen (ULift.{u} (Fin 2)) S j) :
    f.appLE _ ⊤ hi (coordRatio _ S i ⟨0⟩) *
        f.appLE _ ⊤ hj (coordRatio _ S j ⟨1⟩) -
      f.appLE _ ⊤ hi (coordRatio _ S i ⟨1⟩) *
        f.appLE _ ⊤ hj (coordRatio _ S j ⟨0⟩) = 0 := by
  rw [pull_ratio_mul f i j ⟨0⟩ hi hj, pull_ratio_mul f i j ⟨1⟩ hi hj]
  ring

private lemma normalized_pair_mul {R : Type u} [CommRing R]
    (a b : ULift.{u} (Fin 2) → R) (i : ULift.{u} (Fin 2)) (hai : a i = 1)
    (hd : a ⟨0⟩ * b ⟨1⟩ - a ⟨1⟩ * b ⟨0⟩ = 0)
    (k : ULift.{u} (Fin 2)) : a k * b i = b k := by
  rcases i with ⟨i⟩
  rcases k with ⟨k⟩
  fin_cases i <;> fin_cases k <;> simp_all [sub_eq_zero]

private lemma chart_eq_of_det_zero {S X : Scheme.{u}}
    (f g : X ⟶ ProjectiveLine S) (i j : ULift.{u} (Fin 2))
    (hi : ⊤ ≤ f ⁻¹ᵁ standardOpen (ULift.{u} (Fin 2)) S i)
    (hj : ⊤ ≤ g ⁻¹ᵁ standardOpen (ULift.{u} (Fin 2)) S j)
    (hS : f ≫ ProjectiveLine S ↘ S = g ≫ ProjectiveLine S ↘ S)
    (hd : f.appLE _ ⊤ hi (coordRatio _ S i ⟨0⟩) *
        g.appLE _ ⊤ hj (coordRatio _ S j ⟨1⟩) -
      f.appLE _ ⊤ hi (coordRatio _ S i ⟨1⟩) *
        g.appLE _ ⊤ hj (coordRatio _ S j ⟨0⟩) = 0) : f = g := by
  let a (k : ULift.{u} (Fin 2)) := f.appLE _ ⊤ hi (coordRatio _ S i k)
  let b (k : ULift.{u} (Fin 2)) := g.appLE _ ⊤ hj (coordRatio _ S j k)
  have hai : a i = 1 := by simp [a]
  have hbj : b j = 1 := by simp [b]
  have hab (k : ULift.{u} (Fin 2)) : a k * b i = b k :=
    normalized_pair_mul a b i hai hd k
  have hu : IsUnit (b i) := IsUnit.of_mul_eq_one (a j) (by rw [mul_comm, hab j, hbj])
  have hgi : ⊤ ≤ g ⁻¹ᵁ standardOpen (ULift.{u} (Fin 2)) S i := by
    calc
      ⊤ = X.basicOpen (b i) := (X.basicOpen_of_isUnit hu).symm
      _ = ⊤ ⊓ g ⁻¹ᵁ (ProjectiveLine S).basicOpen (coordRatio _ S j i) :=
        Scheme.basicOpen_appLE g _ _ hj _
      _ ≤ g ⁻¹ᵁ standardOpen (ULift.{u} (Fin 2)) S i :=
        inf_le_right.trans (g.preimage_mono (basicOpen_coordRatio_le S j i))
  apply chart_hom_ext i hi hgi hS
  intro k
  apply hu.mul_right_cancel
  exact (hab k).trans (pull_ratio_mul g j i k hj hgi)

private lemma ideal_ker_appLE {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.affineOpens) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U.1)
    {s : Γ(Y, U)} (hs : s ∈ f.ker.ideal U) : f.appLE U.1 V h s = 0 := by
  have hzero := RingHom.mem_ker.mp (f.ideal_ker_le U hs)
  simp only [Scheme.Hom.appLE, CommRingCat.comp_apply, hzero, map_zero]

private lemma fromSpec_appLE {Y : Scheme.{u}} (U : Y.affineOpens)
    (h : ⊤ ≤ U.2.fromSpec ⁻¹ᵁ U.1) :
    U.2.fromSpec.appLE U.1 ⊤ h = (Scheme.ΓSpecIso Γ(Y, U)).inv := by
  have hi : U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge = U.1.topIso.inv := by
    rw [Scheme.Opens.ι_appLE]
    rfl
  have he : ⊤ ≤ U.2.isoSpec.inv ⁻¹ᵁ (⊤ : U.1.toScheme.Opens) := le_top
  have hc := Scheme.Hom.appLE_comp_appLE U.2.isoSpec.inv U.1.ι U.1 ⊤ ⊤
    U.1.ι_preimage_self.ge he
  change _ = U.2.fromSpec.appLE _ _ _ at hc
  rw [← hc, hi, Scheme.Hom.appLE_top_top, IsAffineOpen.isoSpec_inv_appTop,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

private lemma kernel_ideal_eq_span_of_test {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] (U : Y.affineOpens) (s : Γ(Y, U))
    (test : ∀ (Z : Scheme.{u}) (g : Z ⟶ Y) (hg : ⊤ ≤ g ⁻¹ᵁ U.1),
      g.appLE U.1 ⊤ hg s = 0 ↔ ∃ h : Z ⟶ X, h ≫ f = g) :
    f.ker.ideal U = Ideal.span {s} := by
  apply le_antisymm
  · let I : Ideal Γ(Y, U) := Ideal.span {s}
    let φ : Γ(Y, U) ⟶ CommRingCat.of (Γ(Y, U) ⧸ I) :=
      CommRingCat.ofHom (Ideal.Quotient.mk I)
    let g := Spec.map φ ≫ U.2.fromSpec
    have hU : ⊤ ≤ U.2.fromSpec ⁻¹ᵁ U.1 := by
      intro x _
      exact U.2.range_fromSpec.le ⟨x, rfl⟩
    have hg : ⊤ ≤ g ⁻¹ᵁ U.1 := by
      rw [Scheme.Hom.comp_preimage]
      exact le_top.trans ((Spec.map φ).preimage_mono hU)
    have happ : g.appLE U.1 ⊤ hg ≫ (Scheme.ΓSpecIso _).hom = φ := by
      have hc := Scheme.Hom.appLE_comp_appLE (Spec.map φ) U.2.fromSpec U.1 ⊤ ⊤ hU
        (le_top : ⊤ ≤ (Spec.map φ) ⁻¹ᵁ ⊤)
      change _ = g.appLE _ _ _ at hc
      rw [← hc, fromSpec_appLE, Scheme.Hom.appLE_top_top,
        ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hzero : g.appLE U.1 ⊤ hg s = 0 := by
      apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).hom).1
      rw [map_zero, ← CommRingCat.comp_apply, happ]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    obtain ⟨h, hh⟩ := (test _ g hg).mp hzero
    intro x hx
    have hx' : x ∈ g.ker.ideal U := by
      rw [← hh]
      exact h.le_ker_comp f U hx
    have hzero' := ideal_ker_appLE g U ⊤ hg hx'
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change φ x = 0
    rw [← happ, CommRingCat.comp_apply, hzero', map_zero]
  · rw [Ideal.span_singleton_le_iff_mem, f.ker_apply U, RingHom.mem_ker]
    let V := f ⁻¹ᵁ U.1
    let g := V.ι ≫ f
    have hg : ⊤ ≤ g ⁻¹ᵁ U.1 := by
      rw [Scheme.Hom.comp_preimage]
      exact V.ι_preimage_self.ge
    have hzero := (test _ g hg).mpr ⟨V.ι, rfl⟩
    have hmap : g.appLE U.1 ⊤ hg s = V.topIso.inv (f.app U.1 s) := by
      rw [Scheme.Hom.comp_appLE, CommRingCat.comp_apply, Scheme.Opens.ι_appLE]
      rfl
    rw [hmap] at hzero
    exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso V.topIso.inv).1).mp hzero

/-- On an affine open in the product chart `x_i y_j ≠ 0`, the ideal of the
projective-line diagonal is generated by the normalized determinant.
Source: blueprint lemma-class-diagonal-projective-line, first sentence (the determinant
equation), and lem-sp-finite-p1-diagonal-picard, proof step 1.
(auxiliary; not a blueprint node)

Proof: work first over an affine base Spec R. The four product charts have
coordinate rings R[u,v]. On the equal-index charts the diagonal is the graph
u = v, whose kernel is (v-u) or (u-v). On the unequal-index charts it is the
open graph v = u^{-1}, represented by R[u,v]/(1-uv); the opposite ordering
changes the generator by -1. These are precisely the displayed determinants
of coordinate ratios, since the denominator coordinates equal 1. The affine
chart identifications commute with the maps to the base and with coordinate
ratios. Restrict the resulting equality of quasicoherent ideals to an
arbitrary affine open U of the product chart. For a general base, cover it by
affine opens; the equations agree with the same displayed determinant on each
intersection, so the ideal equality descends. This argument uses polynomial
quotients, not residue-field points, and works for nonreduced and zero rings. -/
theorem p1_diagonal_ideal_on_chart (S : Scheme.{u})
    (i j : ULift.{u} (Fin 2))
    (U : (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)).affineOpens)
    (hi : U.1 ≤ pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S) ⁻¹ᵁ
      standardOpen (ULift.{u} (Fin 2)) S i)
    (hj : U.1 ≤ pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S) ⁻¹ᵁ
      standardOpen (ULift.{u} (Fin 2)) S j) :
    (pullback.diagonal (ProjectiveLine S ↘ S)).ker.ideal U =
      Ideal.span {((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)).appLE _ U.1 hi
          (coordRatio (ULift.{u} (Fin 2)) S i ⟨0⟩)) *
        ((pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)).appLE _ U.1 hj
          (coordRatio (ULift.{u} (Fin 2)) S j ⟨1⟩)) -
        ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)).appLE _ U.1 hi
          (coordRatio (ULift.{u} (Fin 2)) S i ⟨1⟩)) *
        ((pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)).appLE _ U.1 hj
          (coordRatio (ULift.{u} (Fin 2)) S j ⟨0⟩))} := by
  apply kernel_ideal_eq_span_of_test
  intro X h hh
  let f := h ≫ pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)
  let g := h ≫ pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)
  have hi' : ⊤ ≤ f ⁻¹ᵁ standardOpen (ULift.{u} (Fin 2)) S i :=
    hh.trans (h.preimage_mono hi)
  have hj' : ⊤ ≤ g ⁻¹ᵁ standardOpen (ULift.{u} (Fin 2)) S j :=
    hh.trans (h.preimage_mono hj)
  have hS : f ≫ ProjectiveLine S ↘ S = g ≫ ProjectiveLine S ↘ S := by
    simp only [f, g, Category.assoc, pullback.condition]
  have hfst (k : ULift.{u} (Fin 2)) :
      h.appLE U.1 ⊤ hh
        ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)).appLE _ U.1 hi
          (coordRatio _ S i k)) = f.appLE _ ⊤ hi' (coordRatio _ S i k) := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  have hsnd (k : ULift.{u} (Fin 2)) :
      h.appLE U.1 ⊤ hh
        ((pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)).appLE _ U.1 hj
          (coordRatio _ S j k)) = g.appLE _ ⊤ hj' (coordRatio _ S j k) := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  simp only [map_sub, map_mul, hfst, hsnd]
  constructor
  · intro hd
    have he : f = g := chart_eq_of_det_zero f g i j hi' hj' hS hd
    refine ⟨f, ?_⟩
    apply pullback.hom_ext
    · simp [f]
    · simpa using he
  · rintro ⟨k, hk⟩
    have he : g = f := by
      simp only [f, g, ← hk, Category.assoc, pullback.diagonal_fst,
        pullback.diagonal_snd, Category.comp_id]
    have heapp : g.appLE (standardOpen (ULift.{u} (Fin 2)) S j) ⊤ hj' =
        f.appLE _ ⊤ (he ▸ hj') := appLE_eq_of_eq he _ _ _
    rw [heapp]
    exact chart_det_zero f i j hi' _

end AlgebraicGeometry.ProjectiveSpace
