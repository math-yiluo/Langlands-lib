/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-! # Pulling back a relation between fractions on two projective charts

Source: Stacks Project, Constructions, Tags 01N8 and 01NK.
(blueprint: lem-sc-proj-chart-pullback-fraction-relation).
-/

@[expose] public section

universe v
open CategoryTheory

namespace AlgebraicGeometry

private lemma inclusion_top (X : Scheme.{v}) (U : X.Opens) :
    U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
  dsimp [Scheme.Hom.appLE, Scheme.Opens.topIso]
  rw [← Functor.map_comp]
  congr 1

private lemma away_top
    (A : Type v) [CommRing A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (d : ℕ) (s : 𝒜 d) (hd : 0 < d) :
    let f := Proj.awayι 𝒜 s.val s.property hd
    Proj.awayToSection 𝒜 s.val ≫
      f.appLE (Proj.basicOpen 𝒜 s.val) ⊤
        (by
          dsimp only [f]
          rw [← Proj.opensRange_awayι 𝒜 s.val s.property hd]
          simp) =
      (Scheme.ΓSpecIso (.of (HomogeneousLocalization.Away 𝒜 s.val))).inv := by
  dsimp only
  let i := Proj.basicOpenIsoSpec 𝒜 s.val s.property hd
  have hc := Scheme.Hom.appLE_comp_appLE i.inv (Proj.basicOpen 𝒜 s.val).ι
    (Proj.basicOpen 𝒜 s.val) ⊤ ⊤ (by simp) (by simp)
  change Proj.awayToSection 𝒜 s.val ≫
    (i.inv ≫ (Proj.basicOpen 𝒜 s.val).ι).appLE _ ⊤ _ = _
  rw [← hc, inclusion_top]
  have ht : i.inv.appLE ⊤ ⊤ (by simp) = i.inv.appTop := by
    simp [Scheme.Hom.appLE]
  rw [ht]
  have hb := Proj.basicOpenToSpec_app_top 𝒜 s.val
  have hi : (Proj.basicOpenToSpec 𝒜 s.val).appTop ≫ i.inv.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop]
    change (i.inv ≫ i.hom).appTop = _
    simp
  dsimp only [Scheme.Hom.appTop] at hi
  rw [hb, Category.assoc] at hi
  apply (cancel_epi (Scheme.ΓSpecIso _).hom).1
  simpa only [Category.assoc, Iso.hom_inv_id] using hi
/-- A homogeneous numerator relation gives the corresponding scalar relation after pullback.
Source: Stacks Project, Constructions, Tags 01N8 and 01NK, comparison on overlapping charts.
(blueprint: lem-sc-proj-chart-pullback-fraction-relation).

Proof: Use the common chart D_+(ts). The two localization maps send xi/t^n
and p/s^N to xi*s^n/(ts)^n and p*t^N/(ts)^N. Their product equals
r*t^N/(ts)^N: cross multiplication reduces the equality to xi*p = r*t^n
multiplied by s^n*t^N*(ts)^N. This uses no cancellation. Apply the canonical
map from the homogeneous localization at ts to sections and pull back to
V = g^{-1}D_+(t). This is possible because g factors through D_+(s), so V
also lies over D_+(ts). Naturality of awayToSection and g.app identifies the
two localization maps with the pullbacks of the t- and s-chart sections.
The inverse s-chart isomorphism and basicOpenToSpec_app_top identify its
map on sections with the canonical Spec map. Compose with q and apply hq;
then restrict to V. The topIso of U identifies the resulting restriction
with the ambient restriction to W. Applying the ring map preserves products
and proves the displayed equality. The same calculation covers n=0, N=0,
zero numerators, t of degree zero, nilpotents, and empty overlaps. -/
theorem Proj.chart_pullback_fraction_relation
    (A : Type v) [CommRing A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (X : Scheme.{v}) (d : ℕ) (s : 𝒜 d) (hd : 0 < d) (U : X.Opens)
    (ρ : HomogeneousLocalization.Away 𝒜 s.val →+* Γ(X, U))
    (q : U.toScheme ⟶ Spec (.of (HomogeneousLocalization.Away 𝒜 s.val)))
    (hq : (Scheme.ΓSpecIso (.of (HomogeneousLocalization.Away 𝒜 s.val))).inv ≫
      q.appTop = CommRingCat.ofHom ρ ≫ U.topIso.inv)
    (e : ℕ) (t : 𝒜 e) (n N : ℕ) (ξ : 𝒜 (n • e))
    (p r : 𝒜 (N • d)) (h : ξ.val * p.val = r.val * t.val ^ n) :
    let g := q ≫ Proj.awayι 𝒜 s.val s.property hd
    let W := U.ι ''ᵁ (g ⁻¹ᵁ Proj.basicOpen 𝒜 t.val)
    (show Γ(X, W) from g.app (Proj.basicOpen 𝒜 t.val)
      (Proj.awayToSection 𝒜 t.val
        (HomogeneousLocalization.Away.mk 𝒜 t.property n ξ.val ξ.property))) *
      X.presheaf.map (homOfLE (U.ι_image_le _)).op
        (ρ (HomogeneousLocalization.Away.mk 𝒜 s.property N p.val p.property)) =
      X.presheaf.map (homOfLE (U.ι_image_le _)).op
        (ρ (HomogeneousLocalization.Away.mk 𝒜 s.property N r.val r.property)) := by
  dsimp only
  let f := Proj.awayι 𝒜 s.val s.property hd
  let g := q ≫ f
  let V := g ⁻¹ᵁ Proj.basicOpen 𝒜 t.val
  have hf : f ⁻¹ᵁ Proj.basicOpen 𝒜 s.val = ⊤ := by
    dsimp only [f]
    rw [← Proj.opensRange_awayι 𝒜 s.val s.property hd,
      Scheme.Hom.preimage_opensRange]
  have hg : g ⁻¹ᵁ Proj.basicOpen 𝒜 s.val = ⊤ := by
    change q ⁻¹ᵁ (f ⁻¹ᵁ Proj.basicOpen 𝒜 s.val) = ⊤
    rw [hf, Scheme.Hom.preimage_top]
  have hsTop : ⊤ ≤ g ⁻¹ᵁ Proj.basicOpen 𝒜 s.val := hg.ge
  have hVs : V ≤ g ⁻¹ᵁ Proj.basicOpen 𝒜 s.val := le_top.trans hsTop
  have hVst : V ≤ g ⁻¹ᵁ Proj.basicOpen 𝒜 (t.val * s.val) := by
    rw [Proj.basicOpen_mul]
    change V ≤ (g ⁻¹ᵁ Proj.basicOpen 𝒜 t.val) ⊓
      (g ⁻¹ᵁ Proj.basicOpen 𝒜 s.val)
    exact le_inf le_rfl hVs
  have hstop : Proj.awayToSection 𝒜 s.val ≫
      g.appLE (Proj.basicOpen 𝒜 s.val) ⊤ hsTop =
      CommRingCat.ofHom ρ ≫ U.topIso.inv := by
    have hcomp := Scheme.Hom.appLE_comp_appLE q f (Proj.basicOpen 𝒜 s.val)
      ⊤ ⊤ hf.ge (by simp)
    rw [← hcomp, ← Category.assoc, away_top]
    have htop : q.appLE ⊤ ⊤ (by simp) = q.appTop := by
      simp only [Scheme.Hom.appLE, Scheme.Hom.preimage_top, homOfLE_refl,
        op_id]
      erw [CategoryTheory.Functor.map_id, Category.comp_id]
    rw [htop]
    exact hq
  have hsres : Proj.awayToSection 𝒜 s.val ≫
      g.appLE (Proj.basicOpen 𝒜 s.val) V hVs =
      CommRingCat.ofHom ρ ≫ X.presheaf.map (homOfLE (U.ι_image_le V)).op := by
    rw [← Scheme.Hom.appLE_map g hsTop (homOfLE (le_top : V ≤ ⊤)).op,
      ← Category.assoc, hstop, Category.assoc]
    congr 1
    dsimp [Scheme.Opens.topIso]
    rw [← Functor.map_comp]
    congr 1
  let bt := HomogeneousLocalization.Away.mk 𝒜 t.property n ξ.val ξ.property
  let bp := HomogeneousLocalization.Away.mk 𝒜 s.property N p.val p.property
  let br := HomogeneousLocalization.Away.mk 𝒜 s.property N r.val r.property
  let mt := HomogeneousLocalization.awayMap 𝒜 s.property (rfl : t.val * s.val = _)
  let ms := HomogeneousLocalization.awayMap 𝒜 t.property (mul_comm t.val s.val)
  have hfrac : mt bt * ms bp = ms br := by
    apply HomogeneousLocalization.val_injective
    dsimp only [mt, ms, bt, bp, br]
    rw [HomogeneousLocalization.val_mul,
      HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.awayMap_mk,
      HomogeneousLocalization.awayMap_mk]
    simp only [HomogeneousLocalization.Away.val_mk]
    rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [Submonoid.coe_mul, Submonoid.coe_one, one_mul]
    calc
      _ = (ξ.val * p.val) * (s.val ^ n * t.val ^ N * (t.val * s.val) ^ N) := by ring
      _ = _ := by rw [h]; simp only [mul_pow]; ring
  let φ := Proj.awayToSection 𝒜 (t.val * s.val) ≫
    g.appLE (Proj.basicOpen 𝒜 (t.val * s.val)) V hVst
  have htmap : Proj.awayToSection 𝒜 t.val ≫ g.app (Proj.basicOpen 𝒜 t.val) =
      CommRingCat.ofHom mt ≫ φ := by
    dsimp only [φ, mt, ms]
    rw [Proj.awayMap_awayToSection_assoc, Scheme.Hom.map_appLE]
    congr 1
    exact Scheme.Hom.app_eq_appLE g
  have hsmap : Proj.awayToSection 𝒜 s.val ≫
      g.appLE (Proj.basicOpen 𝒜 s.val) V hVs = CommRingCat.ofHom ms ≫ φ := by
    dsimp only [φ, mt, ms]
    rw [Proj.awayMap_awayToSection_assoc, Scheme.Hom.map_appLE]
  have hpull := congrArg φ.hom hfrac
  rw [map_mul] at hpull
  change φ (mt bt) * φ (ms bp) = φ (ms br) at hpull
  have htval := ConcreteCategory.congr_hom htmap bt
  have hpval := ConcreteCategory.congr_hom (hsres.symm.trans hsmap) bp
  have hrval := ConcreteCategory.congr_hom (hsres.symm.trans hsmap) br
  simp only [ConcreteCategory.comp_apply, CommRingCat.hom_ofHom] at htval hpval hrval
  calc
    _ = φ (mt bt) * φ (ms bp) := congrArg₂ (· * ·) htval hpval
    _ = φ (ms br) := hpull
    _ = _ := hrval.symm

end AlgebraicGeometry
