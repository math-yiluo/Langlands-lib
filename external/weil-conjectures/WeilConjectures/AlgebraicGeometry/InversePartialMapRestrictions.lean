/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Birational.Composition

/-!
# Inverse restrictions of partial maps

Source: Stacks Project, Tag 0BAA (Lemma 29.50.12).
(blueprint: lem-sbc-inverse-partial-map-restrictions)
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry.Scheme.PartialMap

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private lemma restrict_comp_factor
    {X Y Z : Scheme.{u}} [IsIntegral X] [Nonempty Y]
    (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z)
    (U : X.Opens) (hU : Dense (U : Set X)) (hUfg : U ≤ (f.comp g).domain) :
    ∃ k : U.toScheme ⟶ g.domain.toScheme,
      k ≫ g.domain.ι = X.homOfLE (hUfg.trans (f.domain.ι_image_le _)) ≫ f.hom ∧
      k ≫ g.hom = ((f.comp g).restrict U hU hUfg).hom := by
  change U ≤ f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ g.domain) at hUfg
  let k := X.homOfLE hUfg ≫
    (f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).inv ≫ f.hom ∣_ g.domain
  refine ⟨k, ?_, rfl⟩
  dsimp [k]
  simp only [Category.assoc, morphismRestrict_ι]
  rw [f.domain.isoImage_ι_inv_ι_assoc]
  rw [homOfLE_homOfLE_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Dominant partial maps whose composites are equivalent to the identities restrict
to mutually inverse morphisms on dense opens, preserving the supplied forward map.

Source: Stacks Project, Tag 0BAA (Lemma 29.50.12).
Proof: Equivalence to the identities supplies dense opens W_X and W_Y on which g f
and f g are identity morphisms into X and Y. Shrink W_X to lie in the forward domain
and in the inverse image of W_Y, and call the resulting open U. Define V to be the
points of W_Y whose image under g lies in U. Both contain generic points: dominance
sends generic points to generic points, and every dense open contains the generic
point. The identities on W_X and W_Y imply that f(U) is contained in V and g(V) is
contained in U. Lift the restricted maps through these open inclusions. Their two
composites become the identity after composing with the open inclusions, so they
are identity morphisms because open inclusions are monomorphisms. The lift of f
has the required compatibility with its original restriction by construction.
The hypothesis that both composites agree with the identities is essential;
one-sided inverse maps do not suffice.

(blueprint: lem-sbc-inverse-partial-map-restrictions) -/
theorem exists_inverse_restrictions_of_comp_equiv_id
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X.PartialMap Y) [IsDominant f.hom]
    (g : Y.PartialMap X) [IsDominant g.hom]
    (hf : (f.comp g).equiv (PartialMap.id X))
    (hg : (g.comp f).equiv (PartialMap.id Y)) :
    ∃ (U : X.Opens) (_ : Dense (U : Set X)) (hUf : U ≤ f.domain)
      (V : Y.Opens) (_ : Dense (V : Set Y))
      (f' : U.toScheme ⟶ V.toScheme) (g' : V.toScheme ⟶ U.toScheme),
      f' ≫ g' = 𝟙 _ ∧ g' ≫ f' = 𝟙 _ ∧
        f' ≫ V.ι = X.homOfLE hUf ≫ f.hom := by
  obtain ⟨A, hA, hAfg, hAid, hEqA⟩ := hf
  obtain ⟨B, hB, hBgf, hBid, hEqB⟩ := hg
  obtain ⟨Fa, hFa, hFag⟩ := restrict_comp_factor f g A hA hAfg
  obtain ⟨Gb, hGb, hGbf⟩ := restrict_comp_factor g f B hB hBgf
  have hAf : A ≤ f.domain := hAfg.trans (f.domain.ι_image_le _)
  have hBg : B ≤ g.domain := hBgf.trans (g.domain.ι_image_le _)
  have hAinv : Fa ≫ g.hom = A.ι := by
    rw [hFag, hEqA]
    simpa only [restrict_hom, id, Hom.toPartialMap_hom, Category.assoc,
      Category.comp_id, topIso_hom] using X.homOfLE_ι (show A ≤ ⊤ from hAid)
  have hBinv : Gb ≫ f.hom = B.ι := by
    rw [hGbf, hEqB]
    simpa only [restrict_hom, id, Hom.toPartialMap_hom, Category.assoc,
      Category.comp_id, topIso_hom] using Y.homOfLE_ι (show B ≤ ⊤ from hBid)
  let F0 := X.homOfLE hAf ≫ f.hom
  let G0 := Y.homOfLE hBg ≫ g.hom
  let U := A.ι ''ᵁ (F0 ⁻¹ᵁ B)
  have hUA : U ≤ A := A.ι_image_le _
  have hUf : U ≤ f.domain := hUA.trans hAf
  have hU : Dense (U : Set X) := by
    have : IsDominant (X.homOfLE hAf) := Opens.isDominant_homOfLE hA hAf
    have : IsDominant F0 := inferInstance
    apply U.2.dense
    obtain ⟨y, hyB, x, hxy⟩ :=
      F0.denseRange.inter_open_nonempty _ B.2 hB.nonempty
    exact ⟨x.1, x, by simpa [hxy] using hyB, rfl⟩
  let V := B.ι ''ᵁ (G0 ⁻¹ᵁ U)
  have hVB : V ≤ B := B.ι_image_le _
  have hVg : V ≤ g.domain := hVB.trans hBg
  have hV : Dense (V : Set Y) := by
    have : IsDominant (Y.homOfLE hBg) := Opens.isDominant_homOfLE hB hBg
    have : IsDominant G0 := inferInstance
    apply V.2.dense
    obtain ⟨x, hxU, y, hyx⟩ :=
      G0.denseRange.inter_open_nonempty _ U.2 hU.nonempty
    exact ⟨y.1, y, by simpa [hyx] using hxU, rfl⟩
  let F := X.homOfLE hUf ≫ f.hom
  let G := Y.homOfLE hVg ≫ g.hom
  have hFcomp : X.homOfLE hUA ≫ F0 = F := by
    dsimp [F0, F]
    rw [homOfLE_homOfLE_assoc]
  have hGcomp : Y.homOfLE hVB ≫ G0 = G := by
    dsimp [G0, G]
    rw [homOfLE_homOfLE_assoc]
  have hFU : ∀ x : U.toScheme, F x ∈ B := by
    intro x
    obtain ⟨a, ha, hax⟩ := x.2
    have ha' : (X.homOfLE hUA x) = a := by
      apply Subtype.ext
      simpa using hax.symm
    rw [← hFcomp, Hom.comp_apply, ha']
    exact ha
  have hGV : ∀ y : V.toScheme, G y ∈ U := by
    intro y
    obtain ⟨b, hb, hby⟩ := y.2
    have hb' : (Y.homOfLE hVB y) = b := by
      apply Subtype.ext
      simpa using hby.symm
    rw [← hGcomp, Hom.comp_apply, hb']
    exact hb
  have hFV : ∀ x : U.toScheme, F x ∈ V := by
    intro x
    let b : B.toScheme := ⟨F x, hFU x⟩
    refine ⟨b, ?_, rfl⟩
    have hFaPoint : Fa (X.homOfLE hUA x) =
        Y.homOfLE hBg b := by
      apply Subtype.ext
      have H := congrArg (fun k : A.toScheme ⟶ Y ↦ k (X.homOfLE hUA x)) hFa
      rw [homOfLE_apply]
      change (Fa (X.homOfLE hUA x)).1 = F x
      change _ = F0 (X.homOfLE hUA x) at H
      have H' : F0 (X.homOfLE hUA x) = F x :=
        congrArg (fun k : U.toScheme ⟶ Y ↦ k x) hFcomp
      exact H.trans H'
    have H := congrArg (fun k : A.toScheme ⟶ X ↦ k (X.homOfLE hUA x)) hAinv
    change g.hom (Y.homOfLE hBg b) ∈ U
    rw [← hFaPoint]
    have H' : g.hom (Fa (X.homOfLE hUA x)) = x.1 := by
      simpa [Hom.comp_apply] using H
    rw [H']
    exact x.2
  let F' := IsOpenImmersion.lift V.ι F (by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨F x, hFV x⟩, rfl⟩)
  let G' := IsOpenImmersion.lift U.ι G (by
    rintro _ ⟨y, rfl⟩
    exact ⟨⟨G y, hGV y⟩, rfl⟩)
  have hF' : F' ≫ V.ι = F := IsOpenImmersion.lift_fac ..
  have hG' : G' ≫ U.ι = G := IsOpenImmersion.lift_fac ..
  refine ⟨U, hU, hUf, V, hV, F', G', ?_, ?_, hF'⟩
  · apply (cancel_mono U.ι).mp
    rw [Category.assoc, hG']
    change F' ≫ (Y.homOfLE hVg ≫ g.hom) = _
    have H : F' ≫ Y.homOfLE hVg = X.homOfLE hUA ≫ Fa := by
      apply (cancel_mono g.domain.ι).mp
      simp only [Category.assoc, homOfLE_ι]
      rw [hF', hFa]
      simp only [← Category.assoc, homOfLE_homOfLE]
      rfl
    rw [← Category.assoc, H, Category.assoc, hAinv]
    simp
  · apply (cancel_mono V.ι).mp
    rw [Category.assoc, hF']
    change G' ≫ (X.homOfLE hUf ≫ f.hom) = _
    have H : G' ≫ X.homOfLE hUf = Y.homOfLE hVB ≫ Gb := by
      apply (cancel_mono f.domain.ι).mp
      simp only [Category.assoc, homOfLE_ι]
      rw [hG', hGb]
      simp only [← Category.assoc, homOfLE_homOfLE]
      rfl
    rw [← Category.assoc, H, Category.assoc, hBinv]
    simp

end AlgebraicGeometry.Scheme.PartialMap
