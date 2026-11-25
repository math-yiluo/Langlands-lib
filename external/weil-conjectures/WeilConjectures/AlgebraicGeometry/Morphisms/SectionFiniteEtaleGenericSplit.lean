/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
import WeilConjectures.AlgebraicGeometry.Morphisms.NormalIntegralGenericHomFull
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.Mathlib.CategoryTheory.Extensive

/-! # Splitting the section pullback of a finite étale generic model

## References

* Stacks Project, Tag 0EYJ, section fibre calculation
* Stacks Project, Tag 0EYJ, the section fibre calculation
* Tag 0BQM, full faithfulness
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Pulling back the torsor identity along a point trivializes its fibre. -/
private theorem torsor_split {T K : Scheme.{u}}
    (G : Type (u + 1)) [Group G] [Finite G] (Z : GaloisCover G T) (z : K ⟶ Z.P) :
    ∃ e : (∐ fun _ : G ↦ K) ≅ pullback Z.π (z ≫ Z.π),
      e.hom ≫ pullback.snd Z.π (z ≫ Z.π) = Sigma.desc (fun _ : G ↦ 𝟙 K) := by
  let D := Sigma.desc fun g : G ↦
    pullback.lift (f := Z.π) (g := Z.π) (𝟙 Z.P) (Z.smul g) (by simp [Z.smul_π])
  have hD : D = (Sigma.desc fun g : G ↦
      pullback.lift (f := Z.π) (g := Z.π) (Z.smul g) (𝟙 Z.P)
        (by simp [Z.smul_π])) ≫ (pullbackSymmetry Z.π Z.π).hom := by
    apply Sigma.hom_ext
    intro g
    apply pullback.hom_ext <;> simp [D]
  have : IsIso D := by
    rw [hD]
    have := Z.isIso_sigmaDesc
    infer_instance
  have := FinitaryPreExtensive.isIso_sigmaDesc_lift_comp Z.π Z.smul Z.smul_π z
  let F := Sigma.desc fun g : G ↦
    pullback.lift (f := z ≫ Z.π) (g := Z.π) (𝟙 K) (z ≫ Z.smul g)
      (by simp [Z.smul_π])
  refine ⟨asIso F ≪≫ pullbackSymmetry (z ≫ Z.π) Z.π, ?_⟩
  apply Sigma.hom_ext
  intro g
  simp [F]

/-- Finite coproducts are universal, so constant covers commute with base change. -/
private theorem constant_cover_generic {B K : Scheme.{u}}
    (G : Type (u + 1)) [Finite G] (a : K ⟶ B) :
    ∃ e : (∐ fun _ : G ↦ K) ≅ pullback (Sigma.desc (fun _ : G ↦ 𝟙 B)) a,
      e.hom ≫ pullback.snd (Sigma.desc (fun _ : G ↦ 𝟙 B)) a =
        Sigma.desc (fun _ : G ↦ 𝟙 K) := by
  let v := Sigma.desc fun g : G ↦ a ≫ Sigma.ι (fun _ : G ↦ B) g
  have H : IsPullback v (Sigma.desc (fun _ : G ↦ 𝟙 K))
      (Sigma.desc (fun _ : G ↦ 𝟙 B)) a := by
    have hu := FinitaryPreExtensive.isUniversal_finiteCoproducts
      (coproductIsCoproduct (fun _ : G ↦ B))
    have hs := hu.isPullback_of_isColimit_left (fun _ : G ↦ 𝟙 B)
      (Sigma.desc (fun _ : G ↦ 𝟙 B)) a (fun _ : G ↦ 𝟙 K)
      (fun _ : G ↦ a) (fun _ ↦ IsPullback.of_id_fst (f := a))
      (coproductIsCoproduct (fun _ : G ↦ K))
    simpa [Cofan.IsColimit.desc, coproductIsCoproduct, v] using hs.flip
  exact ⟨H.isoPullback, H.isoPullback_hom_snd⟩

/-- The section cover has split generic fibre, without asserting any extension over U. -/
private theorem section_cover_generic_fibre_split {S C : Scheme.{u}}
    [IsIntegral S]
    (c : C ⟶ S)
    (σ : S ⟶ C) (_hσ : σ ≫ c = 𝟙 S)
    (G : Type (u + 1)) [Group G] [Finite G]
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (_hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    (sη : Spec S.functionField ⟶ Cη) (_hsq : sη ≫ q = 𝟙 _)
    (hsj : sη ≫ j = S.fromSpecStalk (genericPoint S) ≫ σ)
    (Z : GaloisCover G Cη) (hZ : ∃ z : Spec S.functionField ⟶ Z.P, z ≫ Z.π = sη)
    (U : S.Opens) (hηU : genericPoint S ∈ U)
    (jU : Cη ⟶ (c ⁻¹ᵁ U).toScheme) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (ψ : Z.P ⟶ PA.obj.left) (hjU : jU ≫ (c ⁻¹ᵁ U).ι = j)
    (hψ : IsPullback ψ Z.π PA.obj.hom jU)
    (b : U.toScheme ⟶ (c ⁻¹ᵁ U).toScheme)
    (hb : b ≫ (c ⁻¹ᵁ U).ι = U.ι ≫ σ) :
    letI : Nonempty U := ⟨⟨genericPoint S, hηU⟩⟩
    let a := U.toScheme.fromSpecStalk (genericPoint U.toScheme)
    let πX := Sigma.desc (fun _ : G ↦ 𝟙 U.toScheme)
    let πY := pullback.snd PA.obj.hom b
    ∃ e : pullback πX a ≅ pullback πY a,
      e.hom ≫ pullback.snd πY a = pullback.snd πX a := by
  have : Nonempty U := ⟨⟨genericPoint S, hηU⟩⟩
  dsimp only
  have hx : (⟨genericPoint S, hηU⟩ : U) = genericPoint U.toScheme := by
    apply Subtype.ext
    exact (genericPoint_eq_of_isOpenImmersion U.ι).symm
  rw [← hx]
  let x : U := ⟨genericPoint S, hηU⟩
  let a := U.toScheme.fromSpecStalk x
  let k : Spec (U.toScheme.presheaf.stalk x) ⟶ Spec S.functionField :=
    Spec.map (U.ι.stalkMap x)
  have hk : k ≫ S.fromSpecStalk (genericPoint S) = a ≫ U.ι :=
    SpecMap_stalkMap_fromSpecStalk U.ι
  obtain ⟨z, hz⟩ := hZ
  let r := k ≫ z
  have hr : (r ≫ Z.π) ≫ jU = a ≫ b := by
    apply (cancel_mono (c ⁻¹ᵁ U).ι).mp
    simp only [Category.assoc, hjU, r]
    rw [← Category.assoc z, hz, hsj, ← Category.assoc k, hk]
    simp only [Category.assoc, hb]
  obtain ⟨eZ, heZ⟩ := torsor_split G Z r
  obtain ⟨eX, heX⟩ := constant_cover_generic G a
  let H := (IsPullback.of_hasPullback Z.π (r ≫ Z.π)).paste_horiz hψ
  have H' : IsPullback
      (pullback.fst Z.π (r ≫ Z.π) ≫ ψ)
      (pullback.snd Z.π (r ≫ Z.π)) PA.obj.hom (a ≫ b) := by
    simpa only [hr] using H
  let Hη := (IsPullback.of_hasPullback (pullback.snd PA.obj.hom b) a).paste_horiz
    (IsPullback.of_hasPullback PA.obj.hom b)
  let eY := H'.isoIsPullback _ _ Hη
  refine ⟨eX.symm ≪≫ eZ ≪≫ eY, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [H'.isoIsPullback_hom_snd, heZ]
  rw [← heX, Iso.inv_hom_id_assoc]

/-- Extend both directions and use generic full faithfulness to check the inverse identities. -/
private theorem generic_iso_extends {B : Scheme.{u}} [IsIntegral B]
    (hB : ∀ x : B, IsIntegrallyClosed (B.presheaf.stalk x))
    {X Y : Scheme.{u}} (πX : X ⟶ B) (πY : Y ⟶ B)
    [IsFinite πX] [Etale πX] [IsFinite πY] [Etale πY]
    (eη : pullback πX (B.fromSpecStalk (genericPoint B)) ≅
      pullback πY (B.fromSpecStalk (genericPoint B)))
    (heη : eη.hom ≫ pullback.snd πY (B.fromSpecStalk (genericPoint B)) =
      pullback.snd πX (B.fromSpecStalk (genericPoint B))) :
    ∃ e : X ≅ Y, e.hom ≫ πY = πX := by
  let a := B.fromSpecStalk (genericPoint B)
  let ψX := pullback.fst πX a
  let ψY := pullback.fst πY a
  let πXη := pullback.snd πX a
  let πYη := pullback.snd πY a
  have hX := IsPullback.of_hasPullback πX a
  have hY := IsPullback.of_hasPullback πY a
  obtain ⟨f, hf, _⟩ := finiteEtale_normalIntegral_generic_hom_full hB
    πX πY πXη πYη ψX ψY hX hY eη.hom heη
  have hbη : eη.inv ≫ πXη = πYη := by
    change eη.inv ≫ pullback.snd πX (B.fromSpecStalk (genericPoint B)) =
      pullback.snd πY (B.fromSpecStalk (genericPoint B))
    rw [← heη, eη.inv_hom_id_assoc]
  obtain ⟨g, hg, _⟩ := finiteEtale_normalIntegral_generic_hom_full hB
    πY πX πYη πXη ψY ψX hY hX eη.inv hbη
  have hfg : f ≫ g = 𝟙 X := by
    have hx := finiteEtale_normalIntegral_generic_hom_full hB
      πX πX πXη πXη ψX ψX hX hX (𝟙 _) (by simp)
    apply hx.unique
    · constructor
      · simp [hf.1, hg.1]
      · calc
          ψX ≫ (f ≫ g) = eη.hom ≫ (ψY ≫ g) := by
            rw [← Category.assoc, hf.2, Category.assoc]
          _ = (eη.hom ≫ eη.inv) ≫ ψX := by rw [hg.2, Category.assoc]
          _ = 𝟙 _ ≫ ψX := by simp
    · simp
  have hgf : g ≫ f = 𝟙 Y := by
    have hy := finiteEtale_normalIntegral_generic_hom_full hB
      πY πY πYη πYη ψY ψY hY hY (𝟙 _) (by simp)
    apply hy.unique
    · constructor
      · simp [hf.1, hg.1]
      · calc
          ψY ≫ (g ≫ f) = eη.inv ≫ (ψX ≫ f) := by
            rw [← Category.assoc, hg.2, Category.assoc]
          _ = (eη.inv ≫ eη.hom) ≫ ψY := by rw [hf.2, Category.assoc]
          _ = 𝟙 _ ≫ ψY := by simp
    · simp
  exact ⟨⟨f, g, hfg, hgf⟩, hf.1⟩

/-- A finite étale model of a generic torsor splits after pullback to the section on U. -/
theorem GaloisCover.section_finiteEtale_generic_split {S C : Scheme.{u}}
    [IsIntegral S] (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S)
    (σ : S ⟶ C) (hσ : σ ≫ c = 𝟙 S)
    (G : Type (u + 1)) [Group G] [Finite G]
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    (sη : Spec S.functionField ⟶ Cη) (hsq : sη ≫ q = 𝟙 _)
    (hsj : sη ≫ j = S.fromSpecStalk (genericPoint S) ≫ σ)
    (Z : GaloisCover G Cη) (hZ : ∃ z : Spec S.functionField ⟶ Z.P, z ≫ Z.π = sη)
    (U : S.Opens) (hηU : genericPoint S ∈ U)
    (jU : Cη ⟶ (c ⁻¹ᵁ U).toScheme) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (ψ : Z.P ⟶ PA.obj.left) (hjU : jU ≫ (c ⁻¹ᵁ U).ι = j)
    (hψ : IsPullback ψ Z.π PA.obj.hom jU)
    (b : U.toScheme ⟶ (c ⁻¹ᵁ U).toScheme)
    (hb : b ≫ (c ⁻¹ᵁ U).ι = U.ι ≫ σ) :
    ∃ e : (∐ fun _ : G ↦ U.toScheme) ≅ pullback PA.obj.hom b,
      e.hom ≫ pullback.snd PA.obj.hom b = Sigma.desc (fun _ : G ↦ 𝟙 U.toScheme) := by
  have : Nonempty U := ⟨⟨genericPoint S, hηU⟩⟩
  have hU : ∀ x : U.toScheme, IsIntegrallyClosed (U.toScheme.presheaf.stalk x) := by
    intro x
    have := hS (U.ι x)
    exact IsIntegrallyClosed.of_equiv (asIso (U.ι.stalkMap x)).commRingCatIsoToRingEquiv
  have : IsFinite PA.obj.hom := PA.property
  let πX := Sigma.desc (fun _ : G ↦ 𝟙 U.toScheme)
  let πY := pullback.snd PA.obj.hom b
  have : IsFinite πX := inferInstance
  have : Etale πX := IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
  obtain ⟨eη, heη⟩ := section_cover_generic_fibre_split c σ hσ G
    q j hCη sη hsq hsj Z hZ U hηU jU PA ψ hjU hψ b hb
  exact generic_iso_extends hU πX πY eη heη

end AlgebraicGeometry.Scheme
