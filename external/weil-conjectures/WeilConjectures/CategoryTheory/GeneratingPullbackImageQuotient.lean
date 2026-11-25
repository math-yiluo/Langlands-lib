/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom
import all WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import all WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackUnitExistence

/-! # Epic quotient onto the structural image ideal

Source: Stacks Project, algebraization.tex, Tags 099E and 0A0G, finite generating covers.
(blueprint: lem-weil-pbc-ringed-image-ideal-quotient).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

private noncomputable abbrev underlyingModules
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) :=
  SheafOfModules.toSheaf R ⋙ sheafCompose J (forget AddCommGrpCat)

private theorem linear_lift
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N Q : SheafOfModules.{u} R}
    (j : N ⟶ Q) [Mono j] (a : M ⟶ Q)
    (k : (underlyingModules R).obj M ⟶ (underlyingModules R).obj N)
    (hk : k ≫ (underlyingModules R).map j = (underlyingModules R).map a) :
    ∃ b : M ⟶ N, b ≫ j = a := by
  have hj (W : Cᵒᵖ) : Function.Injective (j.val.app W) := by
    exact (ModuleCat.mono_iff_injective ((SheafOfModules.evaluation R W).map j)).mp
      inferInstance
  have he (W : Cᵒᵖ) (m : M.val.obj W) :
      j.val.app W (k.hom.app W m) = a.val.app W m :=
    congrArg (fun f ↦ f.hom.app W m) hk
  let b : M ⟶ N := ⟨{
    app := fun W ↦ ModuleCat.ofHom {
      toFun := k.hom.app W
      map_add' := fun x y ↦ hj W (by simp only [map_add, he])
      map_smul' := fun r x ↦ hj W (by simp only [map_smul, RingHom.id_apply, he]) }
    naturality := by
      intro W V f
      ext x
      exact CategoryTheory.congr_fun (k.hom.naturality f) x }⟩
  refine ⟨b, ?_⟩
  ext W x
  exact he W x

private theorem ideal_unit_endomorphism
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (j : M ⟶ SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (δ : End (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) :
    ∃ a : M ⟶ M, a ≫ j = j ≫ (δ).asHom := by
  let s := (SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).unitHomEquiv (δ).asHom
  let a : M ⟶ M := ⟨PresheafOfModules.sectionsSMul M.val ⟨s.val, s.property⟩⟩
  refine ⟨a, ?_⟩
  ext W x
  let : CommRing ((SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).val.obj W) :=
    inferInstanceAs (CommRing (R.obj.obj W))
  change j.val.app W ((show R.obj.obj W from s.val W) • x) = δ.asHom.val.app W (j.val.app W x)
  rw [map_smul]
  change (δ.asHom.val.app W (1 : R.obj.obj W) : R.obj.obj W) *
    (j.val.app W x : R.obj.obj W) = (δ.asHom.val.app W (j.val.app W x) : R.obj.obj W)
  rw [mul_comm]
  simpa only [RingHom.id_apply, smul_eq_mul, mul_one] using
    ((δ.asHom.val.app W).hom.map_smul (j.val.app W x) (1 : R.obj.obj W)).symm

/-- The least structural-image ideal is an epic quotient of any specified module pullback.
Source: Stacks Project, Modules on Sites, Tags 03D7 and 04IE; Algebraization, Tag 0A0G.
(blueprint: lem-weil-pbc-ringed-image-ideal-quotient).

Proof: present the inverse image algebraically and use tensor adjunction. A factorization
of the underlying structural map through a monic ideal is linear by cancellation of that
monomorphism; its adjoint factors the tensor pullback map. Thus its image and IX have
the same least-ideal property, and the induced map onto IX is epic. The tensor unit
comparison identifies this map with the pullback of the inclusion. Uniqueness of left
adjoints transports it to G. Changing the rank-one comparison to u multiplies by a
unit global section of RX; multiplication by that unit acts invertibly on every ideal.
Composing with this automorphism gives the required quotient and commuting square. -/
theorem exists_ringed_image_ideal_quotient
    {C X : Type u} [SmallCategory C] [SmallCategory X]
    {J : GrothendieckTopology C} {K : GrothendieckTopology X}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (RY : Sheaf J CommRingCat.{u}) (RX : Sheaf K CommRingCat.{u})
    (f : RingedToposMorphism
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
    (IY : ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
    (ιY : IY ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
    [Mono ιY]
    (IX : ringedSiteModules.{u, u, u, u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
    (ιX : IX ⟶ SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
    [Mono ιX]
    (hImage : ∀ (N : ringedSiteModules.{u, u, u, u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
      (j : N ⟶ SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)),
      Mono j →
      ((∃ k : f.inverse.obj ((SheafOfModules.toSheaf
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY) ⋙
          sheafCompose J (forget AddCommGrpCat)).obj IY) ⟶
          (SheafOfModules.toSheaf ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX) ⋙
            sheafCompose K (forget AddCommGrpCat)).obj N,
        (k ≫ (SheafOfModules.toSheaf ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX) ⋙
            sheafCompose K (forget AddCommGrpCat)).map j : _ ⟶ (sheafCompose K (forget RingCat)).obj
              ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)) =
          (f.inverse.map ((SheafOfModules.toSheaf
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY) ⋙
            sheafCompose J (forget AddCommGrpCat)).map ιY) : _ ⟶ f.inverse.obj
              ((sheafCompose J (forget RingCat)).obj
                ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))) ≫ f.ringMap) ↔
      ∃ a : IX ⟶ N, a ≫ j = ιX))
    (G : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY) ⥤
      ringedSiteModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
    (hG : G ⊣ f.modules)
    (u : G.obj (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)) ≅
      SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)) :
    ∃ e : G.obj IY ⟶ IX, Epi e ∧ e ≫ ιX = G.map ιY ≫ u.hom := by
  classical
  let _ := f.leftExact
  obtain ⟨RI, ⟨I⟩⟩ := algebraic_image J K
    f.inverse f.direct f.adj RY
  obtain ⟨c, hc⟩ := structural_map K J RX RY f RI I
  have hc' : I.ringUnderlying.hom ≫
      (sheafCompose K (forget CommRingCat)).map c = f.ringMap := by
    rw [hc, Iso.hom_inv_id_assoc]
  obtain ⟨eI, heI⟩ := SheafOfModules.inverseImage_unit_iso RY RI f.inverse I
  let A := (sheafCompose K (forget₂ CommRingCat RingCat)).obj RI
  let B := (sheafCompose K (forget₂ CommRingCat RingCat)).obj RX
  let U := underlyingModules A
  let V := underlyingModules B
  let T := SheafOfModules.tensorFunctor c
  let S := SheafOfModules.restrictScalars
    ((sheafCompose K (forget₂ CommRingCat RingCat)).map c)
  let adj := SheafOfModules.tensorAdjunction c
  let _ : PreservesLimits S := adj.rightAdjoint_preservesLimits
  let q : SheafOfModules.unit A ⟶ S.obj (SheafOfModules.unit B) := ⟨{
    app := fun W ↦ ModuleCat.ofHom
      (X := (SheafOfModules.unit A).val.obj W)
      (Y := (S.obj (SheafOfModules.unit B)).val.obj W) {
      toFun := c.hom.app W
      map_add' := map_add (c.hom.app W).hom
      map_smul' := fun r x ↦ (c.hom.app W).hom.map_mul r x }
    naturality := by
      intro W V a
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact CategoryTheory.congr_fun (c.hom.naturality a) x }⟩
  let d := I.modules.map ιY ≫ eI.inv ≫ q
  let α := (adj.homEquiv _ _).symm d
  have heI' : U.map eI.inv = I.moduleUnderlying.hom.app _ ≫ I.ringUnderlying.hom := by
    apply (cancel_epi (U.map eI.hom)).mp
    rw [← U.map_comp, Iso.hom_inv_id, U.map_id, heI]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id]
  have hd : U.map d = I.moduleUnderlying.hom.app IY ≫
      f.inverse.map ((underlyingModules
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)).map ιY) ≫ f.ringMap := by
    dsimp only [d]
    rw [U.map_comp, U.map_comp, heI']
    have hn := I.moduleUnderlying.hom.naturality ιY
    change U.map (I.modules.map ιY) ≫ I.moduleUnderlying.hom.app _ =
      I.moduleUnderlying.hom.app IY ≫ f.inverse.map
        ((underlyingModules
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)).map ιY) at hn
    change U.map (I.modules.map ιY) ≫
      (I.moduleUnderlying.hom.app _ ≫ I.ringUnderlying.hom) ≫
        (sheafCompose K (forget CommRingCat)).map c = _
    rw [Category.assoc, ← Category.assoc (U.map (I.modules.map ιY)), hn]
    simp only [Category.assoc, hc']
  have hα : U.map d = SheafOfModules.tensorUnit c (I.modules.obj IY) ≫ V.map α := by
    rw [← SheafOfModules.tensorAdjunction_underlying]
    exact congrArg (fun a ↦ U.map a) ((adj.homEquiv _ _).apply_symm_apply d).symm
  have hfac (N : SheafOfModules.{u} B) (j : N ⟶ SheafOfModules.unit B) [Mono j] :
      (∃ k : f.inverse.obj ((underlyingModules
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)).obj IY) ⟶ V.obj N,
        k ≫ V.map j =
          f.inverse.map ((underlyingModules
            ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)).map ιY) ≫
              f.ringMap) ↔ ∃ b : T.obj (I.modules.obj IY) ⟶ N, b ≫ j = α := by
    constructor
    · rintro ⟨k, hk⟩
      obtain ⟨b, hb⟩ := linear_lift (S.map j) d
        (I.moduleUnderlying.hom.app IY ≫ k) (by
          change (I.moduleUnderlying.hom.app IY ≫ k) ≫ V.map j = U.map d
          rw [Category.assoc, hk, hd])
      refine ⟨(adj.homEquiv _ _).symm b, ?_⟩
      apply (adj.homEquiv _ _).injective
      rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply]
      exact hb
    · rintro ⟨b, hb⟩
      refine ⟨I.moduleUnderlying.inv.app IY ≫
        SheafOfModules.tensorUnit c (I.modules.obj IY) ≫ V.map b, ?_⟩
      simp only [Category.assoc, ← V.map_comp, hb]
      rw [← hα, hd]
      simp only [Iso.inv_hom_id_app_assoc]
  obtain ⟨b, hb⟩ := (hfac IX ιX).mp
    ((hImage IX ιX inferInstance).mpr ⟨𝟙 IX, Category.id_comp _⟩)
  obtain ⟨a, ha⟩ := (hImage (image α) (image.ι α) inferInstance).mp
    ((hfac (image α) (image.ι α)).mpr ⟨factorThruImage α, image.fac α⟩)
  let mf : MonoFactorisation α := { I := IX, m := ιX, e := b, fac := hb }
  let v := image.lift mf
  have hv : v ≫ ιX = image.ι α := image.lift_fac mf
  have hav : a ≫ v = 𝟙 IX := by
    apply (cancel_mono ιX).mp
    rw [Category.assoc, hv, ha, Category.id_comp]
  have : Epi v := epi_of_epi_fac hav
  have : Epi b := by
    have h : factorThruImage α ≫ v = b := image.fac_lift mf
    rw [← h]
    infer_instance
  obtain ⟨eS, heS⟩ := SheafOfModules.scalarExtension_unit_iso RX RI c
  have hq : (adj.homEquiv _ _ eS.hom) = q := by
    apply (underlyingModules A).map_injective
    rw [SheafOfModules.tensorAdjunction_underlying]
    ext W x
    exact heS W x
  let H := I.modules ⋙ T
  let v0 : H.obj (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)) ≅
      SheafOfModules.unit B := T.mapIso eI.symm ≪≫ eS
  have hcanonical : α = H.map ιY ≫ v0.hom := by
    apply (adj.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    dsimp only [v0, H, Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom,
      Iso.symm_hom]
    rw [← Category.assoc, ← T.map_comp, adj.homEquiv_naturality_left, hq]
    simp only [d, Category.assoc]
  obtain ⟨adjH⟩ := supplied_adjunction f RI I c hc
  let ε : H ≅ G := Adjunction.leftAdjointUniq adjH hG
  let vG : G.obj (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)) ≅
      SheafOfModules.unit B := (ε.app _).symm ≪≫ v0
  let e0 : G.obj IY ⟶ IX := ε.inv.app IY ≫ b
  have he0 : e0 ≫ ιX = G.map ιY ≫ vG.hom := by
    dsimp only [e0, vG, Iso.trans_hom, Iso.symm_hom, Iso.app_inv]
    rw [Category.assoc, hb, hcanonical, ← Category.assoc,
      ← ε.inv.naturality ιY, Category.assoc]
  let δ : SheafOfModules.unit B ≅ SheafOfModules.unit B := vG.symm ≪≫ u
  obtain ⟨a, ha⟩ := ideal_unit_endomorphism RX IX ιX (.of δ.hom)
  obtain ⟨a', ha'⟩ := ideal_unit_endomorphism RX IX ιX (.of δ.inv)
  have haa : a' ≫ a = 𝟙 IX := by
    apply (cancel_mono ιX).mp
    rw [Category.assoc, ha, ← Category.assoc, ha', Category.assoc,
      Iso.inv_hom_id, Category.comp_id, Category.id_comp]
  have : Epi e0 := by dsimp only [e0]; infer_instance
  have : Epi a := epi_of_epi_fac haa
  refine ⟨e0 ≫ a, inferInstance, ?_⟩
  rw [Category.assoc, ha, ← Category.assoc, he0, Category.assoc]
  simp only [δ, Iso.trans_hom, Iso.symm_hom, ← Category.assoc,
    Iso.hom_inv_id, Category.id_comp]

end CategoryTheory
