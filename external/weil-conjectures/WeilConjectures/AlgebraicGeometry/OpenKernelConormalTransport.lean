/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.TensorPullback

/-! # Localizing the actual kernel conormal

Source: Stacks Project, Tags 01R3 (1), 00A0 and 0096.
(blueprint: lem-sc-open-kernel-conormal-transport).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem range_kernelIdeal {A B : Scheme.{u}} (i : A ⟶ B)
    [IsClosedImmersion i] (U : B.Opens) :
    Set.range (i.ker.toModulesι.app U) = {x | i.app U x = 0} := by
  rw [Scheme.IdealSheafData.range_toModulesι_app_eq]
  ext x
  change i.imageι.app U x = 0 ↔ i.app U x = 0
  have hi := Scheme.Hom.congr_app i.toImage_imageι U
  rw [Scheme.Hom.comp_app] at hi
  have hcomp : (i.imageι.app U ≫ i.toImage.app (i.imageι ⁻¹ᵁ U)) x = 0 ↔
      i.app U x = 0 := by
    rw [hi]
    have heq {V W : A.Opens} (he : V = W) (y : Γ(A, W)) :
        A.presheaf.map (eqToHom he).op y = 0 ↔ y = 0 :=
      map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
        (A.presheaf.map (eqToHom he).op)).1
    exact heq _ _
  exact (map_eq_zero_iff _
    (ConcreteCategory.bijective_of_isIso (i.toImage.app (i.imageι ⁻¹ᵁ U))).1).symm.trans
      hcomp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem open_kernel_zero_iff
    {Z Z' : Scheme.{u}} (i : Z ⟶ Z')
    {V : Z.Opens} {V' : Z'.Opens} (iV : V.toScheme ⟶ V'.toScheme)
    (hpre : i ⁻¹ᵁ V' = V) (hcomm : iV ≫ V'.ι = V.ι ≫ i)
    (W : V'.toScheme.Opens) (x : Γ(Z', V'.ι ''ᵁ W)) :
    iV.app W ((V'.ι.appIso W).hom x) = 0 ↔ i.app (V'.ι ''ᵁ W) x = 0 := by
  have hle : i ⁻¹ᵁ (V'.ι ''ᵁ W) ≤ V.ι.opensRange := by
    rw [Scheme.Opens.opensRange_ι, ← hpre]
    apply i.preimage_mono
    rintro x ⟨y, hy, rfl⟩
    exact y.property
  have : IsIso (V.ι.app (i ⁻¹ᵁ (V'.ι ''ᵁ W))) := V.ι.isIso_app _ hle
  rw [IsOpenImmersion.app_eq_appIso_inv_app_of_comp_eq iV V'.ι
    (V.ι ≫ i) hcomm.symm W]
  simp only [CommRingCat.comp_apply, Iso.hom_inv_id_apply]
  rw [map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso _).1]
  rw [Scheme.Hom.comp_app]
  simp only [CommRingCat.comp_apply]
  rw [map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso _).1]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem actual_kernel_restrict_iso {X Y : Scheme.{u}} (g : X ⟶ Y)
    (W : Y.Opens) (U : X.Opens) (h : U ≤ g ⁻¹ᵁ W) (hpre : g ⁻¹ᵁ W = U)
    [IsClosedImmersion (g.resLE W U h)] :
    let i := g.resLE W U h
    let K := kernel (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom)
    ∃ δ : (restrictFunctor W.ι).obj K ≅ i.ker.toModules,
      δ.hom ≫ i.ker.toModulesι =
        (restrictFunctor W.ι).map (kernel.ι
          (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom)) ≫
            (restrictUnitIso W.ι).hom := by
  classical
  let i := g.resLE W U h
  let f := SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom
  let K := kernel f
  let M := (restrictFunctor W.ι).obj K
  let α : M ⟶ SheafOfModules.unit W.toScheme.ringCatSheaf :=
    (restrictFunctor W.ι).map (kernel.ι f) ≫ (restrictUnitIso W.ι).hom
  have hα (T : W.toScheme.Opens) (s : Γ(M, T)) :
      α.app T s = (W.ι.appIso T).hom
        ((kernel.ι f).val.app (op (W.ι ''ᵁ T)) s) := rfl
  have hk (T : Y.Opens) :
      Set.range ((kernel.ι f).val.app (op T)) = {x | g.app T x = 0} :=
    range_map_kernelι T f
  have hzero : α ≫ i.ker.toPushforwardSubscheme = 0 := by
    apply hom_ext
    intro T
    ext s
    change i.ker.subschemeι.app T (α.app T s) = 0
    have hs : g.app (W.ι ''ᵁ T) ((kernel.ι f).val.app (op (W.ι ''ᵁ T)) s) = 0 := by
      have hm : (kernel.ι f).val.app (op (W.ι ''ᵁ T)) s ∈
          Set.range ((kernel.ι f).val.app (op (W.ι ''ᵁ T))) := ⟨s, rfl⟩
      rwa [hk] at hm
    have hm : α.app T s ∈ Set.range (i.ker.toModulesι.app T) := by
      rw [range_kernelIdeal]
      change i.app T (α.app T s) = 0
      rw [hα]
      exact (open_kernel_zero_iff g i hpre (g.resLE_comp_ι h) T _).mpr hs
    rwa [Scheme.IdealSheafData.range_toModulesι_app_eq] at hm
  let δ : M ⟶ i.ker.toModules := kernel.lift _ α hzero
  have hδ : δ ≫ i.ker.toModulesι = α := kernel.lift_ι _ _ _
  have hδapp (T : W.toScheme.Opens) (s : Γ(M, T)) :
      i.ker.toModulesι.app T (δ.app T s) = α.app T s :=
    congrArg (fun f ↦ f.app T s) hδ
  have : IsIso δ := by
    rw [Hom.isIso_iff_isIso_app]
    intro T
    rw [ConcreteCategory.isIso_iff_bijective]
    constructor
    · intro s t he
      have hinj : Function.Injective ((kernel.ι f).val.app (op (W.ι ''ᵁ T))) :=
        injective_map_kernelι (W.ι ''ᵁ T) f
      apply hinj
      apply (ConcreteCategory.bijective_of_isIso (W.ι.appIso T).hom).1
      rw [← hα T s, ← hα T t, ← hδapp T s, ← hδapp T t, he]
    · intro t
      let x := (W.ι.appIso T).inv (i.ker.toModulesι.app T t)
      have hx : g.app (W.ι ''ᵁ T) x = 0 := by
        apply (open_kernel_zero_iff g i hpre (g.resLE_comp_ι h) T x).mp
        simp only [x, Iso.inv_hom_id_apply]
        have hm : i.ker.toModulesι.app T t ∈ Set.range (i.ker.toModulesι.app T) :=
          ⟨t, rfl⟩
        rwa [range_kernelIdeal] at hm
      have hm : x ∈ Set.range ((kernel.ι f).val.app (op (W.ι ''ᵁ T))) := by
        rwa [hk]
      obtain ⟨s, hs⟩ := hm
      refine ⟨s, ?_⟩
      apply i.ker.injective_toModulesι_app T
      rw [hδapp, hα, hs]
      exact Iso.inv_hom_id_apply _ _
  exact ⟨asIso δ, hδ⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The unit calculation elaborates several nested restriction and pushforward functors.
private theorem open_pullback_sections_transport {X Y : Scheme.{u}} (g : X ⟶ Y)
    (W : Y.Opens) (U : X.Opens) (h : U ≤ g ⁻¹ᵁ W) (hpre : g ⁻¹ᵁ W = U)
    (M : Y.Modules) :
    let i := g.resLE W U h
    let L := (restrictFunctor W.ι).obj M
    let N := (tensorPullback g).obj M
    let C := (pushforward i).obj ((tensorPullback i).obj L)
    let : Module Γ(W.toScheme, ⊤) Γ(N, U) :=
      Module.compHom _ ((g.appLE W U h).hom.comp W.topIso.hom.hom)
    ∃ e : Γ(C, ⊤) ≃ₗ[Γ(W.toScheme, ⊤)] Γ(N, U),
      ∀ s : Γ(M, W),
        e (((Classical.choose (exists_tensorPullbackAdjunction i)).unit.app L).app ⊤
          (M.presheaf.map (eqToHom W.ι_image_top).op s)) =
        N.presheaf.map (homOfLE h).op
          (((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app M).app W s) := by
  classical
  let i := g.resLE W U h
  let ai := Classical.choose (exists_tensorPullbackAdjunction i)
  let ag := Classical.choose (exists_tensorPullbackAdjunction g)
  let a₁ := (restrictAdjunction W.ι).comp ai
  let a₂ := ag.comp (restrictAdjunction U.ι)
  let ρ : pushforward U.ι ⋙ pushforward g ≅ pushforward i ⋙ pushforward W.ι :=
    pushforwardComp U.ι g ≪≫ (pushforwardCongr (g.resLE_comp_ι h).symm) ≪≫
      (pushforwardComp i W.ι).symm
  let β := a₁.leftAdjointUniq (a₂.ofNatIsoRight ρ)
  let N := (tensorPullback g).obj M
  let L := (restrictFunctor W.ι).obj M
  let C := (pushforward i).obj ((tensorPullback i).obj L)
  let E : Γ(C, ⊤) ≅ Γ(N, U) :=
    ((CategoryTheory.evaluation _ AddCommGrpCat).obj (op ⊤)).mapIso
      ((toPresheaf U.toScheme).mapIso (β.app M)) ≪≫
        N.presheaf.mapIso (eqToIso U.ι_image_top.symm).op
  let : Module Γ(W.toScheme, ⊤) Γ(N, U) :=
    Module.compHom _ ((g.appLE W U h).hom.comp W.topIso.hom.hom)
  have hlinear (r : Γ(W.toScheme, ⊤)) (x : Γ(C, ⊤)) :
      E.hom (r • x) = r • E.hom x := by
    change N.presheaf.map (eqToHom U.ι_image_top.symm).op
      ((β.hom.app M).app ⊤ ((show Γ(U.toScheme, ⊤) from i.app ⊤ r) •
        (show Γ((tensorPullback i).obj L, ⊤) from x))) = _
    rw [Hom.app_smul]
    change N.presheaf.map (eqToHom U.ι_image_top.symm).op
      ((show Γ(U.toScheme, ⊤) from i.app ⊤ r) • ((β.hom.app M).app ⊤ x)) = _
    erw [N.map_smul]
    congr 1
    change X.presheaf.map (eqToHom U.ι_image_top.symm).op
      ((U.ι.appIso ⊤).inv (i.app ⊤ r)) = g.appLE W U h (W.topIso.hom r)
    simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
    change U.topIso.hom (i.app ⊤ r) = g.appLE W U h (W.topIso.hom r)
    dsimp only [i]
    simp only [Scheme.Hom.resLE_app_top, CommRingCat.comp_apply]
    exact ConcreteCategory.congr_hom U.topIso.inv_hom_id _
  let e : Γ(C, ⊤) ≃ₗ[Γ(W.toScheme, ⊤)] Γ(N, U) :=
    { E.addCommGroupIsoToAddEquiv with map_smul' := hlinear }
  refine ⟨e, ?_⟩
  intro s
  have hu := Adjunction.unit_leftAdjointUniq_hom_app a₁ (a₂.ofNatIsoRight ρ) M
  have hs := congrArg (fun f ↦ f.app W s) hu
  dsimp only [a₁, a₂, ρ] at hs
  simp only [Adjunction.comp_unit_app, Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Hom.comp_app, Functor.comp_map,
    pushforward_map_app,
    restrictAdjunction_unit_app_app, Iso.trans_hom, pushforwardComp_hom_app_app,
    pushforwardCongr_hom_app_app] at hs
  simp only [Iso.symm_hom, pushforwardComp_inv_app_app,
    ConcreteCategory.comp_apply] at hs
  have hU : U.ι ⁻¹ᵁ (g ⁻¹ᵁ W) = ⊤ := by rw [hpre, U.ι_preimage_self]
  change (β.hom.app M).app (i ⁻¹ᵁ (W.ι ⁻¹ᵁ W))
    ((ai.unit.app L).app (W.ι ⁻¹ᵁ W)
      (M.presheaf.map (homOfLE (W.ι.image_preimage_le W)).op s)) =
    N.presheaf.map (homOfLE (show U.ι ''ᵁ (i ⁻¹ᵁ (W.ι ⁻¹ᵁ W)) ≤
      U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ⁻¹ᵁ W)) from by
        rw [W.ι_preimage_self, i.preimage_top, hU])).op
      (N.presheaf.map (homOfLE (U.ι.image_preimage_le (g ⁻¹ᵁ W))).op
        ((ag.unit.app M).app W s)) at hs
  let v : (⊤ : W.toScheme.Opens) ⟶ W.ι ⁻¹ᵁ W := eqToHom W.ι_preimage_self.symm
  let q : (⊤ : U.toScheme.Opens) ⟶ i ⁻¹ᵁ (W.ι ⁻¹ᵁ W) :=
    (TopologicalSpace.Opens.map i.base).map v
  have hn := congrArg (fun f ↦ f
    ((ai.unit.app L).app (W.ι ⁻¹ᵁ W)
      (M.presheaf.map (homOfLE (W.ι.image_preimage_le W)).op s)))
    ((β.hom.app M).mapPresheaf.naturality q.op)
  simp only [mapPresheaf_app, ConcreteCategory.comp_apply] at hn
  have hv := congrArg (fun f ↦ f
    (M.presheaf.map (homOfLE (W.ι.image_preimage_le W)).op s))
    ((ai.unit.app L).mapPresheaf.naturality v.op)
  simp only [mapPresheaf_app, ConcreteCategory.comp_apply] at hv
  have hinput : L.presheaf.map v.op
    (M.presheaf.map (homOfLE (W.ι.image_preimage_le W)).op s) =
      M.presheaf.map (eqToHom W.ι_image_top).op s := by
    change M.presheaf.map (W.ι.opensFunctor.map v).op
      (M.presheaf.map (homOfLE (W.ι.image_preimage_le W)).op s) = _
    rw [← Functor.map_comp_apply]
    congr 1
  change N.presheaf.map (eqToHom U.ι_image_top.symm).op
    ((β.hom.app M).app ⊤ ((ai.unit.app L).app ⊤
      (M.presheaf.map (eqToHom W.ι_image_top).op s))) = _
  change (ai.unit.app L).app ⊤
    (L.presheaf.map v.op (M.presheaf.map
      (homOfLE (W.ι.image_preimage_le W)).op s)) =
    ((tensorPullback i).obj L).presheaf.map q.op
      ((ai.unit.app L).app (W.ι ⁻¹ᵁ W)
        (M.presheaf.map (homOfLE (W.ι.image_preimage_le W)).op s)) at hv
  rw [← hinput, hv]
  erw [hn]
  rw [hs]
  change N.presheaf.map _ (N.presheaf.map _ (N.presheaf.map _
    (N.presheaf.map _ ((ag.unit.app M).app W s)))) = _
  simp only [← Functor.map_comp_apply]
  congr 1


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restrict the actual kernel pullback to a chart where the morphism is closed.
Source: Stacks Project, Tags 01R3 (1), 00A0 and 0096.
(blueprint: lem-sc-open-kernel-conormal-transport).

Proof: The preimage equality identifies the square of g and its restriction i
with a Cartesian square of open immersions. Restriction of sheaves preserves
kernels. On every open T of W the two maps on functions are identified by the
open-section isomorphisms, so their kernels, including their inclusions, agree.
Since i is closed, its actual kernel is its quasi-coherent ideal module.
Thus restriction gives an isomorphism between the original kernel and this
ideal module, taking s to the unique t with the displayed inclusion equation.
Compose the two pullback adjunctions around the Cartesian square. The canonical
isomorphism of left adjoints identifies their units; using the explicit units
from exists_tensorPullbackAdjunction, both images of s are the sheafification
of 1 ⊗ s. Pullback along the open inclusions is restriction. Take sections,
identify sections on the open subschemes with sections on the ambient opens,
and restrict scalars through the displayed map. This gives e and the unit
identity. This construction does not require g to be globally closed or its
kernel to be globally quasi-coherent. Empty opens give the zero-module maps. -/
theorem open_kernel_conormal_transport {X Y : Scheme.{u}} (g : X ⟶ Y)
    (W : Y.Opens) (U : X.Opens) (h : U ≤ g ⁻¹ᵁ W) (hpre : g ⁻¹ᵁ W = U)
    [IsClosedImmersion (g.resLE W U h)] :
    let i := g.resLE W U h
    let K := kernel (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom)
    let N := (tensorPullback g).obj K
    let C := (pushforward i).obj ((tensorPullback i).obj i.ker.toModules)
    letI : Module Γ(W.toScheme, ⊤) Γ(N, U) :=
      Module.compHom _ ((g.appLE W U h).hom.comp W.topIso.hom.hom)
    ∃ e : Γ(C, ⊤) ≃ₗ[Γ(W.toScheme, ⊤)] Γ(N, U),
      ∀ s : Γ(K, W), ∃ t : Γ(i.ker.toModules, ⊤),
        i.ker.toModulesι.app ⊤ t = W.topIso.inv
          ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
            g.toRingCatSheafHom)).val.app (op W) s) ∧
        e (((Classical.choose (exists_tensorPullbackAdjunction i)).unit.app
          i.ker.toModules).app ⊤ t) = N.presheaf.map (homOfLE h).op
            (((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app K).val.app
              (op W) s) := by
  classical
  let i := g.resLE W U h
  let f := SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom
  let K : Y.Modules := kernel f
  let N := (tensorPullback g).obj K
  let L := (restrictFunctor W.ι).obj K
  obtain ⟨δ, hδ⟩ := actual_kernel_restrict_iso g W U h hpre
  obtain ⟨e, he⟩ := open_pullback_sections_transport g W U h hpre K
  let d := (pushforward i).mapIso ((tensorPullback i).mapIso δ.symm)
  let d₀ := ((SheafOfModules.evaluation W.toScheme.ringCatSheaf (op ⊤)).mapIso d)
  let : Module Γ(W.toScheme, ⊤) Γ(N, U) :=
    Module.compHom _ ((g.appLE W U h).hom.comp W.topIso.hom.hom)
  let e₀ : Γ((pushforward i).obj ((tensorPullback i).obj i.ker.toModules), ⊤)
      ≃ₗ[Γ(W.toScheme, ⊤)] Γ((pushforward i).obj ((tensorPullback i).obj L), ⊤) :=
    d₀.toLinearEquiv
  refine ⟨e₀.trans e, ?_⟩
  intro s
  let s₀ : Γ(L, ⊤) := K.presheaf.map (eqToHom W.ι_image_top).op s
  let t := δ.hom.app ⊤ s₀
  refine ⟨t, ?_, ?_⟩
  · have hd := congrArg (fun q ↦ q.app ⊤ s₀) hδ
    change i.ker.toModulesι.app ⊤ t = _ at hd
    rw [hd]
    change (W.ι.appIso ⊤).hom
      ((kernel.ι f).val.app (op (W.ι ''ᵁ ⊤)) s₀) = _
    simp only [Scheme.Opens.ι_appIso, Iso.refl_hom]
    let κ : K ⟶ SheafOfModules.unit Y.ringCatSheaf := kernel.ι f
    have hn := congrArg (fun q ↦ q s)
      (κ.mapPresheaf.naturality (eqToHom W.ι_image_top).op)
    simp only [mapPresheaf_app, ConcreteCategory.comp_apply] at hn
    exact hn
  · have hn := congrArg (fun q ↦ q.app ⊤ t)
      ((Classical.choose (exists_tensorPullbackAdjunction i)).unit_naturality δ.inv)
    simp only [Hom.comp_app, pushforward_map_app,
      ConcreteCategory.comp_apply] at hn
    change e (((tensorPullback i).map δ.inv).app ⊤
      (((Classical.choose (exists_tensorPullbackAdjunction i)).unit.app
        i.ker.toModules).app ⊤ t)) = _
    have ht : δ.inv.app ⊤ t = s₀ := by
      exact ConcreteCategory.congr_hom
        (congrArg (fun q ↦ q.app ⊤) δ.hom_inv_id) s₀
    exact (congrArg e hn).trans
      ((congrArg (fun z ↦ e (((Classical.choose (exists_tensorPullbackAdjunction i)).unit.app
        L).app ⊤ z)) ht).trans (he s))

end AlgebraicGeometry.Scheme.Modules
