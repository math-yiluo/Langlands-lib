/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Modules.Tilde

import WeilConjectures.AlgebraicGeometry.FormalSystemsPullback
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Affine section comparisons for coherent formal modules

Source: Stacks Project, Lemmas 087W and 087X.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Compare affine top sections using inverse pushforward and uniqueness of left adjoints. -/
private noncomputable def affineSectionsIso (X : Scheme.{u}) (V : X.affineOpens) :
    SheafOfModules.evaluation V.1.toScheme.ringCatSheaf (op ⊤) ⋙
        ModuleCat.restrictScalars V.1.topIso.inv.hom ≅
      Scheme.Modules.tensorPullback V.2.isoSpec.inv ⋙
        moduleSpecΓFunctor (R := CommRingCat.of Γ(X, V.1)) := by
  let e := V.2.isoSpec
  let E : V.1.toScheme.Modules ≌ (Spec (CommRingCat.of Γ(X, V.1))).Modules :=
    CategoryTheory.Equivalence.mk
      (Scheme.Modules.pushforward e.hom) (Scheme.Modules.pushforward e.inv)
      ((Scheme.Modules.pushforwardId _).symm ≪≫
        Scheme.Modules.pushforwardCongr e.hom_inv_id.symm ≪≫
        (Scheme.Modules.pushforwardComp _ _).symm)
      (Scheme.Modules.pushforwardComp _ _ ≪≫
        Scheme.Modules.pushforwardCongr e.inv_hom_id ≪≫ Scheme.Modules.pushforwardId _)
  let t := (Scheme.Modules.nonempty_tensorPullbackAdjunction e.inv).some.leftAdjointUniq
    E.toAdjunction
  refine ?_ ≪≫ (Functor.isoWhiskerRight t
    (moduleSpecΓFunctor (R := CommRingCat.of Γ(X, V.1)))).symm
  let ev := SheafOfModules.evaluation V.1.toScheme.ringCatSheaf (op ⊤)
  have h : (Scheme.ΓSpecIso (CommRingCat.of Γ(X, V.1))).inv ≫ e.hom.appTop =
      V.1.topIso.inv := by
    change (Scheme.ΓSpecIso Γ(X, V.1)).inv ≫ e.hom.appTop = _
    rw [IsAffineOpen.isoSpec_hom_appTop]
    simp
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · exact (ModuleCat.restrictScalarsComp'
      (Scheme.ΓSpecIso (CommRingCat.of Γ(X, V.1))).inv.hom e.hom.appTop.hom
      V.1.topIso.inv.hom (congrArg CommRingCat.Hom.hom h.symm)).app (ev.obj M)
  · intro M N f
    ext x
    rfl

/-- Transport coherent formal modules from an affine open to its canonical spectrum,
including the natural comparison of the underlying A-module section diagrams.
Source: Stacks Project, Lemma 087X, affine reduction, and Lemma 087W.
(blueprint: lem-weil-pbc-formal-affine-spec-transport)

Proof: Put A=Γ(X,V) and J=I(V). Use IsAffineOpen.isoSpec to identify V with Spec A.
The ideal comapped along its inverse is ofIdealTop (J.map ΓSpecIso.inv): the inverse
has top ring map V.topIso.hom followed by ΓSpecIso.inv, and extension of I to V has
top ideal J transported by V.topIso.inv. Check equality on the affine basis using
quasi-coherence. Termwise tensor pullback along the inverse isomorphism gives T.
The functor in the other direction is tensor pullback along the isomorphism, with
the ideal equality just checked. Pullback composition and identity isomorphisms
supply inverse comparisons; lift these through the fully faithful full-subcategory
inclusions to obtain the transport equivalence. To compare sections, pushforward
along the affine isomorphism and its inverse are inverse equivalences of module
categories. Uniqueness of left adjoints identifies inverse-isomorphism tensor
pullback with forward-isomorphism pushforward. Its top sections are the original
top sections with scalars restricted along the forward top-ring map. Composing
that map with ΓSpecIso.inv gives V.topIso.inv, so restrictScalarsComp' supplies the
A-linear comparison, naturally in all module sheaves. Whisker this comparison by
the inverse-system functor and the formal-module inclusion; the equation defining
P identifies the result with the section diagram after T. Empty V and zero or unit ideals obey the
same formulas, since none of the argument requires a nonzero ring or proper ideal.
-/
theorem coherentFormalModule_affine_spec_transport
    (X : Scheme.{u}) [IsNoetherian X] (I : X.IdealSheafData) (V : X.affineOpens)
    [IsNoetherian V.1.toScheme] :
    letI : IsNoetherianRing Γ(X, V.1) :=
      IsLocallyNoetherian.component_noetherian V
    ∃ T : CoherentFormalModule V.1.toScheme (I.comap V.1.ι) ≌
      CoherentFormalModule (Spec (CommRingCat.of Γ(X, V.1)))
        (Scheme.IdealSheafData.ofIdealTop
          ((I.ideal V).map (Scheme.ΓSpecIso (CommRingCat.of Γ(X, V.1))).inv.hom)),
    Nonempty
      (((IsCoherentFormalModule (I.comap V.1.ι)).ι ⋙
          (Functor.whiskeringRight ℕᵒᵖ V.1.toScheme.Modules (ModuleCat Γ(X, V.1))).obj
            (SheafOfModules.evaluation V.1.toScheme.ringCatSheaf (op ⊤) ⋙
              ModuleCat.restrictScalars V.1.topIso.inv.hom)) ≅
        T.functor ⋙
          (IsCoherentFormalModule (Scheme.IdealSheafData.ofIdealTop
            ((I.ideal V).map
              (Scheme.ΓSpecIso (CommRingCat.of Γ(X, V.1))).inv.hom))).ι ⋙
          (Functor.whiskeringRight ℕᵒᵖ
            (Spec (CommRingCat.of Γ(X, V.1))).Modules (ModuleCat Γ(X, V.1))).obj
              (moduleSpecΓFunctor (R := CommRingCat.of Γ(X, V.1)))) := by
  classical
  let : IsNoetherianRing Γ(X, V.1) :=
    IsLocallyNoetherian.component_noetherian V
  have : IsAffine V.1.toScheme := V.2
  let e := V.2.isoSpec
  let K := Scheme.IdealSheafData.ofIdealTop
    ((I.ideal V).map (Scheme.ΓSpecIso (CommRingCat.of Γ(X, V.1))).inv.hom)
  have hK : (I.comap V.1.ι).comap e.inv = K := by
    apply Scheme.IdealSheafData.ext_of_isAffine
    rw [Scheme.IdealSheafData.ideal_top_comap_of_isAffine,
      Scheme.IdealSheafData.ideal_top_ofIdealTop,
      IsAffineOpen.isoSpec_inv_appTop, CommRingCat.hom_comp, ← Ideal.map_map,
      Scheme.IdealSheafData.map_topIso_ideal_top_comap_ι]
    rfl
  have hI : K.comap e.hom = I.comap V.1.ι := by
    rw [← hK, ← Scheme.IdealSheafData.comap_comp, e.hom_inv_id,
      Scheme.IdealSheafData.comap_id]
  have hP := (exists_formalSystemsPullback e.inv (I.comap V.1.ι)).1
  rw [hK] at hP
  obtain ⟨P, _, hP, _, _⟩ := hP
  have hQ := (exists_formalSystemsPullback e.hom K).1
  rw [hI] at hQ
  obtain ⟨Q, _, hQ, _, _⟩ := hQ
  obtain ⟨cX⟩ := Scheme.Modules.nonempty_tensorPullbackComp e.hom e.inv
  obtain ⟨cY⟩ := Scheme.Modules.nonempty_tensorPullbackComp e.inv e.hom
  rw [e.hom_inv_id] at cX
  rw [e.inv_hom_id] at cY
  obtain ⟨iX⟩ := Scheme.Modules.nonempty_tensorPullbackId V.1.toScheme
  obtain ⟨iY⟩ := Scheme.Modules.nonempty_tensorPullbackId
    (Spec (CommRingCat.of Γ(X, V.1)))
  let aX := cX.symm ≪≫ iX
  let aY := cY.symm ≪≫ iY
  let WX := Functor.whiskeringRight ℕᵒᵖ V.1.toScheme.Modules V.1.toScheme.Modules
  let WY := Functor.whiskeringRight ℕᵒᵖ
    (Spec (CommRingCat.of Γ(X, V.1))).Modules
    (Spec (CommRingCat.of Γ(X, V.1))).Modules
  let IX := ObjectProperty.ι (IsCoherentFormalModule (I.comap V.1.ι))
  let IY := ObjectProperty.ι (IsCoherentFormalModule K)
  have hPX : (P ⋙ Q) ⋙ IX = IX ⋙ WX.obj
      (Scheme.Modules.tensorPullback e.inv ⋙ Scheme.Modules.tensorPullback e.hom) := by
    rw [Functor.assoc, hQ, ← Functor.assoc, hP, Functor.assoc]
    exact congrArg (IX ⋙ ·) (Functor.whiskeringRight_obj_comp _ _)
  have hQY : (Q ⋙ P) ⋙ IY = IY ⋙ WY.obj
      (Scheme.Modules.tensorPullback e.hom ⋙ Scheme.Modules.tensorPullback e.inv) := by
    rw [Functor.assoc, hP, ← Functor.assoc, hQ, Functor.assoc]
    exact congrArg (IY ⋙ ·) (Functor.whiskeringRight_obj_comp _ _)
  let u : (P ⋙ Q) ⋙ IX ≅ (𝟭 _) ⋙ IX :=
    eqToIso hPX ≪≫ Functor.isoWhiskerLeft IX (WX.mapIso aX) ≪≫
      Functor.rightUnitor IX ≪≫ (Functor.leftUnitor IX).symm
  let v : (Q ⋙ P) ⋙ IY ≅ (𝟭 _) ⋙ IY :=
    eqToIso hQY ≪≫ Functor.isoWhiskerLeft IY (WY.mapIso aY) ≪≫
      Functor.rightUnitor IY ≪≫ (Functor.leftUnitor IY).symm
  let T := CategoryTheory.Equivalence.mk P Q
    (Functor.fullyFaithfulCancelRight IX u).symm
    (Functor.fullyFaithfulCancelRight IY v)
  refine ⟨T, ?_⟩
  let W := Functor.whiskeringRight ℕᵒᵖ V.1.toScheme.Modules (ModuleCat Γ(X, V.1))
  let G := (Functor.whiskeringRight ℕᵒᵖ
    (Spec (CommRingCat.of Γ(X, V.1))).Modules (ModuleCat Γ(X, V.1))).obj
      (moduleSpecΓFunctor (R := CommRingCat.of Γ(X, V.1)))
  have hPG : P ⋙ IY ⋙ G = IX ⋙ W.obj
      (Scheme.Modules.tensorPullback e.inv ⋙
        moduleSpecΓFunctor (R := CommRingCat.of Γ(X, V.1))) := by
    rw [← Functor.assoc, hP, Functor.assoc]
    exact congrArg (IX ⋙ ·) (Functor.whiskeringRight_obj_comp _ _)
  exact ⟨Functor.isoWhiskerLeft IX (W.mapIso (affineSectionsIso X V)) ≪≫
    (eqToIso hPG).symm⟩

end AlgebraicGeometry
