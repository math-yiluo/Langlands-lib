/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.Algebra.Category.ModuleCat.Limits

import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesAffine
import WeilConjectures.AlgebraicGeometry.FormalSystemsPullback
import WeilConjectures.AlgebraicGeometry.ModulePullbackIdealPowerProductImage
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine

/-! # The affine formal equivalence with its two natural comparisons

Source: Stacks Project, Tags 087W, 01IB and 00MA.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open CategoryTheory.Limits in
/-- Pullback identifies positive-power quotient cokernels, using the ideal-product image
comparison and preservation of cokernels. This is the construction from FormalSystemsPullback. -/
private noncomputable def powerQuotientIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : Y.IdealSheafData) (G : Y.Modules) (hG : G.IsQuasicoherent) (n : ℕ) :
    formalModuleQuotient (J.comap f) n ((Scheme.Modules.tensorPullback f).obj G) ≅
      (Scheme.Modules.tensorPullback f).obj (formalModuleQuotient J n G) := by
  let T := Scheme.Modules.tensorPullback f
  let : T.IsLeftAdjoint := ⟨_, Scheme.Modules.nonempty_tensorPullbackAdjunction f⟩
  let i := Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι n).2 G
  let k := Scheme.idealModuleProductι
    (Scheme.idealSheafPower (J.comap f).toModulesι n).2 (T.obj G)
  have : Mono k := by dsimp [k, Scheme.idealModuleProductι]; infer_instance
  have he : Subobject.mk k = Subobject.mk (image.ι (T.map i)) := by
    rw [← imageSubobject_mono k]
    exact (modulePullbackIdealPowerProductImage f J G hG n).symm
  let e := Subobject.isoOfMkEqMk k (image.ι (T.map i)) he
  exact cokernel.mapIso k (image.ι (T.map i)) e (Iso.refl _) (by simp [e]) ≪≫
    cokernelImageι (T.map i) ≪≫ (PreservesCokernel.iso T i).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open CategoryTheory.Limits in
private theorem powerQuotientIso_π {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : Y.IdealSheafData) (G : Y.Modules) (hG : G.IsQuasicoherent) (n : ℕ) :
    formalModuleQuotientπ (J.comap f) n ((Scheme.Modules.tensorPullback f).obj G) ≫
        (powerQuotientIso f J G hG n).hom =
      (Scheme.Modules.tensorPullback f).map (formalModuleQuotientπ J n G) := by
  let T := Scheme.Modules.tensorPullback f
  let : T.IsLeftAdjoint := ⟨_, Scheme.Modules.nonempty_tensorPullbackAdjunction f⟩
  dsimp only [powerQuotientIso, Iso.trans_hom, Iso.symm_hom]
  rw [PreservesCokernel.iso_inv]
  simp [formalModuleQuotientπ, cokernel.mapIso, cokernelImageι]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open CategoryTheory.Limits in
private theorem quotientMap_π {X : Scheme.{u}} (J : X.IdealSheafData)
    {G H : X.Modules} (a : G ⟶ H) {m n : ℕ} (h : n ≤ m) :
    formalModuleQuotientπ J m G ≫ formalModuleQuotientMap J a h =
      a ≫ formalModuleQuotientπ J n H := by
  exact cokernel.π_desc _ _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open CategoryTheory.Limits in
private theorem powerQuotientIso_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : Y.IdealSheafData) {G H : Y.Modules}
    (hG : G.IsQuasicoherent) (hH : H.IsQuasicoherent)
    (a : G ⟶ H) {m n : ℕ} (h : n ≤ m) :
    (powerQuotientIso f J G hG m).hom ≫
        (Scheme.Modules.tensorPullback f).map (formalModuleQuotientMap J a h) =
      formalModuleQuotientMap (J.comap f) ((Scheme.Modules.tensorPullback f).map a) h ≫
        (powerQuotientIso f J H hH n).hom := by
  let T := Scheme.Modules.tensorPullback f
  apply (cancel_epi (cokernel.π (Scheme.idealModuleProductι
    (Scheme.idealSheafPower (J.comap f).toModulesι m).2 (T.obj G)))).1
  change formalModuleQuotientπ (J.comap f) m (T.obj G) ≫ _ =
    formalModuleQuotientπ (J.comap f) m (T.obj G) ≫ _
  rw [← Category.assoc, powerQuotientIso_π, ← T.map_comp, quotientMap_π, T.map_comp]
  rw [← Category.assoc, quotientMap_π, Category.assoc, powerQuotientIso_π]

-- Naturality unfolds the quotient-system functors and cokernel comparisons.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open CategoryTheory.Limits in
/-- The completion/pullback comparison for any functor landing in quasi-coherent sheaves.
The construction from FormalSystemsPullback applies here without a coherence assumption:
the restricted completed modules need not be finite over the uncompleted ring. -/
private noncomputable def completionPullbackIso {X Y : Scheme.{u}}
    (f : X ⟶ Y) (J : Y.IdealSheafData)
    {D : Type*} [Category D] (H : D ⥤ Y.Modules)
    (hq : ∀ G, (H.obj G).IsQuasicoherent) :
    (H ⋙
      Scheme.Modules.tensorPullback f) ⋙ formalCompletionFunctor (J.comap f) ≅
    (H ⋙
      formalCompletionFunctor J) ⋙
      (Functor.whiskeringRight ℕᵒᵖ Y.Modules X.Modules).obj
        (Scheme.Modules.tensorPullback f) := by
  refine NatIso.ofComponents (fun G ↦ NatIso.ofComponents
    (fun n ↦ powerQuotientIso f J (H.obj G) (hq G) (n.unop + 1)) ?_) ?_
  · rename_i G
    intro a b t
    change formalModuleQuotientMap (J.comap f)
        (𝟙 ((Scheme.Modules.tensorPullback f).obj (H.obj G)))
        (Nat.succ_le_succ (leOfHom t.unop)) ≫
          (powerQuotientIso f J (H.obj G) (hq G) (b.unop + 1)).hom =
      (powerQuotientIso f J (H.obj G) (hq G) (a.unop + 1)).hom ≫
        (Scheme.Modules.tensorPullback f).map (formalModuleQuotientMap J (𝟙 (H.obj G))
          (Nat.succ_le_succ (leOfHom t.unop)))
    have hn := (powerQuotientIso_naturality f J (hq G) (hq G) (𝟙 (H.obj G))
      (Nat.succ_le_succ (leOfHom t.unop))).symm
    rw [(Scheme.Modules.tensorPullback f).map_id] at hn
    exact hn
  · intro G G' a
    apply NatTrans.ext
    funext n
    exact (powerQuotientIso_naturality f J (hq G) (hq G') (H.map a)
      (Nat.le_refl (n.unop + 1))).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Compare affine top sections using inverse pushforward and uniqueness of left adjoints. -/
private noncomputable def affineSectionsIso (X : Scheme.{u}) [IsAffine X] :
    SheafOfModules.evaluation X.ringCatSheaf (op ⊤) ≅
      Scheme.Modules.tensorPullback X.isoSpec.inv ⋙
        moduleSpecΓFunctor (R := CommRingCat.of Γ(X, ⊤)) := by
  let e := X.isoSpec
  let E : X.Modules ≌ (Spec (CommRingCat.of Γ(X, ⊤))).Modules :=
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
    (moduleSpecΓFunctor (R := CommRingCat.of Γ(X, ⊤)))).symm
  let ev := SheafOfModules.evaluation X.ringCatSheaf (op ⊤)
  have h : (Scheme.ΓSpecIso (CommRingCat.of Γ(X, ⊤))).inv ≫ e.hom.appTop =
      𝟙 Γ(X, ⊤) := by
    change (Scheme.ΓSpecIso Γ(X, ⊤)).inv ≫ X.toSpecΓ.appTop = _
    rw [Scheme.toSpecΓ_appTop, Iso.inv_hom_id]
  refine (Functor.rightUnitor ev).symm ≪≫ ?_
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · exact (ModuleCat.restrictScalarsComp'
      (Scheme.ΓSpecIso (CommRingCat.of Γ(X, ⊤))).inv.hom e.hom.appTop.hom
      (RingHom.id Γ(X, ⊤)) (congrArg CommRingCat.Hom.hom h.symm)).app (ev.obj M)
  · intro M N f
    ext x
    rfl

-- Transport composes the affine, formal-system and finite-module equivalences.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On any affine Noetherian scheme, the finite completed-module equivalence has
its prescribed quotient-system realization and its natural section-limit realization.

Source: Stacks Project, Tag 087W, with the canonical affine chart of Tag 01IB and
finite-module completeness of Tag 00MA.
(blueprint: lem-weil-pbc-affine-global-formal-comparison).

Proof: Let A be the top section ring and I the top ideal. Pull back formal systems
along X.isoSpec.inv. The top ring map is GammaSpecIso.inv, so the transported ideal
is ofIdealTop (I.map GammaSpecIso.inv). Apply the equivalence of 087W over A and I
and compose its inverse with transport back to X. This gives E. The inverse
comparison of 087W identifies its underlying system with the completion of tilde
of the restricted finite module. Pullback along the affine chart commutes with
ideal products, powers, cokernels and the transition projections; uniqueness of
left adjoints identifies tensor pullback with Scheme.Modules.pullback. Thus these
comparisons give the first natural isomorphism. The cones in 087W identify the
restricted completed module with the inverse limit of its sections. Transporting
the cones across the chart gives cones on top sections of X: GammaSpecIso.inv
followed by the chart's top ring map is the identity on A. Their universal limit
isomorphisms give the second comparison. Naturality follows by composing with
each limit projection and using naturality of the transported cones. These
projections jointly distinguish maps. For I=0 the systems are constant; for I=A
both the completed ring and systems are zero. The argument also covers the empty
scheme and zero modules, without any nonzero-ring or proper-ideal assumption.
-/
theorem coherentFormalModules_affine_global_comparison
    (X : Scheme.{u}) [IsNoetherian X] [IsAffine X] (J : X.IdealSheafData) :
    let A := Γ(X, ⊤)
    let I := J.ideal ⟨⊤, isAffineOpen_top X⟩
    let S := AdicCompletion I A
    let F := ObjectProperty.FullSubcategory
      (fun Q : ModuleCat.{u} S ↦ Module.Finite S Q)
    let R := ObjectProperty.ι (fun Q : ModuleCat.{u} S ↦ Module.Finite S Q) ⋙
      ModuleCat.restrictScalars (algebraMap A S)
    let C := tilde.functor A ⋙ Scheme.Modules.pullback X.isoSpec.hom ⋙
      formalCompletionFunctor J
    let W := (Functor.whiskeringRight ℕᵒᵖ X.Modules (ModuleCat A)).obj
      (SheafOfModules.evaluation X.ringCatSheaf (op ⊤))
    ∃ E : F ≌ CoherentFormalModule X J,
      Nonempty (E.functor ⋙ (IsCoherentFormalModule J).ι ≅ R ⋙ C) ∧
      Nonempty (R ≅ E.functor ⋙ (IsCoherentFormalModule J).ι ⋙ W ⋙ lim) := by
  classical
  dsimp only
  let A := Γ(X, ⊤)
  let I := J.ideal ⟨⊤, isAffineOpen_top X⟩
  let : IsNoetherianRing A :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  let e := X.isoSpec
  let K := J.comap e.inv
  have hf : e.inv.appTop = (Scheme.ΓSpecIso A).inv := by
    apply (cancel_mono e.hom.appTop).1
    rw [← Scheme.Hom.comp_appTop, e.hom_inv_id, Scheme.Hom.id_appTop]
    change 𝟙 _ = (Scheme.ΓSpecIso A).inv ≫ X.toSpecΓ.appTop
    rw [Scheme.toSpecΓ_appTop, Iso.inv_hom_id]
  have hK : K = Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso A).inv.hom) := by
    apply Scheme.IdealSheafData.ext_of_isAffine
    rw [Scheme.IdealSheafData.ideal_top_ofIdealTop,
      Scheme.IdealSheafData.ideal_top_comap_of_isAffine, hf]
  have hJ : K.comap e.hom = J := by
    dsimp [K]
    rw [← Scheme.IdealSheafData.comap_comp, e.hom_inv_id,
      Scheme.IdealSheafData.comap_id]
  obtain ⟨P, _, hP, _, _⟩ := (exists_formalSystemsPullback e.inv J).1
  have hQ := (exists_formalSystemsPullback e.hom K).1
  rw [hJ] at hQ
  obtain ⟨Q, _, hQ, _, _⟩ := hQ
  obtain ⟨cX⟩ := Scheme.Modules.nonempty_tensorPullbackComp e.hom e.inv
  obtain ⟨cY⟩ := Scheme.Modules.nonempty_tensorPullbackComp e.inv e.hom
  rw [e.hom_inv_id] at cX
  rw [e.inv_hom_id] at cY
  obtain ⟨iX⟩ := Scheme.Modules.nonempty_tensorPullbackId X
  obtain ⟨iY⟩ := Scheme.Modules.nonempty_tensorPullbackId (Spec A)
  let aX := cX.symm ≪≫ iX
  let aY := cY.symm ≪≫ iY
  let WX := Functor.whiskeringRight ℕᵒᵖ X.Modules X.Modules
  let WY := Functor.whiskeringRight ℕᵒᵖ (Spec A).Modules (Spec A).Modules
  let IX := ObjectProperty.ι (IsCoherentFormalModule J)
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
  obtain ⟨E, p, hl, hn, _, _, ⟨b⟩⟩ := coherentFormalModules_affine A I K hK
  let R := ObjectProperty.ι
    (fun N : ModuleCat.{u} (AdicCompletion I A) ↦ Module.Finite (AdicCompletion I A) N) ⋙
      ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))
  let Z := (Functor.whiskeringRight ℕᵒᵖ (Spec A).Modules X.Modules).obj
    (Scheme.Modules.tensorPullback e.hom)
  let W := (Functor.whiskeringRight ℕᵒᵖ X.Modules (ModuleCat A)).obj
    (SheafOfModules.evaluation X.ringCatSheaf (op ⊤))
  let G := (Functor.whiskeringRight ℕᵒᵖ (Spec A).Modules (ModuleCat A)).obj
    (moduleSpecΓFunctor (R := A))
  refine ⟨E.symm.trans T.symm, ?_, ?_⟩
  · let H := R ⋙ tilde.functor A
    have hqc (N) : (H.obj N).IsQuasicoherent := by
      change (tilde (R := A) (R.obj N)).IsQuasicoherent
      infer_instance
    let c := completionPullbackIso e.hom K H hqc
    rw [hJ] at c
    let t : Scheme.Modules.tensorPullback e.hom ≅ Scheme.Modules.pullback e.hom :=
      (Scheme.Modules.nonempty_tensorPullbackAdjunction e.hom).some.leftAdjointUniq
        (Scheme.Modules.pullbackPushforwardAdjunction e.hom)
    refine ⟨?_⟩
    exact (eqToIso (congrArg (E.inverse ⋙ ·) hQ)) ≪≫
      Functor.isoWhiskerRight b Z ≪≫ c.symm ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft H t) (formalCompletionFunctor J)
  · let W' := Functor.whiskeringRight ℕᵒᵖ X.Modules (ModuleCat A)
    have hPG : P ⋙ IY ⋙ G = IX ⋙ W'.obj
        (Scheme.Modules.tensorPullback e.inv ⋙ moduleSpecΓFunctor (R := A)) := by
      rw [← Functor.assoc, hP, Functor.assoc]
      exact congrArg (IX ⋙ ·) (Functor.whiskeringRight_obj_comp _ _)
    let d : IX ⋙ W ≅ P ⋙ IY ⋙ G :=
      Functor.isoWhiskerLeft IX (W'.mapIso (affineSectionsIso X)) ≪≫
        (eqToIso hPG).symm
    let dQ : Q ⋙ IX ⋙ W ≅ IY ⋙ G :=
      Functor.isoWhiskerLeft Q d ≪≫ Functor.isoWhiskerRight v G ≪≫
        Functor.leftUnitor (IY ⋙ G)
    let c : E.functor ⋙ R ≅ IY ⋙ G ⋙ lim := NatIso.ofComponents
      (fun F ↦ (hl F).some.conePointUniqueUpToIso (limit.isLimit (G.obj F.obj))) (by
        intro F F' f
        apply limit.hom_ext
        intro n
        change R.map (E.functor.map f) ≫
            ((hl F').some.conePointUniqueUpToIso (limit.isLimit (G.obj F'.obj))).hom ≫
              limit.π (G.obj F'.obj) n =
          ((hl F).some.conePointUniqueUpToIso (limit.isLimit (G.obj F.obj))).hom ≫
            limMap (G.map (IY.map f)) ≫ limit.π (G.obj F'.obj) n
        erw [limMap_π, limit.conePointUniqueUpToIso_hom_comp,
          ← Category.assoc, limit.conePointUniqueUpToIso_hom_comp]
        exact hn F F' f n.unop)
    refine ⟨?_⟩
    exact (Functor.leftUnitor R).symm ≪≫
      (Functor.isoWhiskerRight E.counitIso R).symm ≪≫
      Functor.isoWhiskerLeft E.inverse c ≪≫
      Functor.isoWhiskerLeft E.inverse (Functor.isoWhiskerRight dQ.symm lim)

end AlgebraicGeometry
