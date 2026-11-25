/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenArrows
import all WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearCompositorCoherence

/-! # Ordinary semilinear restriction normalization

Source: Stacks Project, Tags 03DI, 0F7B and 0F7F.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.VaryingRing
variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)
attribute [local instance] moduleJAdj_unit_isIso

attribute [local irreducible] moduleBeta moduleSquareG moduleGComp moduleJComp
  moduleAdj moduleJAdj Functor.leftAdjoint

private theorem beta_restriction {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g)
    (hsq : IsPullback a j' j g) (M : Modules R φ U) :
    (pull R φ j').map ((moduleBeta R φ a j' j g h hsq).hom.app M) ≫
        inv ((moduleJAdj R φ j').unit.app ((pull R φ a).obj M)) =
      (moduleSquareG R φ a j' j g h).hom.app ((extension R φ j).obj M) ≫
        (pull R φ a).map (inv ((moduleJAdj R φ j).unit.app M)) := by
  have hu : (moduleJAdj R φ j').unit.app ((pull R φ a).obj M) ≫
      (pull R φ j').map ((moduleBeta R φ a j' j g h hsq).inv.app M) =
    (pull R φ a).map ((moduleJAdj R φ j).unit.app M) ≫
      (moduleSquareG R φ a j' j g h).inv.app ((extension R φ j).obj M) := by
    have hh := ((moduleJAdj R φ j').homEquiv _ _).apply_symm_apply
      ((pull R φ a).map ((moduleJAdj R φ j).unit.app M) ≫
        (moduleSquareG R φ a j' j g h).inv.app ((extension R φ j).obj M))
    simpa only [Adjunction.homEquiv_unit, moduleBeta, Iso.symm_hom,
      Iso.symm_inv, asIso_hom, moduleBetaInv, moduleBetaInvApp,
      Functor.id_obj, Functor.comp_obj] using hh
  let u := asIso ((moduleJAdj R φ j').unit.app ((pull R φ a).obj M))
  let v := (pull R φ j').mapIso ((moduleBeta R φ a j' j g h hsq).app M)
  let z := (moduleSquareG R φ a j' j g h).app ((extension R φ j).obj M)
  let w := (pull R φ a).mapIso (asIso ((moduleJAdj R φ j).unit.app M))
  have he : u ≪≫ v.symm = w ≪≫ z.symm := Iso.ext hu
  have hi := congrArg (fun e ↦ e.inv) he
  simpa only [u, v, z, w, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, asIso_hom, asIso_inv,
    Iso.app_hom] using hi

private theorem pi_restriction {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] (M : Modules R φ X) :
    (pull R φ s).map ((modulePi R φ s).app M) =
      (moduleJAdj R φ s).unit.app ((pull R φ s).obj M) := by
  have := moduleOpenToP_isIso R φ s
  let t : Adjunction.Triple (extension R φ s) (pull R φ s) (push R φ s) :=
    ⟨moduleJAdj R φ s, moduleAdj R φ s⟩
  let ff := (moduleJAdj R φ s).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have he : moduleOpenToP R φ s = t.leftToRight := by
    ext N
    simp [moduleOpenToP, push, t, Adjunction.Triple.leftToRight]
  simp only [modulePi, NatTrans.comp_app, Functor.whiskerLeft_app,
    NatIso.isIso_inv_app, Functor.map_comp]
  apply (cancel_mono ((pull R φ s).map ((moduleOpenToP R φ s).app
    ((pull R φ s).obj M)))).1
  simp only [Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id, Category.comp_id]
  rw [he, t.leftToRight_app_obj, Functor.map_comp]
  change _ = (moduleJAdj R φ s).unit.app _ ≫
    (pull R φ s).map ((moduleJAdj R φ s).counit.app M) ≫ _
  rw [← Category.assoc, (moduleJAdj R φ s).right_triangle_components]
  exact (Category.id_comp _).symm

private theorem jcomp_restriction {U T V : Scheme.{u}} (s : U ⟶ T) (b : T ⟶ V)
    [IsOpenImmersion s] [IsOpenImmersion b] (N : Modules R φ U) :
    (pull R φ (s ≫ b)).map ((moduleJComp R φ s b).hom.app N) ≫
        inv ((moduleJAdj R φ (s ≫ b)).unit.app N) =
      (moduleGComp R φ s b).hom.app ((extension R φ b).obj ((extension R φ s).obj N)) ≫
        (pull R φ s).map (inv ((moduleJAdj R φ b).unit.app
          ((extension R φ s).obj N))) ≫ inv ((moduleJAdj R φ s).unit.app N) := by
  have hu := unit_conjugateEquiv ((moduleJAdj R φ s).comp (moduleJAdj R φ b))
    (moduleJAdj R φ (s ≫ b)) (moduleJComp R φ s b).inv N
  have hc : conjugateEquiv ((moduleJAdj R φ s).comp (moduleJAdj R φ b))
      (moduleJAdj R φ (s ≫ b)) (moduleJComp R φ s b).inv =
        (moduleGComp R φ s b).inv := by
    unfold moduleJComp
    exact Adjunction.conjugateEquiv_leftAdjointCompIso_inv
      (moduleJAdj R φ s) (moduleJAdj R φ b) (moduleJAdj R φ (s ≫ b))
      (moduleGComp R φ s b).symm
  rw [hc] at hu
  simp only [Adjunction.comp_unit_app, Functor.comp_obj, Functor.id_obj] at hu
  let e := asIso ((moduleJAdj R φ s).unit.app N) ≪≫
    (pull R φ s).mapIso (asIso ((moduleJAdj R φ b).unit.app
      ((extension R φ s).obj N))) ≪≫
    (moduleGComp R φ s b).symm.app ((extension R φ b).obj ((extension R φ s).obj N))
  let f := asIso ((moduleJAdj R φ (s ≫ b)).unit.app N) ≪≫
    (pull R φ (s ≫ b)).mapIso ((moduleJComp R φ s b).symm.app N)
  have he : e = f := Iso.ext (by
    simpa only [e, f, Iso.trans_hom, asIso_hom, Functor.mapIso_hom,
      Iso.app_hom, Iso.symm_hom, Category.assoc] using hu)
  have hi := congrArg Iso.inv he
  simpa only [e, f, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
    asIso_inv, Iso.app_inv, Iso.app_hom, Iso.symm_hom, Category.assoc] using hi.symm

private theorem section_restriction {U T V W : Scheme.{u}}
    (s : U ⟶ T) (b : T ⟶ V) (a : T ⟶ W)
    [IsOpenImmersion s] [IsClosedImmersion s] [IsOpenImmersion b]
    (M : Modules R φ W) :
    (pull R φ (s ≫ b)).map
        ((extension R φ b).map ((modulePi R φ s).app ((pull R φ a).obj M)) ≫
          (moduleJComp R φ s b).hom.app ((pull R φ s).obj ((pull R φ a).obj M)) ≫
          (extension R φ (s ≫ b)).map ((moduleGComp R φ s a).inv.app M)) ≫
        inv ((moduleJAdj R φ (s ≫ b)).unit.app ((pull R φ (s ≫ a)).obj M)) =
      (moduleGComp R φ s b).hom.app ((extension R φ b).obj ((pull R φ a).obj M)) ≫
        (pull R φ s).map (inv ((moduleJAdj R φ b).unit.app ((pull R φ a).obj M))) ≫
        (moduleGComp R φ s a).inv.app M := by
  have hn := (inv (moduleJAdj R φ (s ≫ b)).unit).naturality
    ((moduleGComp R φ s a).inv.app M)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, NatIso.isIso_inv_app] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [hn, reassoc_of% (jcomp_restriction R φ s b
    ((pull R φ s).obj ((pull R φ a).obj M)))]
  rw [reassoc_of% (moduleGComp R φ s b).hom.naturality
    ((extension R φ b).map ((modulePi R φ s).app ((pull R φ a).obj M)))]
  have hb := (inv (moduleJAdj R φ b).unit).naturality
    ((modulePi R φ s).app ((pull R φ a).obj M))
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.id_map,
    NatIso.isIso_inv_app] at hb
  slice_lhs 2 3 => rw [← Functor.map_comp, hb, Functor.map_comp]
  simp only [pi_restriction, Category.assoc, IsIso.hom_inv_id_assoc]

private def compEq {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (t : X ⟶ Z) (e : f ≫ g = t) :
    pull R φ t ≅ pull R φ g ⋙ pull R φ f :=
  eqToIso (congrArg (pull R φ) e.symm) ≪≫ moduleGComp R φ f g

private theorem compEq_coherence {A B C D : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D)
    (ab : A ⟶ C) (bc : B ⟶ D) (abc : A ⟶ D)
    (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
    (hl : ab ≫ c = abc) (hr : a ≫ bc = abc) :
    compEq R φ a bc abc hr ≪≫
        Functor.isoWhiskerRight (compEq R φ b c bc hbc) (pull R φ a) =
      compEq R φ ab c abc hl ≪≫
        Functor.isoWhiskerLeft (pull R φ c) (compEq R φ a b ab hab) := by
  subst ab bc
  cases hr
  apply Iso.ext
  apply NatTrans.ext
  funext M
  simpa only [compEq, eqToIso_refl, Iso.refl_trans, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp] using ordinary_coherence R φ a b c M

private theorem square_factor {U T V W Z : Scheme.{u}}
    (s : U ⟶ T) (a : T ⟶ W) (b : T ⟶ V) (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z)
    (ek : s ≫ b = k) (er : s ≫ a = r) (h : a ≫ i = b ≫ p)
    (w : k ≫ p = r ≫ i) :
    Functor.isoWhiskerLeft (pull R φ p)
        (compEq R φ s b k ek) ≪≫
        Functor.isoWhiskerRight (moduleSquareG R φ a b i p h) (pull R φ s) ≪≫
        (Functor.isoWhiskerLeft (pull R φ i)
          (compEq R φ s a r er)).symm =
      (moduleSquareG R φ k r p i w).symm := by
  have hs : s ≫ (b ≫ p) = k ≫ p := by rw [← Category.assoc, ek]
  have h₁ := compEq_coherence R φ s b p k (b ≫ p) (k ≫ p) ek rfl rfl hs
  have h₂ := compEq_coherence R φ s a i r (b ≫ p) (k ≫ p) er h w.symm hs
  have hb : moduleSquareG R φ a b i p h =
      (compEq R φ b p (b ≫ p) rfl).symm ≪≫ compEq R φ a i (b ≫ p) h := by
    rw [moduleSquareG_eq]
    simp only [compEq, eqToIso_refl, Iso.refl_trans]
  have hw : (moduleSquareG R φ k r p i w).symm =
      (compEq R φ k p (k ≫ p) rfl).symm ≪≫ compEq R φ r i (k ≫ p) w.symm := by
    have ht : (eqToIso (congrArg (pull R φ) w.symm)).symm =
        eqToIso (congrArg (pull R φ) w) := by
      apply Iso.ext
      rfl
    rw [moduleSquareG_eq]
    simp only [compEq, Iso.trans_symm, Iso.symm_symm_eq, eqToIso_refl,
      Iso.refl_trans, Iso.trans_assoc, ht]
  change Functor.isoWhiskerLeft (pull R φ p) (compEq R φ s b k ek) ≪≫ _ ≪≫
    (Functor.isoWhiskerLeft (pull R φ i) (compEq R φ s a r er)).symm = _
  rw [hb, hw, Functor.isoWhiskerRight_trans, ← Functor.isoWhiskerRight_symm]
  apply Iso.ext
  apply (cancel_epi (compEq R φ k p (k ≫ p) rfl).hom).mp
  apply (cancel_mono
    (Functor.isoWhiskerLeft (pull R φ i) (compEq R φ s a r er)).hom).mp
  have he₁ := congrArg Iso.hom h₁
  have he₂ := congrArg Iso.hom h₂
  simp only [Iso.trans_hom, Iso.symm_hom] at he₁ he₂ ⊢
  simp only [Category.assoc, Iso.inv_hom_id, Iso.hom_inv_id_assoc, Category.comp_id]
  slice_lhs 1 2 => rw [← he₁]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact he₂

private theorem section_restriction_congr {U T V W : Scheme.{u}}
    (s : U ⟶ T) (b : T ⟶ V) (a : T ⟶ W) (k : U ⟶ V) (r : U ⟶ W)
    [IsOpenImmersion s] [IsClosedImmersion s] [IsOpenImmersion b] [IsOpenImmersion k]
    (ek : s ≫ b = k) (er : s ≫ a = r) (M : Modules R φ W) :
    (pull R φ k).map
        ((extension R φ b).map ((modulePi R φ s).app ((pull R φ a).obj M)) ≫
          ((moduleJComp R φ s b).hom ≫ (moduleJCongr R φ ek).hom).app
            ((pull R φ s).obj ((pull R φ a).obj M)) ≫
          (extension R φ k).map (((moduleGComp R φ s a).inv ≫
            (eqToIso (congrArg (pull R φ) er)).hom).app M)) ≫
        inv ((moduleJAdj R φ k).unit.app ((pull R φ r).obj M)) =
      (compEq R φ s b k ek).hom.app
          ((extension R φ b).obj ((pull R φ a).obj M)) ≫
        (pull R φ s).map (inv ((moduleJAdj R φ b).unit.app ((pull R φ a).obj M))) ≫
        (compEq R φ s a r er).inv.app M := by
  subst k r
  simpa only [compEq, moduleJCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    NatTrans.comp_app, Category.comp_id, Iso.refl_trans] using
      section_restriction R φ s b a M

private theorem compose_restrictions {𝒞 : Type*} [Category* 𝒞]
    {A B C D E F : 𝒞} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (t : D ⟶ E)
    (u : C ⟶ F) (v : F ⟶ E) (z : A ⟶ F)
    (hy : h ≫ t = u ≫ v) (hc : f ≫ g ≫ u = z) :
    f ≫ g ≫ h ≫ t = z ≫ v := by
  calc
    _ = f ≫ g ≫ u ≫ v := by rw [hy]
    _ = (f ≫ g ≫ u) ≫ v := by simp only [Category.assoc]
    _ = z ≫ v := congrArg (fun q ↦ q ≫ v) hc

private theorem right_composite_naturality {C D E : Type*}
    [Category* C] [Category* D] [Category* E]
    {F : C ⥤ D} {G : C ⥤ E} {H : E ⥤ D} (α : F ⟶ G ⋙ H)
    {M N : C} (f : M ⟶ N) :
    F.map f ≫ α.app N = α.app M ≫ H.map (G.map f) := α.naturality f

private theorem left_composite_naturality {C D E : Type*}
    [Category* C] [Category* D] [Category* E]
    {F : C ⥤ E} {G : E ⥤ D} {H : C ⥤ D} (α : F ⋙ G ⟶ H)
    {M N : C} (f : M ⟶ N) :
    G.map (F.map f) ≫ α.app N = α.app M ≫ H.map f := α.naturality f

private theorem square_word {C D E F G : Type*}
    [Category* C] [Category* D] [Category* E] [Category* F] [Category* G]
    (P : C ⥤ D) (I : C ⥤ E) (B : D ⥤ F) (A : E ⥤ F) (S : F ⥤ G)
    (K : D ⥤ G) (Q : E ⥤ G) (x : K ≅ B ⋙ S) (z : P ⋙ B ≅ I ⋙ A)
    (y : Q ≅ A ⋙ S) (t : P ⋙ K ≅ I ⋙ Q)
    (e : Functor.isoWhiskerLeft P x ≪≫ Functor.isoWhiskerRight z S ≪≫
      (Functor.isoWhiskerLeft I y).symm = t) (M : C) :
    x.hom.app (P.obj M) ≫ S.map (z.hom.app M) ≫ y.inv.app (I.obj M) = t.hom.app M := by
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.isoWhiskerLeft_inv] using
      NatTrans.congr_app (congrArg Iso.hom e) M

private theorem map_restriction {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {A B C' : C} {T : D}
    (a : A ⟶ C') (b : A ⟶ B) (c : B ⟶ C') (u : F.obj C' ⟶ T) (v : F.obj B ⟶ T)
    (ha : a = b ≫ c) (hs : F.map c ≫ u = v) : F.map a ≫ u = F.map b ≫ v := by
  rw [ha, F.map_comp, Category.assoc, hs]

private theorem map_comp_eq {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {A B C' E : C} (a : A ⟶ B) (b : B ⟶ E) (c : A ⟶ C')
    (d : C' ⟶ E) (h : a ≫ b = c ≫ d) : F.map a ≫ F.map b = F.map c ≫ F.map d := by
  simpa only [F.map_comp] using congrArg F.map h

private theorem word_restriction {𝒞 : Type*} [Category* 𝒞]
    {A B C D E F G H : 𝒞} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (d : D ⟶ E)
    (x : A ⟶ F) (q : F ⟶ C) (g : F ⟶ G) (h : G ⟶ D) (u : G ⟶ H) (v : H ⟶ E)
    (z : A ⟶ H) (hx : a ≫ b = x ≫ q) (hb : q ≫ c = g ≫ h)
    (hy : h ≫ d = u ≫ v) (hc : x ≫ g ≫ u = z) : a ≫ b ≫ c ≫ d = z ≫ v := by
  calc
    _ = (a ≫ b) ≫ c ≫ d := by simp only [Category.assoc]
    _ = (x ≫ q) ≫ c ≫ d := by rw [hx]
    _ = x ≫ (q ≫ c) ≫ d := by simp only [Category.assoc]
    _ = x ≫ (g ≫ h) ≫ d := by rw [hb]
    _ = x ≫ g ≫ h ≫ d := by simp only [Category.assoc]
    _ = z ≫ v := compose_restrictions x g h d u v z hy hc

private def factor {C D E F : Type*}
    [Category* C] [Category* D] [Category* E] [Category* F]
    (A : C ⥤ D) (S : D ⥤ E) (J : E ⥤ D) (B : D ⥤ F)
    (L : C ⥤ F) (Q : C ⥤ E) (K : E ⥤ F)
    (β : L ⟶ A ⋙ B) (π : 𝟭 D ⟶ S ⋙ J) (j : J ⋙ B ⟶ K) (y : A ⋙ S ⟶ Q) :
    L ⟶ Q ⋙ K :=
  β ≫ Functor.whiskerRight (Functor.whiskerLeft A π) B ≫
    Functor.whiskerRight (Functor.associator A S J).inv B ≫
    (Functor.associator (A ⋙ S) J B).hom ≫
    Functor.whiskerLeft (A ⋙ S) j ≫ Functor.whiskerRight y K

private theorem factor_app {C D E F : Type*}
    [Category* C] [Category* D] [Category* E] [Category* F]
    (A : C ⥤ D) (S : D ⥤ E) (J : E ⥤ D) (B : D ⥤ F)
    (L : C ⥤ F) (Q : C ⥤ E) (K : E ⥤ F)
    (β : L ⟶ A ⋙ B) (π : 𝟭 D ⟶ S ⋙ J) (j : J ⋙ B ⟶ K) (y : A ⋙ S ⟶ Q)
    (M : C) :
    (factor A S J B L Q K β π j y).app M =
      β.app M ≫ B.map (π.app (A.obj M)) ≫ j.app (S.obj (A.obj M)) ≫ K.map (y.app M) := by
  dsimp only [factor, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj]
  simp only [B.map_id, Category.id_comp]

private theorem alpha_factor
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (w : k ≫ p = r ≫ i) :
    moduleAlpha R φ k r p i w = factor
      (pull R φ (pullback.snd p i)) (pull R φ (StrictTower.squareLift k r p i w))
      (extension R φ (StrictTower.squareLift k r p i w))
      (extension R φ (pullback.fst p i)) (extension R φ i ⋙ pull R φ p)
      (pull R φ r) (extension R φ k)
      (moduleBeta R φ (pullback.snd p i) (pullback.fst p i) i p
        pullback.condition.symm (IsPullback.of_hasPullback p i).flip).hom
      (modulePi R φ (StrictTower.squareLift k r p i w))
      ((moduleJComp R φ (StrictTower.squareLift k r p i w) (pullback.fst p i)).hom ≫
        (moduleJCongr R φ (pullback.lift_fst k r w)).hom)
      ((moduleGComp R φ (StrictTower.squareLift k r p i w) (pullback.snd p i)).inv ≫
        (eqToIso (congrArg (pull R φ) (pullback.lift_snd k r w))).hom) := by
  rfl

private theorem functor_calculation {C D E F G : Type*}
    [Category* C] [Category* D] [Category* E] [Category* F] [Category* G]
    (P : C ⥤ D) (I : C ⥤ E) (B : D ⥤ F) (A : E ⥤ F) (S : F ⥤ G)
    (K : D ⥤ G) (Q : E ⥤ G) (J : F ⥤ D) (L : E ⥤ C)
    (x : K ≅ B ⋙ S) (y : Q ≅ A ⋙ S) (z : P ⋙ B ≅ I ⋙ A) (t : P ⋙ K ≅ I ⋙ Q)
    (β : L ⋙ P ⟶ A ⋙ J) (u : ∀ N : F, B.obj (J.obj N) ⟶ N)
    (v : ∀ N : E, I.obj (L.obj N) ⟶ N)
    (hβ : ∀ N : E, B.map (β.app N) ≫ u (A.obj N) =
      z.hom.app (L.obj N) ≫ A.map (v N))
    (he : Functor.isoWhiskerLeft P x ≪≫ Functor.isoWhiskerRight z S ≪≫
      (Functor.isoWhiskerLeft I y).symm = t) (M : E) :
    K.map (β.app M) ≫ x.hom.app (J.obj (A.obj M)) ≫
        S.map (u (A.obj M)) ≫ y.inv.app M =
      t.hom.app (L.obj M) ≫ Q.map (v M) := by
  have hx := right_composite_naturality (F := K) (G := B) (H := S) x.hom (β.app M)
  have hb := map_comp_eq S (B.map (β.app M)) (u (A.obj M))
    (z.hom.app (L.obj M)) (A.map (v M)) (hβ M)
  have hy := left_composite_naturality (F := A) (G := S) (H := Q) y.inv (v M)
  have hc := square_word P I B A S K Q x z y t he (L.obj M)
  exact word_restriction (𝒞 := G) (K.map (β.app M)) (x.hom.app (J.obj (A.obj M)))
    (S.map (u (A.obj M))) (y.inv.app M) (x.hom.app (P.obj (L.obj M)))
    (S.map (B.map (β.app M))) (S.map (z.hom.app (L.obj M)))
    (S.map (A.map (v M))) (y.inv.app (I.obj (L.obj M))) (Q.map (v M))
    (t.hom.app (L.obj M)) hx hb hy hc

-- Keep the chosen composition comparisons abstract during the calculation.
attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [local irreducible] compEq in
set_option backward.isDefEq.respectTransparency.types true in
private theorem alpha_calculation
    (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)
    {U T V W Z : Scheme.{u}}
    (s : U ⟶ T) (a : T ⟶ W) (b : T ⟶ V) (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion b] [IsOpenImmersion i]
    (ek : s ≫ b = k) (er : s ≫ a = r) (h : a ≫ i = b ≫ p)
    (w : k ≫ p = r ≫ i) (hsq : IsPullback a b i p) (M : Modules R φ W) :
    let x := compEq R φ s b k ek
    let y := (compEq R φ s a r er).inv
    let β := (moduleBeta R φ a b i p h hsq).hom
    (pull R φ k).map (β.app M) ≫
        x.hom.app ((extension R φ b).obj ((pull R φ a).obj M)) ≫
        (pull R φ s).map (inv ((moduleJAdj R φ b).unit.app ((pull R φ a).obj M))) ≫
        y.app M =
      (moduleSquareG R φ k r p i w).inv.app ((extension R φ i).obj M) ≫
        (pull R φ r).map (inv ((moduleJAdj R φ i).unit.app M)) := by
  exact functor_calculation (pull R φ p) (pull R φ i) (pull R φ b) (pull R φ a)
    (pull R φ s) (pull R φ k) (pull R φ r) (extension R φ b) (extension R φ i)
    (compEq R φ s b k ek) (compEq R φ s a r er)
    (moduleSquareG R φ a b i p h) (moduleSquareG R φ k r p i w).symm
    (moduleBeta R φ a b i p h hsq).hom
    (fun N ↦ inv ((moduleJAdj R φ b).unit.app N))
    (fun N ↦ inv ((moduleJAdj R φ i).unit.app N))
    (beta_restriction R φ a b i p h hsq) (square_factor R φ s a b k r p i ek er h w) M

-- Apply the calculation to an arbitrary clopen factorization of alpha.
attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [local irreducible] compEq in
set_option backward.isDefEq.respectTransparency.types true in
private theorem factor_restriction
    (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)
    {U T V W Z : Scheme.{u}}
    (s : U ⟶ T) (a : T ⟶ W) (b : T ⟶ V) (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion s] [IsClosedImmersion s] [IsOpenImmersion b]
    [IsOpenImmersion k] [IsOpenImmersion i]
    (ek : s ≫ b = k) (er : s ≫ a = r) (h : a ≫ i = b ≫ p)
    (w : k ≫ p = r ≫ i) (hsq : IsPullback a b i p) (M : Modules R φ W)
    (α : extension R φ i ⋙ pull R φ p ⟶ pull R φ r ⋙ extension R φ k)
    (ha : α = factor (pull R φ a) (pull R φ s) (extension R φ s)
      (extension R φ b) (extension R φ i ⋙ pull R φ p) (pull R φ r) (extension R φ k)
      (moduleBeta R φ a b i p h hsq).hom (modulePi R φ s)
      ((moduleJComp R φ s b).hom ≫ (moduleJCongr R φ ek).hom)
      ((moduleGComp R φ s a).inv ≫ (eqToIso (congrArg (pull R φ) er)).hom)) :
    (pull R φ k).map (α.app M) ≫ inv ((moduleJAdj R φ k).unit.app ((pull R φ r).obj M)) =
      (moduleSquareG R φ k r p i w).inv.app ((extension R φ i).obj M) ≫
        (pull R φ r).map (inv ((moduleJAdj R φ i).unit.app M)) := by
  let β := (moduleBeta R φ a b i p h hsq).hom
  have he := map_restriction (pull R φ k) (α.app M) (β.app M)
    ((extension R φ b).map ((modulePi R φ s).app ((pull R φ a).obj M)) ≫
      ((moduleJComp R φ s b).hom ≫ (moduleJCongr R φ ek).hom).app
        ((pull R φ s).obj ((pull R φ a).obj M)) ≫
      (extension R φ k).map (((moduleGComp R φ s a).inv ≫
        (eqToIso (congrArg (pull R φ) er)).hom).app M))
    (inv ((moduleJAdj R φ k).unit.app ((pull R φ r).obj M)))
    ((compEq R φ s b k ek).hom.app ((extension R φ b).obj ((pull R φ a).obj M)) ≫
      (pull R φ s).map (inv ((moduleJAdj R φ b).unit.app ((pull R φ a).obj M))) ≫
      (compEq R φ s a r er).inv.app M)
    ((NatTrans.congr_app ha M).trans (factor_app (pull R φ a) (pull R φ s) (extension R φ s)
      (extension R φ b) (extension R φ i ⋙ pull R φ p) (pull R φ r) (extension R φ k)
      (moduleBeta R φ a b i p h hsq).hom (modulePi R φ s)
      ((moduleJComp R φ s b).hom ≫ (moduleJCongr R φ ek).hom)
      ((moduleGComp R φ s a).inv ≫ (eqToIso (congrArg (pull R φ) er)).hom) M))
    (section_restriction_congr R φ s b a k r ek er M)
  exact he.trans (alpha_calculation R φ s a b k r p i ek er h w hsq M)

attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [local irreducible] compEq moduleAlpha modulePi moduleJCongr push eqToIso factor in
set_option backward.isDefEq.respectTransparency.types true in
/-- Restriction of intrinsic alpha is the inverse of the open unit, under the specified
inverse-image square comparison.
Source: Stacks Project, Tags 03DI and 0F7B; the restriction calculation in Tag 0F7F
(blueprint: lem-sf-semilinear-alpha-restriction).
Proof: factor the square through its canonical fibre product. The lift is clopen.
The open base-change comparison is the inverse transpose of the open unit, so its
restriction is the square compositor followed by the inverse open unit. The clopen
projector is the direct-image unit followed by inverse open-to-direct comparison;
the two triangle identities give that its restriction is the open unit. The open
composition comparison preserves the units by its adjoint definition. Apply these
three formulas to the defining beta-projector-compositor word for alpha. Naturality
cancels the intermediate open units, and inverse-image composition identifies the
remaining restriction with r-star of the inverse unit for i. -/
theorem moduleAlpha_restriction
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (w : k ≫ p = r ≫ i) (M : Modules R φ W) :
    (pull R φ k).map ((moduleAlpha R φ k r p i w).app M) ≫
        inv ((moduleJAdj R φ k).unit.app ((pull R φ r).obj M)) =
      (moduleSquareG R φ k r p i w).inv.app ((extension R φ i).obj M) ≫
        (pull R φ r).map (inv ((moduleJAdj R φ i).unit.app M)) := by
  exact factor_restriction R φ (StrictTower.squareLift k r p i w)
    (pullback.snd p i) (pullback.fst p i) k r p i
    (pullback.lift_fst k r w) (pullback.lift_snd k r w) pullback.condition.symm w
    (IsPullback.of_hasPullback p i).flip M (moduleAlpha R φ k r p i w) (alpha_factor R φ k r p i w)

end AlgebraicGeometry.ProEtale.VaryingRing
