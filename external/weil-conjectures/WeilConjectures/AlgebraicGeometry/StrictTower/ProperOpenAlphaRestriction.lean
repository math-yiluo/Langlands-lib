/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOrdinaryProperOpenArrows
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOrdinaryProperOpenArrows
import all WeilConjectures.AlgebraicGeometry.StrictTower.TowerOpenBetaNormalization

/-! # Restriction of the intrinsic proper/open arrow

Source: Stacks, Tags 09BN and 0F7B; restriction calculation in steps 2--3 of
`lem-cbc-proper-open-alpha-horizontal-modules`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types true
set_option linter.unusedSimpArgs false

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B : Type (u + 1)) [CommRing B]

/-- The inverse of the specified open adjunction unit. It identifies restriction
of extension by zero with the original module. Source: Stacks, Tag 09BN. -/
def moduleOpenUnitInv {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    moduleJ B j ⋙ modulePullback B j ⟶ 𝟭 (Modules B U) :=
  @inv _ _ _ _ (moduleJAdj B j).unit (clopenModule_openUnit_isIso B j)

attribute [local irreducible] Functor.leftAdjoint modulePullback moduleGComp
attribute [local irreducible] moduleSquareG openBetaModule openBetaModuleJComp
attribute [local irreducible] singleAlpha clopenModulePi singleJCongr moduleOpenUnitInv
attribute [local irreducible] moduleJAdj

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem restriction_square_factor {U T V W Z : Scheme.{u}}
    (s : U ⟶ T) (a : T ⟶ W) (b : T ⟶ V) (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z)
    (ek : s ≫ b = k) (er : s ≫ a = r) (h : a ≫ i = b ≫ p)
    (w : k ≫ p = r ≫ i) :
    Functor.isoWhiskerLeft (modulePullback B p) (moduleCompEq B s b k ek) ≪≫
        Functor.isoWhiskerRight (moduleSquareG B a b i p h) (modulePullback B s) ≪≫
        (Functor.isoWhiskerLeft (modulePullback B i) (moduleCompEq B s a r er)).symm =
      (moduleSquareG B k r p i w).symm := by
  have hs : s ≫ (b ≫ p) = k ≫ p := by rw [← Category.assoc, ek]
  have h₁ := moduleCompEq_coherence B s b p k (b ≫ p) (k ≫ p) ek rfl rfl hs
  have h₂ := moduleCompEq_coherence B s a i r (b ≫ p) (k ≫ p) er h w.symm hs
  have hb : moduleSquareG B a b i p h =
      (moduleCompEq B b p (b ≫ p) rfl).symm ≪≫ moduleCompEq B a i (b ≫ p) h := by
    rw [moduleSquareG_eq]
    simp only [moduleCompEq, eqToIso_refl, Iso.refl_trans]
  have hw : (moduleSquareG B k r p i w).symm =
      (moduleCompEq B k p (k ≫ p) rfl).symm ≪≫ moduleCompEq B r i (k ≫ p) w.symm := by
    rw [moduleSquareG_eq]
    simp only [moduleCompEq, Iso.trans_symm, Iso.symm_symm_eq, eqToIso_refl,
      Iso.refl_trans, Iso.trans_assoc]
    rfl
  rw [hb, hw, Functor.isoWhiskerRight_trans, ← Functor.isoWhiskerRight_symm]
  apply Iso.ext
  apply (cancel_epi (moduleCompEq B k p (k ≫ p) rfl).hom).mp
  apply (cancel_mono
    (Functor.isoWhiskerLeft (modulePullback B i) (moduleCompEq B s a r er)).hom).mp
  have he₁ := congrArg Iso.hom h₁
  have he₂ := congrArg Iso.hom h₂
  simp only [Iso.trans_hom, Iso.symm_hom] at he₁ he₂ ⊢
  simp only [Category.assoc, Iso.inv_hom_id, Iso.hom_inv_id_assoc, Category.comp_id]
  slice_lhs 1 2 => rw [← he₁]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact he₂

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem square_lift_projector {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (N : Modules B (pullback p i)) :
    (modulePullback B (squareLift k r p i h)).map
      ((clopenModulePi B (squareLift k r p i h)).app N) =
      (moduleJAdj B (squareLift k r p i h)).unit.app
        ((modulePullback B (squareLift k r p i h)).obj N) := by
  obtain ⟨C, c, hc, hc'⟩ := (properOpen_clopen_geometry k r p i h).2.2.2.2
  have := hc
  exact (clopenModule_section_projector B (squareLift k r p i h) c hc').2.1 N

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem restriction_beta_unit {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : a ≫ j = j' ≫ g)
    (sq : IsPullback a j' j g) (N : Modules B U) :
    (moduleJAdj B j').unit.app ((modulePullback B a).obj N) ≫
        (modulePullback B j').map ((openBetaModule B a j' j g w sq).inv.app N) =
      (modulePullback B a).map ((moduleJAdj B j).unit.app N) ≫
        (moduleSquareG B a j' j g w).inv.app ((moduleJ B j).obj N) := by
  simpa only [Adjunction.homEquiv_unit] using
    (openBetaModule_normalized B a j' j g w sq).2 N

private instance restriction_openUnitIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : IsIso (moduleJAdj B j).unit :=
  clopenModule_openUnit_isIso B j

private theorem beta_restriction {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g)
    (hsq : IsPullback a j' j g) (M : Modules B U) :
    (modulePullback B j').map ((openBetaModule B a j' j g h hsq).hom.app M) ≫
        inv ((moduleJAdj B j').unit.app ((modulePullback B a).obj M)) =
      (moduleSquareG B a j' j g h).hom.app ((moduleJ B j).obj M) ≫
        (modulePullback B a).map (inv ((moduleJAdj B j).unit.app M)) := by
  have hu := restriction_beta_unit B a j' j g h hsq M
  let u := asIso ((moduleJAdj B j').unit.app ((modulePullback B a).obj M))
  let v := (modulePullback B j').mapIso ((openBetaModule B a j' j g h hsq).app M)
  let z := (moduleSquareG B a j' j g h).app ((moduleJ B j).obj M)
  let w := (modulePullback B a).mapIso (asIso ((moduleJAdj B j).unit.app M))
  have he : u ≪≫ v.symm = w ≪≫ z.symm := Iso.ext hu
  have hi := congrArg (fun e ↦ e.inv) he
  simpa only [u, v, z, w, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, asIso_hom, asIso_inv,
    Iso.app_hom] using hi

private theorem jcomp_restriction {U T V : Scheme.{u}} (s : U ⟶ T) (b : T ⟶ V)
    [IsOpenImmersion s] [IsOpenImmersion b] (N : Modules B U) :
    (modulePullback B (s ≫ b)).map ((openBetaModuleJComp B s b).hom.app N) ≫
        inv ((moduleJAdj B (s ≫ b)).unit.app N) =
      (moduleGComp B s b).hom.app ((moduleJ B b).obj ((moduleJ B s).obj N)) ≫
        (modulePullback B s).map (inv ((moduleJAdj B b).unit.app
          ((moduleJ B s).obj N))) ≫ inv ((moduleJAdj B s).unit.app N) := by
  have hu := unit_conjugateEquiv ((moduleJAdj B s).comp (moduleJAdj B b))
    (moduleJAdj B (s ≫ b)) (openBetaModuleJComp B s b).inv N
  have hc : conjugateEquiv ((moduleJAdj B s).comp (moduleJAdj B b))
      (moduleJAdj B (s ≫ b)) (openBetaModuleJComp B s b).inv =
        (moduleGComp B s b).inv := by
    unfold openBetaModuleJComp
    exact Adjunction.conjugateEquiv_leftAdjointCompIso_inv
      (moduleJAdj B s) (moduleJAdj B b) (moduleJAdj B (s ≫ b))
      (moduleGComp B s b).symm
  rw [hc] at hu
  simp only [Adjunction.comp_unit_app, Functor.comp_obj, Functor.id_obj] at hu
  let e := asIso ((moduleJAdj B s).unit.app N) ≪≫
    (modulePullback B s).mapIso (asIso ((moduleJAdj B b).unit.app
      ((moduleJ B s).obj N))) ≪≫
    (moduleGComp B s b).symm.app ((moduleJ B b).obj ((moduleJ B s).obj N))
  let f := asIso ((moduleJAdj B (s ≫ b)).unit.app N) ≪≫
    (modulePullback B (s ≫ b)).mapIso ((openBetaModuleJComp B s b).symm.app N)
  have he : e = f := Iso.ext (by
    simpa only [e, f, Iso.trans_hom, asIso_hom, Functor.mapIso_hom,
      Iso.app_hom, Iso.symm_hom, Category.assoc] using hu)
  have hi := congrArg Iso.inv he
  simpa only [e, f, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
    asIso_inv, Iso.app_inv, Iso.app_hom, Iso.symm_hom, Category.assoc] using hi.symm

private theorem section_restriction {U T V W : Scheme.{u}}
    (s : U ⟶ T) (b : T ⟶ V) (a : T ⟶ W)
    [IsOpenImmersion s] [IsClosedImmersion s] [IsOpenImmersion b]
    (M : Modules B W)
    (hπ : ∀ N, (modulePullback B s).map ((clopenModulePi B s).app N) =
      (moduleJAdj B s).unit.app ((modulePullback B s).obj N)) :
    (modulePullback B (s ≫ b)).map
        ((moduleJ B b).map ((clopenModulePi B s).app ((modulePullback B a).obj M)) ≫
          (openBetaModuleJComp B s b).hom.app
            ((modulePullback B s).obj ((modulePullback B a).obj M)) ≫
          (moduleJ B (s ≫ b)).map ((moduleGComp B s a).inv.app M)) ≫
        inv ((moduleJAdj B (s ≫ b)).unit.app ((modulePullback B (s ≫ a)).obj M)) =
      (moduleGComp B s b).hom.app ((moduleJ B b).obj ((modulePullback B a).obj M)) ≫
        (modulePullback B s).map (inv ((moduleJAdj B b).unit.app ((modulePullback B a).obj M))) ≫
        (moduleGComp B s a).inv.app M := by
  have hn := (inv (moduleJAdj B (s ≫ b)).unit).naturality
    ((moduleGComp B s a).inv.app M)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, NatIso.isIso_inv_app] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [hn, reassoc_of% (jcomp_restriction B s b
    ((modulePullback B s).obj ((modulePullback B a).obj M)))]
  rw [reassoc_of% (moduleGComp B s b).hom.naturality
    ((moduleJ B b).map ((clopenModulePi B s).app ((modulePullback B a).obj M)))]
  have hb := (inv (moduleJAdj B b).unit).naturality
    ((clopenModulePi B s).app ((modulePullback B a).obj M))
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.id_map,
    NatIso.isIso_inv_app] at hb
  slice_lhs 2 3 => rw [← Functor.map_comp, hb, Functor.map_comp]
  simp only [hπ, Category.assoc, IsIso.hom_inv_id_assoc]

private theorem section_restriction_congr {U T V W : Scheme.{u}}
    (s : U ⟶ T) (b : T ⟶ V) (a : T ⟶ W) (k : U ⟶ V) (r : U ⟶ W)
    [IsOpenImmersion s] [IsClosedImmersion s] [IsOpenImmersion b] [IsOpenImmersion k]
    (ek : s ≫ b = k) (er : s ≫ a = r) (M : Modules B W)
    (hπ : ∀ N, (modulePullback B s).map ((clopenModulePi B s).app N) =
      (moduleJAdj B s).unit.app ((modulePullback B s).obj N)) :
    (modulePullback B k).map
        ((moduleJ B b).map ((clopenModulePi B s).app ((modulePullback B a).obj M)) ≫
          ((openBetaModuleJComp B s b).hom ≫ (singleJCongr B ek).hom).app
            ((modulePullback B s).obj ((modulePullback B a).obj M)) ≫
          (moduleJ B k).map (((moduleGComp B s a).inv ≫
            (eqToIso (congrArg (modulePullback B) er)).hom).app M)) ≫
        inv ((moduleJAdj B k).unit.app ((modulePullback B r).obj M)) =
      (moduleCompEq B s b k ek).hom.app
          ((moduleJ B b).obj ((modulePullback B a).obj M)) ≫
        (modulePullback B s).map (inv ((moduleJAdj B b).unit.app ((modulePullback B a).obj M))) ≫
        (moduleCompEq B s a r er).inv.app M := by
  subst k r
  unfold moduleCompEq
  simpa only [ singleJCongr_refl, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    NatTrans.comp_app, Category.comp_id, Iso.refl_trans] using
      section_restriction B s b a M hπ

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
    singleAlpha B k r p i w = factor
      (modulePullback B (pullback.snd p i)) (modulePullback B (squareLift k r p i w))
      (moduleJ B (squareLift k r p i w))
      (moduleJ B (pullback.fst p i)) (moduleJ B i ⋙ modulePullback B p)
      (modulePullback B r) (moduleJ B k)
      (openBetaModule B (pullback.snd p i) (pullback.fst p i) i p
        pullback.condition.symm (IsPullback.of_hasPullback p i).flip).hom
      (clopenModulePi B (squareLift k r p i w))
      ((openBetaModuleJComp B (squareLift k r p i w) (pullback.fst p i)).hom ≫
        (singleJCongr B (pullback.lift_fst k r w)).hom)
      ((moduleGComp B (squareLift k r p i w) (pullback.snd p i)).inv ≫
        (eqToIso (congrArg (modulePullback B) (pullback.lift_snd k r w))).hom) := by
  unfold singleAlpha factor
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
set_option backward.isDefEq.respectTransparency.types true in
private theorem alpha_calculation
    {U T V W Z : Scheme.{u}}
    (s : U ⟶ T) (a : T ⟶ W) (b : T ⟶ V) (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion b] [IsOpenImmersion i]
    (ek : s ≫ b = k) (er : s ≫ a = r) (h : a ≫ i = b ≫ p)
    (w : k ≫ p = r ≫ i) (hsq : IsPullback a b i p) (M : Modules B W) :
    let x := moduleCompEq B s b k ek
    let y := (moduleCompEq B s a r er).inv
    let β := (openBetaModule B a b i p h hsq).hom
    (modulePullback B k).map (β.app M) ≫
        x.hom.app ((moduleJ B b).obj ((modulePullback B a).obj M)) ≫
        (modulePullback B s).map (inv ((moduleJAdj B b).unit.app ((modulePullback B a).obj M))) ≫
        y.app M =
      (moduleSquareG B k r p i w).inv.app ((moduleJ B i).obj M) ≫
        (modulePullback B r).map (inv ((moduleJAdj B i).unit.app M)) := by
  exact functor_calculation (modulePullback B p) (modulePullback B i)
    (modulePullback B b) (modulePullback B a)
    (modulePullback B s) (modulePullback B k) (modulePullback B r) (moduleJ B b) (moduleJ B i)
    (moduleCompEq B s b k ek) (moduleCompEq B s a r er)
    (moduleSquareG B a b i p h) (moduleSquareG B k r p i w).symm
    (openBetaModule B a b i p h hsq).hom
    (fun N ↦ inv ((moduleJAdj B b).unit.app N))
    (fun N ↦ inv ((moduleJAdj B i).unit.app N))
    (beta_restriction B a b i p h hsq) (restriction_square_factor B s a b k r p i ek er h w) M

-- Apply the calculation to an arbitrary clopen factorization of alpha.
attribute [-instance] CategoryTheory.catToReflQuiver in
set_option backward.isDefEq.respectTransparency.types true in
private theorem factor_restriction
    {U T V W Z : Scheme.{u}}
    (s : U ⟶ T) (a : T ⟶ W) (b : T ⟶ V) (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion s] [IsClosedImmersion s] [IsOpenImmersion b]
    [IsOpenImmersion k] [IsOpenImmersion i]
    (ek : s ≫ b = k) (er : s ≫ a = r) (h : a ≫ i = b ≫ p)
    (w : k ≫ p = r ≫ i) (hsq : IsPullback a b i p) (M : Modules B W)
    (hπ : ∀ N, (modulePullback B s).map ((clopenModulePi B s).app N) =
      (moduleJAdj B s).unit.app ((modulePullback B s).obj N))
    (α : moduleJ B i ⋙ modulePullback B p ⟶ modulePullback B r ⋙ moduleJ B k)
    (ha : α = factor (modulePullback B a) (modulePullback B s) (moduleJ B s)
      (moduleJ B b) (moduleJ B i ⋙ modulePullback B p) (modulePullback B r) (moduleJ B k)
      (openBetaModule B a b i p h hsq).hom (clopenModulePi B s)
      ((openBetaModuleJComp B s b).hom ≫ (singleJCongr B ek).hom)
      ((moduleGComp B s a).inv ≫ (eqToIso (congrArg (modulePullback B) er)).hom)) :
    (modulePullback B k).map (α.app M) ≫
      inv ((moduleJAdj B k).unit.app ((modulePullback B r).obj M)) =
      (moduleSquareG B k r p i w).inv.app ((moduleJ B i).obj M) ≫
        (modulePullback B r).map (inv ((moduleJAdj B i).unit.app M)) := by
  let β := (openBetaModule B a b i p h hsq).hom
  have he := map_restriction (modulePullback B k) (α.app M) (β.app M)
    ((moduleJ B b).map ((clopenModulePi B s).app ((modulePullback B a).obj M)) ≫
      ((openBetaModuleJComp B s b).hom ≫ (singleJCongr B ek).hom).app
        ((modulePullback B s).obj ((modulePullback B a).obj M)) ≫
      (moduleJ B k).map (((moduleGComp B s a).inv ≫
        (eqToIso (congrArg (modulePullback B) er)).hom).app M))
    (inv ((moduleJAdj B k).unit.app ((modulePullback B r).obj M)))
    ((moduleCompEq B s b k ek).hom.app ((moduleJ B b).obj ((modulePullback B a).obj M)) ≫
      (modulePullback B s).map (inv ((moduleJAdj B b).unit.app ((modulePullback B a).obj M))) ≫
      (moduleCompEq B s a r er).inv.app M)
    ((NatTrans.congr_app ha M).trans (factor_app
      (modulePullback B a) (modulePullback B s) (moduleJ B s)
      (moduleJ B b) (moduleJ B i ⋙ modulePullback B p) (modulePullback B r) (moduleJ B k)
      (openBetaModule B a b i p h hsq).hom (clopenModulePi B s)
      ((openBetaModuleJComp B s b).hom ≫ (singleJCongr B ek).hom)
      ((moduleGComp B s a).inv ≫ (eqToIso (congrArg (modulePullback B) er)).hom) M))
    (section_restriction_congr B s b a k r ek er M hπ)
  exact he.trans (alpha_calculation B s a b k r p i ek er h w hsq M)

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Restriction of intrinsic alpha is the canonical square comparison followed
by the inverse open unit.
Source: Stacks, Tags 09BN and 0F7B; the underived restriction calculation in
`lem-cbc-proper-open-alpha-horizontal-modules`, proof steps 2--3.
(blueprint: lem-cbc-single-alpha-restriction)

Proof: write b for the first projection of W ×_T S, q for its second projection,
and s for the proper/open lift V → W ×_T S. Expand singleAlpha as cartesian beta,
then the clopen projector for s, then the open and inverse-image compositors.
The inverse-transpose equation defining beta identifies its restriction along b
with the inverse-image square comparison followed by q* of the inverse unit for i.
Restrict this equation along s. The clopen projector satisfies s*(pi_s)=unit_s,
so it cancels with the inverse unit introduced by restriction of the open compositor.
The compositor for the successive open adjunctions preserves their units; using
bs=k and qs=r leaves precisely the displayed square comparison. All comparisons
are the specified ones, so their associativity and equality transport identify the
result with moduleSquareG. This uses only one square and arbitrary coefficients;
for an empty open the same unit and projector equations hold. -/
theorem singleAlpha_restriction {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (M : Modules B S) :
    (modulePullback B k).map ((singleAlpha B k r p i h).app M) ≫
        (moduleOpenUnitInv B k).app ((modulePullback B r).obj M) =
      (moduleSquareG B k r p i h).inv.app ((moduleJ B i).obj M) ≫
        (modulePullback B r).map ((moduleOpenUnitInv B i).app M) := by
  have hh := factor_restriction B (squareLift k r p i h)
    (pullback.snd p i) (pullback.fst p i) k r p i
    (pullback.lift_fst k r h) (pullback.lift_snd k r h) pullback.condition.symm h
    (IsPullback.of_hasPullback p i).flip M (square_lift_projector B k r p i h)
    (singleAlpha B k r p i h) (alpha_factor B k r p i h)
  simpa only [moduleOpenUnitInv, NatIso.isIso_inv_app] using hh

end AlgebraicGeometry.ProEtale.StrictTower
