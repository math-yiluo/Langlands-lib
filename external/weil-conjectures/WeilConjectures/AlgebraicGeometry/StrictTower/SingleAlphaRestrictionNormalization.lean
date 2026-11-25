/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOrdinaryProperOpenArrows
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOrdinaryProperOpenArrows
import all WeilConjectures.AlgebraicGeometry.StrictTower.TowerOpenBetaNormalization
import all WeilConjectures.CategoryTheory.SmoothPurity.ProperOpenCompositeTransformation

/-! # Restriction of intrinsic proper/open alpha

Source: Stacks Project, Tags 09BN and 0F7C, with the arbitrary-ring underived refinement.
(blueprint: lem-cbc-single-alpha-restriction-normalization)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option linter.unusedSimpArgs false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.StrictTower
variable (B : Type (u + 1)) [CommRing B]

attribute [local irreducible] Functor.leftAdjoint modulePullback singleAlpha moduleGComp
  moduleSquareG moduleJAdj clopenModulePi openBetaModule openBetaModuleJComp
  singleJCongr

private theorem open_comp_unit {U V X : Scheme.{u}} (s : U ⟶ V) (b : V ⟶ X)
    [IsOpenImmersion s] [IsOpenImmersion b] (N : Modules B U) :
    (moduleJAdj B (s ≫ b)).unit.app N ≫
        (moduleGComp B s b).hom.app ((moduleJ B (s ≫ b)).obj N) =
      (moduleJAdj B s).unit.app N ≫
        (modulePullback B s).map ((moduleJAdj B b).unit.app ((moduleJ B s).obj N)) ≫
        (modulePullback B s).map ((modulePullback B b).map
          ((openBetaModuleJComp B s b).hom.app N)) := by
  have hu := unit_conjugateEquiv_symm (moduleJAdj B (s ≫ b))
    ((moduleJAdj B s).comp (moduleJAdj B b)) (moduleGComp B s b).hom N
  simpa only [openBetaModuleJComp, Adjunction.leftAdjointCompIso_hom,
    Adjunction.leftAdjointCompNatTrans, Iso.symm_inv, Adjunction.comp_unit_app,
    Functor.comp_map, Category.assoc] using hu

private theorem cartesian_beta_restriction {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : a ≫ j = j' ≫ g)
    (sq : IsPullback a j' j g) (M : Modules B U) :
    (moduleSquareG B a j' j g w).inv.app ((moduleJ B j).obj M) ≫
        (modulePullback B j').map ((openBetaModule B a j' j g w sq).hom.app M) =
      (modulePullback B a).map
        ((@asIso _ _ _ _ (moduleJAdj B j).unit
          (clopenModule_openUnit_isIso B j)).inv.app M) ≫
        (moduleJAdj B j').unit.app ((modulePullback B a).obj M) := by
  have hj := clopenModule_openUnit_isIso B j
  have hj' := clopenModule_openUnit_isIso B j'
  have ht := (openBetaModule_normalized B a j' j g w sq).2 M
  rw [Adjunction.homEquiv_unit] at ht
  apply (Iso.cancel_iso_hom_left ((modulePullback B a).mapIso
    ((asIso (moduleJAdj B j).unit).app M)) _ _).1
  simp only [Functor.mapIso_hom, Iso.app_hom, asIso_hom]
  rw [← Category.assoc, ← ht]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  have hc : (moduleJAdj B j).unit.app M ≫ (asIso (moduleJAdj B j).unit).inv.app M =
      𝟙 _ := (asIso (moduleJAdj B j).unit).hom_inv_id_app M
  rw [← (modulePullback B a).map_comp_assoc, hc]
  simp only [Functor.comp_obj, Functor.id_obj, CategoryTheory.Functor.map_id,
    Category.comp_id, Category.id_comp]

private theorem cartesian_beta_restriction_cancelled {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : a ≫ j = j' ≫ g)
    (sq : IsPullback a j' j g) (M : Modules B U) :
    (modulePullback B j').map ((openBetaModule B a j' j g w sq).hom.app M) ≫
        ((@asIso _ _ _ _ (moduleJAdj B j').unit
          (clopenModule_openUnit_isIso B j')).inv.app ((modulePullback B a).obj M)) =
      (moduleSquareG B a j' j g w).hom.app ((moduleJ B j).obj M) ≫
        (modulePullback B a).map
          ((@asIso _ _ _ _ (moduleJAdj B j).unit
            (clopenModule_openUnit_isIso B j)).inv.app M) := by
  have hj := clopenModule_openUnit_isIso B j
  have hj' := clopenModule_openUnit_isIso B j'
  apply (Iso.cancel_iso_hom_left
    ((moduleSquareG B a j' j g w).symm.app ((moduleJ B j).obj M)) _ _).1
  simp only [Iso.app_hom, Iso.symm_hom]
  rw [← Category.assoc, cartesian_beta_restriction B a j' j g w sq M]
  simp only [Category.assoc, asIso_hom, Iso.inv_hom_id_app_assoc]
  have hc := (asIso (moduleJAdj B j').unit).hom_inv_id_app
    ((modulePullback B a).obj M)
  simpa only [asIso_hom, Functor.id_obj, Functor.comp_obj, Category.assoc,
    Category.comp_id] using
    congrArg (fun t ↦ (modulePullback B a).map
      ((@asIso _ _ _ _ (moduleJAdj B j).unit
        (clopenModule_openUnit_isIso B j)).inv.app M) ≫ t) hc

private theorem open_comp_congr_unit {U V X : Scheme.{u}}
    (s : U ⟶ V) (b : V ⟶ X) (k : U ⟶ X)
    [IsOpenImmersion s] [IsOpenImmersion b] [IsOpenImmersion k]
    (w : s ≫ b = k) (N : Modules B U) :
    (moduleJAdj B k).unit.app N ≫
        (moduleCompEq B s b k w).hom.app ((moduleJ B k).obj N) =
      (moduleJAdj B s).unit.app N ≫
        (modulePullback B s).map ((moduleJAdj B b).unit.app ((moduleJ B s).obj N)) ≫
        (modulePullback B s).map ((modulePullback B b).map
          (((openBetaModuleJComp B s b) ≪≫ singleJCongr B w).hom.app N)) := by
  subst k
  simp only [Iso.trans_hom, NatTrans.comp_app, singleJCongr_refl, NatTrans.id_app,
    Category.comp_id, moduleCompEq, eqToIso_refl, Iso.refl_trans]
  exact open_comp_unit B s b N

private theorem open_comp_congr_unit_iso {U V X : Scheme.{u}}
    (s : U ⟶ V) (b : V ⟶ X) (k : U ⟶ X)
    [IsOpenImmersion s] [IsOpenImmersion b] [IsOpenImmersion k]
    (w : s ≫ b = k) (N : Modules B U) :
    (@asIso _ _ _ _ (moduleJAdj B k).unit
        (clopenModule_openUnit_isIso B k)).hom.app N ≫
        (moduleCompEq B s b k w).hom.app ((moduleJ B k).obj N) =
      (@asIso _ _ _ _ (moduleJAdj B s).unit
        (clopenModule_openUnit_isIso B s)).hom.app N ≫
        (modulePullback B s).map
          ((@asIso _ _ _ _ (moduleJAdj B b).unit
            (clopenModule_openUnit_isIso B b)).hom.app ((moduleJ B s).obj N)) ≫
        (modulePullback B s).map ((modulePullback B b).map
          (((openBetaModuleJComp B s b) ≪≫ singleJCongr B w).hom.app N)) := by
  simpa only [asIso_hom] using open_comp_congr_unit B s b k w N

private theorem clopen_projector_restriction_iso {U X C : Scheme.{u}}
    (s : U ⟶ X) (c : C ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s]
    [IsOpenImmersion c] (hc : Set.range c = (Set.range s)ᶜ) (N : Modules B X) :
    (modulePullback B s).map ((clopenModulePi B s).app N) =
      (@asIso _ _ _ _ (moduleJAdj B s).unit
        (clopenModule_openUnit_isIso B s)).hom.app ((modulePullback B s).obj N) := by
  simpa only [asIso_hom] using (clopenModule_section_projector B s c hc).2.1 N

private theorem square_factorization_coherence {V W S T Z : Scheme.{u}}
    (s : V ⟶ Z) (b : Z ⟶ W) (q : Z ⟶ S)
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    (hsb : s ≫ b = k) (hsq : s ≫ q = r)
    (hqb : q ≫ i = b ≫ p) (h : k ≫ p = r ≫ i) (N : Modules B T) :
    (moduleSquareG B k r p i h).hom.app N ≫
        (moduleCompEq B s b k hsb).hom.app ((modulePullback B p).obj N) ≫
        (modulePullback B s).map ((moduleSquareG B q b i p hqb).hom.app N) =
      (moduleCompEq B s q r hsq).hom.app ((modulePullback B i).obj N) := by
  let w : s ≫ (q ≫ i) = k ≫ p := by rw [← Category.assoc, hsq, ← h]
  have h₁ := congr_app (congrArg Iso.hom
    (moduleCompEq_coherence B s b p k (q ≫ i) (k ≫ p) hsb hqb.symm rfl w)) N
  have h₂ := congr_app (congrArg Iso.hom
    (moduleCompEq_coherence B s q i r (q ≫ i) (k ≫ p) hsq rfl h.symm w)) N
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h₁ h₂
  have hσ := congr_app (congrArg Iso.hom (moduleSquare_normalize B k r p i h)) N
  have hτ := congrArg (modulePullback B s).map
    (congr_app (congrArg Iso.hom (moduleSquare_normalize B q b i p hqb)) N)
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app] at hσ
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp] at hτ
  exact cancel_factorization_word
    ((moduleCompEq B r i (k ≫ p) h.symm).app N)
    ((moduleCompEq B k p (k ≫ p) rfl).app N)
    ((moduleCompEq B s b k hsb).app ((modulePullback B p).obj N))
    ((moduleCompEq B s (q ≫ i) (k ≫ p) w).app N)
    ((modulePullback B s).mapIso ((moduleCompEq B b p (q ≫ i) hqb.symm).app N))
    ((modulePullback B s).mapIso ((moduleCompEq B q i (q ≫ i) rfl).app N))
    ((moduleCompEq B s q r hsq).app ((modulePullback B i).obj N))
    _ _ hσ hτ h₁ h₂

private theorem compEq_eq_symm {U V X : Scheme.{u}} (s : U ⟶ V) (q : V ⟶ X)
    (r : U ⟶ X) (w : s ≫ q = r) :
    moduleCompEq B s q r w =
      ((moduleGComp B s q).symm ≪≫ eqToIso (congrArg (modulePullback B) w)).symm := by
  subst r
  rw [← moduleCompEq_refl B s q]
  simp only [eqToIso_refl, Iso.trans_refl, Iso.symm_symm_eq]

private theorem square_factorization_coherence_normalized {V W S T Z : Scheme.{u}}
    (s : V ⟶ Z) (b : Z ⟶ W) (q : Z ⟶ S)
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    (hsb : s ≫ b = k) (hsq : s ≫ q = r)
    (hqb : q ≫ i = b ≫ p) (h : k ≫ p = r ≫ i) (N : Modules B T) :
    (moduleSquareG B k r p i h).hom.app N ≫
        (moduleCompEq B s b k hsb).hom.app ((modulePullback B p).obj N) ≫
        (modulePullback B s).map ((moduleSquareG B q b i p hqb).hom.app N) =
      (((moduleGComp B s q).symm ≪≫
        eqToIso (congrArg (modulePullback B) hsq)).symm).hom.app
          ((modulePullback B i).obj N) := by
  exact (square_factorization_coherence B s b q k r p i hsb hsq hqb h N).trans
    (congrArg (fun e : modulePullback B r ≅ modulePullback B q ⋙ modulePullback B s ↦
      e.hom.app ((modulePullback B i).obj N))
      (compEq_eq_symm B s q r hsq))

private theorem singleAlpha_word {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    singleAlpha B k r p i h =
    Functor.properOpenCompositeTransformation
    (Modules B S) (Modules B W) (Modules B (pullback p i)) (Modules B V) (Modules B T)
    (moduleJ B i) (modulePullback B p) (modulePullback B (pullback.snd p i))
    (modulePullback B (squareLift k r p i h)) (moduleJ B (squareLift k r p i h))
    (moduleJ B (pullback.fst p i)) (moduleJ B k) (modulePullback B r)
    (openBetaModule B (pullback.snd p i) (pullback.fst p i) i p
      pullback.condition.symm (IsPullback.of_hasPullback p i).flip).hom
    (clopenModulePi B (squareLift k r p i h))
    ((openBetaModuleJComp B (squareLift k r p i h) (pullback.fst p i)) ≪≫
      singleJCongr B (pullback.lift_fst k r h)).hom
    (((moduleGComp B (squareLift k r p i h) (pullback.snd p i)).symm ≪≫
      eqToIso (congrArg (modulePullback B) (pullback.lift_snd k r h))).symm).inv := by
  unfold singleAlpha Functor.properOpenCompositeTransformation
  rfl

private theorem factorization_restriction_iso {V W S T Z C : Scheme.{u}}
    (s : V ⟶ Z) (b : Z ⟶ W) (q : Z ⟶ S)
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T) (c : C ⟶ Z)
    [IsOpenImmersion s] [IsClosedImmersion s] [IsOpenImmersion b]
    [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion c]
    (hk : s ≫ b = k) (hr : s ≫ q = r) (w : q ≫ i = b ≫ p)
    (h : k ≫ p = r ≫ i) (sq : IsPullback q b i p)
    (hcomp : Set.range c = (Set.range s)ᶜ)
    (α : moduleJ B i ⋙ modulePullback B p ⟶ modulePullback B r ⋙ moduleJ B k)
    (ha : α = Functor.properOpenCompositeTransformation
      (Modules B S) (Modules B W) (Modules B Z) (Modules B V) (Modules B T)
      (moduleJ B i) (modulePullback B p) (modulePullback B q)
      (modulePullback B s) (moduleJ B s) (moduleJ B b) (moduleJ B k)
      (modulePullback B r) (openBetaModule B q b i p w sq).hom (clopenModulePi B s)
      ((openBetaModuleJComp B s b) ≪≫ singleJCongr B hk).hom
      (((moduleGComp B s q).symm ≪≫
        eqToIso (congrArg (modulePullback B) hr)).symm).inv)
    (M : Modules B S) :
    (moduleSquareG B k r p i h).hom.app ((moduleJ B i).obj M) ≫
        (modulePullback B k).map (α.app M) =
      (modulePullback B r).map
        ((@asIso _ _ _ _ (moduleJAdj B i).unit
          (clopenModule_openUnit_isIso B i)).inv.app M) ≫
        (@asIso _ _ _ _ (moduleJAdj B k).unit
          (clopenModule_openUnit_isIso B k)).hom.app ((modulePullback B r).obj M) := by
  let eβ := openBetaModule B q b i p w sq
  let cj := openBetaModuleJComp B s b ≪≫ singleJCongr B hk
  let cg := moduleCompEq B s b k hk
  let cr := ((moduleGComp B s q).symm ≪≫
    eqToIso (congrArg (modulePullback B) hr)).symm
  have hu := clopenModule_openUnit_isIso B s
  have hb := clopenModule_openUnit_isIso B b
  have hku := clopenModule_openUnit_isIso B k
  let us := asIso (moduleJAdj B s).unit
  let ub := asIso (moduleJAdj B b).unit
  let uk := asIso (moduleJAdj B k).unit
  have hd := clopen_projector_restriction_iso B s c hcomp
  have ht := restriction_normalization_word
    (moduleJ B i) (modulePullback B i) (modulePullback B p) (modulePullback B q)
    (modulePullback B s) (moduleJ B s) (moduleJ B b) (modulePullback B b)
    (moduleJ B k) (modulePullback B r) (modulePullback B k)
    eβ (clopenModulePi B s) α
    (moduleSquareG B k r p i h) (moduleSquareG B q b i p w)
    cg cj cr us ub uk
    (@asIso _ _ _ _ (moduleJAdj B i).unit (clopenModule_openUnit_isIso B i))
    hd
    (fun N ↦ open_comp_congr_unit_iso B s b k hk N)
    (fun N ↦ cartesian_beta_restriction_cancelled B q b i p w
      sq N)
    (fun N ↦ square_factorization_coherence_normalized B s b q k r p i hk hr w h N)
    (fun N ↦ (congr_app ha N).trans
      (Functor.properOpenCompositeTransformation_app
        (Modules B S) (Modules B W) (Modules B Z) (Modules B V) (Modules B T)
        (moduleJ B i) (modulePullback B p) (modulePullback B q)
        (modulePullback B s) (moduleJ B s) (moduleJ B b) (moduleJ B k)
        (modulePullback B r) eβ.hom (clopenModulePi B s) cj.hom cr.inv N)) M
  exact ht

private theorem singleAlpha_restriction_iso {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (M : Modules B S) :
    (moduleSquareG B k r p i h).hom.app ((moduleJ B i).obj M) ≫
        (modulePullback B k).map ((singleAlpha B k r p i h).app M) =
      (modulePullback B r).map
        ((@asIso _ _ _ _ (moduleJAdj B i).unit
          (clopenModule_openUnit_isIso B i)).inv.app M) ≫
        (@asIso _ _ _ _ (moduleJAdj B k).unit
          (clopenModule_openUnit_isIso B k)).hom.app ((modulePullback B r).obj M) := by
  let s := squareLift k r p i h
  let b := pullback.fst p i
  let q := pullback.snd p i
  have hk : s ≫ b = k := pullback.lift_fst k r h
  have hr : s ≫ q = r := pullback.lift_snd k r h
  have w : q ≫ i = b ≫ p := pullback.condition.symm
  obtain ⟨C, c, hc, hcomp⟩ := (properOpen_clopen_geometry k r p i h).2.2.2.2
  have : IsOpenImmersion c := hc
  exact factorization_restriction_iso B s b q k r p i c hk hr w h
    (IsPullback.of_hasPullback p i).flip hcomp (singleAlpha B k r p i h)
    (singleAlpha_word B k r p i h) M

/-- Restriction of the intrinsic clopen alpha, with its specified open units.
Source: Stacks Project, Tags 09BN and 0F7C; the restriction calculation in
lem-cbc-proper-open-alpha-vertical-modules, steps 2--3.
(blueprint: lem-cbc-single-alpha-restriction-normalization).
Proof: factor the square through W ×_T S, with open projection b and clopen lift s.
The inverse-transpose equation for cartesian beta identifies its restriction with
inverse image of the inverse unit for i. The clopen projector restricts along s to
the open unit. The unit-preserving compositor for s followed by b identifies the
resulting unit with the unit for k. The inverse-image square compositor cancels
all intermediate inverse-image compositors, giving the displayed equation.
The argument also holds for the empty open and the zero coefficient ring; for
identity opens it is exactly the unit equation for the inverse-image compositor. -/
theorem singleAlpha_restriction_normalized {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (M : Modules B S) :
    (moduleSquareG B k r p i h).hom.app ((moduleJ B i).obj M) ≫
        (modulePullback B k).map ((singleAlpha B k r p i h).app M) =
      (modulePullback B r).map
        ((@asIso _ _ _ _ (moduleJAdj B i).unit
          (clopenModule_openUnit_isIso B i)).inv.app M) ≫
        (moduleJAdj B k).unit.app ((modulePullback B r).obj M) := by
  simpa only [asIso_hom] using singleAlpha_restriction_iso B k r p i h M

end AlgebraicGeometry.ProEtale.StrictTower
