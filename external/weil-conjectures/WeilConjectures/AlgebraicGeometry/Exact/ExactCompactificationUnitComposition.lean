/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Exact.ExactCompactificationUnit
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.Exact.ExactCompactificationUnitRefinement
import WeilConjectures.AlgebraicGeometry.Exact.ExactCompactificationUnitTower

/-!
# Compatibility of normalized exact compact-support units with composition

Source: Stacks Project, Tags 0F7B, 0F7J and 0D6E
(blueprint: lem-sfb-exact-compactification-unit-composition).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private lemma unit_naturality
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (F H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (σ : F ≅ H)
    (a : H ≅ openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
      lowerStar (ModuleCat.{u + 1} A) c.g) :
    exactCompactificationUnit A c F (σ ≪≫ a) =
      (Functor.mapDerivedCategoryNatIso σ).hom ≫ exactCompactificationUnit A c H a := by
  apply Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (.up ℤ))
  intro K
  simp only [NatTrans.comp_app]
  unfold exactCompactificationUnit
  rw [normalizationLocalizationDesc_app, normalizationLocalizationDesc_app]
  simp only [Iso.trans_hom, NatTrans.mapHomotopyCategory_comp,
    Functor.whiskerRight_comp, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc]
  rw [← reassoc_of% (Functor.mapDerivedCategoryNatIso_fach σ K)]

private lemma invert_unit_square
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F F' : C ⥤ D} {G G' : D ⥤ E} {H H' : C ⥤ E}
    (a : F ≅ F') (b : G ≅ G') (c : H ≅ H') (t : F ⋙ G ≅ H)
    (k : F' ⋙ G' ≅ H')
    (h : Functor.whiskerRight a.inv G' ≫ Functor.whiskerLeft F b.inv ≫ t.hom =
      k.hom ≫ c.inv) :
    t ≪≫ c = Functor.isoWhiskerRight a G ≪≫ Functor.isoWhiskerLeft F' b ≪≫ k := by
  let s := Functor.isoWhiskerRight a G ≪≫ Functor.isoWhiskerLeft F' b
  have hs : Functor.whiskerRight a.inv G' ≫ Functor.whiskerLeft F b.inv = s.inv := by
    ext K
    exact b.inv.naturality (a.inv.app K)
  rw [← Category.assoc, hs] at h
  apply Iso.ext
  simp only [Iso.trans_hom]
  rw [← Category.assoc]
  change t.hom ≫ c.hom = s.hom ≫ k.hom
  apply (cancel_epi s.inv).1
  rw [← Category.assoc, h]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Iso.inv_hom_id_assoc]

set_option maxRecDepth 4096 in
/-- The inverse normalized units respect the proper/open composition map.
Source: Stacks Project, Tags 0F7B, 0F7J and 0D6E
(blueprint: lem-sfb-exact-compactification-unit-composition).

Proof: choose a compatible proper/open tower for h,e. On a homotopy representative J,
resolve j!J to I and then b!I to M. Proper direct image preserves K-injectives, so resolve
i!q*I to L and lift its proper/open comparison to p*M. Naturality of the section-preserving
sheaf identification and its normalization into ordinary direct image identify the two
paths after applying s*. The equality of resolution paths is precisely
properOpenTowerDerivedUnit. The composite b!j!J to b!I to M is a K-injective resolution
because b! is exact. The derived-composition normalization therefore identifies the
successive units with the single unit, after D(sigma). Localization descends the equality
on all representatives. Refinement compatibility transports it from the tower to the
chosen compactifications. Finally invert the three units and cancel their invertible
whiskerings. This gives exactly the displayed equation. -/
theorem exactCompactificationUnit_composition
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V T B : Scheme.{u}} [IsNoetherian V] [IsNoetherian T] [IsNoetherian B]
    (h : V ⟶ T) (e : T ⟶ B)
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} A))
    (H : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} A))
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (ιh : F ⟶ lowerStar (ModuleCat.{u + 1} A) h)
    (ιe : G ⟶ lowerStar (ModuleCat.{u + 1} A) e)
    (ιhe : H ⟶ lowerStar (ModuleCat.{u + 1} A) (h ≫ e))
    (ah : ∀ c : Compactification h, F ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g)
    (ae : ∀ c : Compactification e, G ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g)
    (ahe : ∀ c : Compactification (h ≫ e), H ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g)
    (nh : ∀ c, (ah c).hom ≫ compactificationSheafToDirectImage A c = ιh)
    (ne : ∀ c, (ae c).hom ≫ compactificationSheafToDirectImage A c = ιe)
    (nhe : ∀ c, (ahe c).hom ≫ compactificationSheafToDirectImage A c = ιhe)
    (ch : ∀ c : Compactification h,
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
        F.mapDerivedCategory)
    (ce : ∀ c : Compactification e,
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
        G.mapDerivedCategory)
    (che : ∀ c : Compactification (h ≫ e),
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
        H.mapDerivedCategory)
    (uh : ∀ c, (ch c).inv = exactCompactificationUnit A c F (ah c))
    (ue : ∀ c, (ce c).inv = exactCompactificationUnit A c G (ae c))
    (uhe : ∀ c, (che c).inv = exactCompactificationUnit A c H (ahe c))
    (σ : F ⋙ G ≅ H)
    (nσ : ∀ M, σ.hom.app M ≫ ιhe.app M =
      ιe.app (F.obj M) ≫ (lowerStar (ModuleCat.{u + 1} A) e).map (ιh.app M) ≫
        (lowerStarComp (ModuleCat.{u + 1} A) h e).hom.app M) :
    (unboundedEtaleLowerShriekCompIso A h e ≪≫
      (rightDerivedLowerShriekIso A
        (HasCompactification.compactification (h ≫ e))).symm ≪≫
      che (HasCompactification.compactification (h ≫ e))) =
    (Functor.isoWhiskerRight
        ((rightDerivedLowerShriekIso A
          (HasCompactification.compactification h)).symm ≪≫
          ch (HasCompactification.compactification h))
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) e) ≪≫
      Functor.isoWhiskerLeft F.mapDerivedCategory
        ((rightDerivedLowerShriekIso A
          (HasCompactification.compactification e)).symm ≪≫
          ce (HasCompactification.compactification e)) ≪≫
      Functor.mapDerivedCategoryCompIso F G ≪≫
      Functor.mapDerivedCategoryNatIso σ) := by
  let d := HasCompactification.compactification e
  let c := (HasCompactification.compactification (h ≫ e)).ofComp d
  let a := σ ≪≫ ahe (d.comp c)
  have na (M) : a.hom.app M ≫
      (compactificationSheafToDirectImage A (d.comp c)).app M =
      (ae d).hom.app (F.obj M) ≫
        (compactificationSheafToDirectImage A d).app (F.obj M) ≫
        (lowerStar (ModuleCat.{u + 1} A) e).map
          ((ah c.restrict).hom.app M ≫
            (compactificationSheafToDirectImage A c.restrict).app M) ≫
        (lowerStarComp (ModuleCat.{u + 1} A) h e).hom.app M := by
    have nhM := congr_app (nh c.restrict) M
    have neM := congr_app (ne d) (F.obj M)
    have nheM := congr_app (nhe (d.comp c)) M
    simp only [NatTrans.comp_app] at nhM neM nheM
    simp only [a, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
    rw [nheM, reassoc_of% neM, nhM]
    exact nσ M
  have ht := exactCompactificationUnit_tower A h e d c F G
    (ah c.restrict) (ae d) a na
  have hr := exactCompactificationUnit_refinement A h F c.restrict
    (HasCompactification.compactification h) (ah c.restrict)
    (ah (HasCompactification.compactification h)) (by rw [nh, nh])
  have hs := exactCompactificationUnit_refinement A (h ≫ e) H (d.comp c)
    (HasCompactification.compactification (h ≫ e)) (ahe (d.comp c))
    (ahe (HasCompactification.compactification (h ≫ e))) (by rw [nhe, nhe])
  let α := (rightDerivedLowerShriekIso A
    (HasCompactification.compactification h)).symm ≪≫
      ch (HasCompactification.compactification h)
  let β := (rightDerivedLowerShriekIso A d).symm ≪≫ ce d
  let γ := (rightDerivedLowerShriekIso A
    (HasCompactification.compactification (h ≫ e))).symm ≪≫
      che (HasCompactification.compactification (h ≫ e))
  have self (X Y : Scheme.{u}) [IsNoetherian X] [IsNoetherian Y]
      (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
      rightDerivedLowerShriekIso A (HasCompactification.compactification f) =
        Iso.refl _ :=
    (unboundedEtaleCompactSupport_comparison_coherence A f).1 _
  have hα : α.inv = exactCompactificationUnit A c.restrict F (ah c.restrict) ≫
      (rightDerivedLowerShriekIso A c.restrict).hom := by
    dsimp only [α, Iso.trans_inv, Iso.symm_inv]
    rw [uh, self, Iso.refl_hom, Category.comp_id]
    exact hr.symm
  have hβ : β.inv = exactCompactificationUnit A d G (ae d) := by
    dsimp only [β, Iso.trans_inv, Iso.symm_inv, d]
    rw [ue, self, Iso.refl_hom, Category.comp_id]
  have hγ : γ.inv = exactCompactificationUnit A (d.comp c) H (ahe (d.comp c)) ≫
      (rightDerivedLowerShriekIso A (d.comp c)).hom := by
    dsimp only [γ, Iso.trans_inv, Iso.symm_inv]
    rw [uhe, self, Iso.refl_hom, Category.comp_id]
    exact hs.symm
  apply invert_unit_square α β γ (unboundedEtaleLowerShriekCompIso A h e)
    (Functor.mapDerivedCategoryCompIso F G ≪≫
      Functor.mapDerivedCategoryNatIso σ)
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Iso.trans_hom]
  rw [hα, hγ]
  simp only [NatTrans.comp_app, Functor.map_comp, Category.assoc]
  simp only [unboundedEtaleLowerShriekCompIso, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerRight_app]
  change G.mapDerivedCategory.map
      ((exactCompactificationUnit A c.restrict F (ah c.restrict)).app K) ≫
    G.mapDerivedCategory.map ((rightDerivedLowerShriekIso A c.restrict).hom.app K) ≫
    β.inv.app ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) h).obj K) ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) e).map
      ((rightDerivedLowerShriekIso A c.restrict).inv.app K) ≫
    (rightDerivedLowerShriekOfCompactificationCompIso A d c).hom.app K ≫
    (rightDerivedLowerShriekIso A (d.comp c)).hom.app K = _
  rw [← β.inv.naturality_assoc]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app, Category.comp_id]
  rw [hβ]
  change G.mapDerivedCategory.map
      ((exactCompactificationUnit A c.restrict F (ah c.restrict)).app K) ≫
    (exactCompactificationUnit A d G (ae d)).app
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c.restrict).obj K) ≫
    (rightDerivedLowerShriekOfCompactificationCompIso A d c).hom.app K ≫
    (rightDerivedLowerShriekIso A (d.comp c)).hom.app K = _
  have htK := congr_app ht K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at htK
  have hpost := congrArg (fun t => t ≫
    (rightDerivedLowerShriekIso A (d.comp c)).hom.app K) htK
  simp only [Category.assoc] at hpost
  refine hpost.trans ?_
  rw [unit_naturality]
  simp only [NatTrans.comp_app, Category.assoc]

end AlgebraicGeometry.Etale
