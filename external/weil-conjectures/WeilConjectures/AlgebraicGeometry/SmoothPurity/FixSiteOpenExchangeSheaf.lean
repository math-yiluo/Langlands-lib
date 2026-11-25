/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
public import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionSquare
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.Open.OpenComparisonUnitNormalization
import WeilConjectures.AlgebraicGeometry.SmoothPurity.FixSiteOpenExchangeSquare

/-!
# The ordinary sheaf calculation for site comparison and open exchange

Source: Stacks Project, Tags 03S6, 09AF and 099R
(blueprint: lem-fix-site-open-exchange-sheaf).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits

private theorem exchange_mate_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {G : B ⥤ D} {GR : D ⥤ B} {H : A ⥤ C} {HR : C ⥤ A}
    (a : L ⊣ R) (b : L' ⊣ R') (c : G ⊣ GR) (d : H ⊣ HR)
    (s : R ⋙ H ⟶ G ⋙ R') (β : GR ⋙ R ⟶ R' ⋙ HR)
    (hβ : β = (mateEquiv c d (TwoSquare.mk _ _ _ _ s))) (F : A) :
    b.unit.app (H.obj F) ≫
        R'.map (((conjugateEquiv (a.comp c) (d.comp b)).symm β).app F) =
      H.map (a.unit.app F) ≫ s.app (L.obj F) := by
  apply (d.homEquiv _ _).injective
  have h := unit_conjugateEquiv_symm (a.comp c) (d.comp b) β F
  dsimp only [Functor.comp_obj, Functor.comp_map] at h
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app, Category.assoc] at h
  conv_lhs at h => rw [hβ, unit_mateEquiv]
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, Functor.map_comp,
    Adjunction.unit_naturality_assoc]
  exact (h.trans (Category.assoc _ _ _)).symm

private theorem transport_open_unit
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R S : D ⥤ C} {L' : C' ⥤ D'} {R' S' : D' ⥤ C'}
    (N : C ⥤ C') (M : D ⥤ D') (a : L ⊣ S) (b : L' ⊣ S')
    (r : R ≅ S) (r' : R' ≅ S') (c : L ⋙ M ≅ N ⋙ L')
    (t : M ⋙ R' ≅ R ⋙ N) (F : C)
    (h : N.map (a.unit.app F) ≫
      (N.map (r.inv.app (L.obj F)) ≫ t.inv.app (L.obj F) ≫
        r'.hom.app (M.obj (L.obj F))) ≫ S'.map (c.hom.app F) =
      b.unit.app (N.obj F)) :
    (b.ofNatIsoRight r'.symm).unit.app (N.obj F) ≫ R'.map (c.inv.app F) =
      N.map ((a.ofNatIsoRight r.symm).unit.app F) ≫ t.inv.app (L.obj F) := by
  change (b.unit.app (N.obj F) ≫ r'.inv.app (L'.obj (N.obj F))) ≫
    R'.map (c.inv.app F) =
      N.map (a.unit.app F ≫ r.inv.app (L.obj F)) ≫ t.inv.app (L.obj F)
  rw [← h, Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% (r'.inv.naturality (c.hom.app F))]
  simp only [← Functor.map_comp, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc]
  change N.map (a.unit.app F) ≫ N.map (r.inv.app (L.obj F)) ≫ t.inv.app (L.obj F) ≫
    R'.map (𝟙 (M.obj (L.obj F))) = _
  exact (congrArg
    (fun z ↦ N.map (a.unit.app F) ≫ N.map (r.inv.app (L.obj F)) ≫
      t.inv.app (L.obj F) ≫ z) (R'.map_id (M.obj (L.obj F)))).trans
    (congrArg (fun z ↦ N.map (a.unit.app F) ≫ N.map (r.inv.app (L.obj F)) ≫ z)
      (Category.comp_id (t.inv.app (L.obj F))))

private theorem exchange_comparison
    {C D E F P Q R S : Type*}
    [Category C] [Category D] [Category E] [Category F]
    [Category P] [Category Q] [Category R] [Category S]
    (a : C ⥤ D) (ar : D ⥤ C) (b : F ⥤ E) (br : E ⥤ F)
    (c : P ⥤ Q) (cr : Q ⥤ P) (d : S ⥤ R) (dr : R ⥤ S)
    (g : D ⥤ E) (h : C ⥤ F) (G : Q ⥤ R) (H : P ⥤ S)
    (NC : C ⥤ P) (ND : D ⥤ Q) (NE : E ⥤ R) (NF : F ⥤ S)
    (aa : a ⊣ ar) (ab : b ⊣ br) (ac : c ⊣ cr) (ad : d ⊣ dr)
    (cj : a ⋙ ND ≅ NC ⋙ c) (ck : b ⋙ NE ≅ NF ⋙ d)
    (ah : NC ⋙ H ≅ h ⋙ NF) (ag : ND ⋙ G ≅ g ⋙ NE)
    (aj : ND ⋙ cr ≅ ar ⋙ NC) (ak : NE ⋙ dr ≅ br ⋙ NF)
    (ep : c ⋙ G ≅ H ⋙ d) (ee : h ⋙ b ≅ a ⋙ g)
    (sp : cr ⋙ H ≅ G ⋙ dr) (se : ar ⋙ h ≅ g ⋙ br)
    (uj : ∀ X, ac.unit.app (NC.obj X) ≫ cr.map (cj.inv.app X) =
      NC.map (aa.unit.app X) ≫ aj.inv.app (a.obj X))
    (uk : ∀ X, ad.unit.app (NF.obj X) ≫ dr.map (ck.inv.app X) =
      NF.map (ab.unit.app X) ≫ ak.inv.app (b.obj X))
    (up : ∀ X, ad.unit.app (H.obj X) ≫ dr.map (ep.inv.app X) =
      H.map (ac.unit.app X) ≫ sp.hom.app (c.obj X))
    (ue : ∀ X, ab.unit.app (h.obj X) ≫ br.map (ee.hom.app X) =
      h.map (aa.unit.app X) ≫ se.hom.app (a.obj X))
    (sq : ∀ X, ah.inv.app (ar.obj X) ≫ H.map (aj.inv.app X) ≫
      sp.hom.app (ND.obj X) = NF.map (se.hom.app X) ≫
        ak.inv.app (g.obj X) ≫ dr.map (ag.inv.app X)) (X : C) :
    G.map (cj.hom.app X) ≫ ep.hom.app (NC.obj X) ≫ d.map (ah.hom.app X) =
      ag.hom.app (a.obj X) ≫ NE.map (ee.inv.app X) ≫ ck.hom.app (h.obj X) := by
  let el := G.mapIso (cj.app X) ≪≫ ep.app (NC.obj X) ≪≫ d.mapIso (ah.app X)
  let er := ag.app (a.obj X) ≪≫ NE.mapIso (ee.symm.app X) ≪≫ ck.app (h.obj X)
  change el.hom = er.hom
  apply (Iso.inv_eq_inv el er).mp
  apply (ad.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, el, er, Iso.trans_inv, Functor.mapIso_inv,
    Iso.app_inv, Iso.symm_inv, Functor.map_comp, Category.assoc]
  dsimp only [Functor.comp_obj] at *
  have hn := ad.unit.naturality (ah.inv.app X)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  erw [← reassoc_of% hn, reassoc_of% (up (NC.obj X))]
  have hs := sp.hom.naturality (cj.inv.app X)
  dsimp only [Functor.comp_map] at hs
  erw [← hs]
  have hu := congrArg H.map (uj X)
  simp only [Functor.map_comp] at hu
  erw [reassoc_of% hu]
  have ha := ah.inv.naturality (aa.unit.app X)
  dsimp only [Functor.comp_map] at ha
  erw [← reassoc_of% ha, reassoc_of% (uk (h.obj X))]
  have hb := ak.inv.naturality (ee.hom.app X)
  dsimp only [Functor.comp_map] at hb
  erw [← reassoc_of% hb]
  have he := congrArg NF.map (ue X)
  simp only [Functor.map_comp] at he
  erw [reassoc_of% he]
  simpa only [Category.assoc, Functor.comp_obj, Functor.id_obj] using congrArg
    (fun f ↦ NF.map (h.map (aa.unit.app X)) ≫ f) (sq (a.obj X))

namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false in
private theorem comparison_pullback_eq (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) :
    supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) j =
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) j).symm := by
  have hs : supportSiteComparisonSiteBaseChangeIso j = toProEtCompOverPullbackIso j := by
    ext W
    rfl
  unfold supportSiteComparisonCoefficientPullbackIso comparisonUpperStarCompUpperStarIso
  unfold supportSiteComparisonCoefficientDirectImageIso lowerStarCompComparisonLowerStarIso
  rw [hs]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem comparison_open_inverse_unit
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).obj F) ≫
      (upperStar (ModuleCat.{u + 1} Λ) j).map
        ((openImmersionLowerShriekComparisonUpperStarIso
          (ModuleCat.{u + 1} Λ) j).inv.app F) =
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).map
        ((Etale.openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} Λ) j).unit.app F) ≫
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) j).inv.app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).obj F) := by
  let A := ModuleCat.{u + 1} Λ
  apply transport_open_unit (comparisonUpperStar A U) (comparisonUpperStar A X)
    (Etale.openImmersionLowerShriekAdjunction A j)
    (openImmersionLowerShriekAdjunction A j)
    (Etale.upperStarIsoOpenImmersionRestriction A j)
    (upperStarIsoOpenImmersionRestriction A j)
    (openImmersionLowerShriekComparisonUpperStarIso A j)
    (comparisonUpperStarCompUpperStarIso A j) F
  have h := (openComparison_unit_normalization Λ j).2 F
  unfold openComparisonRestrictionIso at h
  rw [comparison_pullback_eq] at h
  dsimp only [A] at *
  simpa only [supportSiteComparisonCoefficientPullback, comparisonUpperStar,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.comp_app, Category.assoc] using h

private theorem pro_square_conjugate (Λ : Type (u + 1)) [CommRing Λ]
    {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {g : X' ⟶ X} (sq : CommSq gU j' j g) :
    conjugateIsoEquiv
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).comp
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j'))
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).comp
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) gU))
      (upperStarCompIso (ModuleCat.{u + 1} Λ) sq.w) =
        ProEtale.squareLowerStarIso (ModuleCat.{u + 1} Λ) sq := by
  rw [upperStarCompIso,
    conjugateIsoEquiv_trans _ (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (gU ≫ j)) _,
    conjugateIsoEquiv_trans _ (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (j' ≫ g)) _]
  rw [conjugateIsoEquiv_iso_symm,
    conjugateIsoEquiv_upperStarComp (ModuleCat.{u + 1} Λ) j' g,
    conjugateIsoEquiv_upperStarComp (ModuleCat.{u + 1} Λ) gU j,
    conjugateIsoEquiv_upperStarCongr (ModuleCat.{u + 1} Λ) sq.w]
  have key {Y Z : Scheme.{u}} {f g : Y ⟶ Z} (w : f = g) :
      (lowerStarCongr (ModuleCat.{u + 1} Λ) w).symm =
        lowerStarCongr (ModuleCat.{u + 1} Λ) w.symm := by
    subst w
    simp only [lowerStarCongr_rfl, Iso.refl_symm]
  simp only [ProEtale.squareLowerStarIso, Iso.trans_assoc, key]

private theorem pro_baseChange_eq_mate (Λ : Type (u + 1)) [CommRing Λ]
    {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {g : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : CommSq gU j' j g) :
    ProEtale.baseChangeMap (ModuleCat.{u + 1} Λ) sq =
      (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g)
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) gU)
        (TwoSquare.mk _ _ _ _
          (upperStarCompIso (ModuleCat.{u + 1} Λ) sq.w).hom)) := by
  let A := ModuleCat.{u + 1} Λ
  have h := iterated_mateEquiv_conjugateEquiv
    (upperStarLowerStarAdjunction A g) (upperStarLowerStarAdjunction A gU)
    (upperStarLowerStarAdjunction A j) (upperStarLowerStarAdjunction A j')
    (TwoSquare.mk _ _ _ _ (upperStarCompIso A sq.w).hom)
  have hc := congrArg Iso.hom (pro_square_conjugate Λ sq)
  rw [conjugateIsoEquiv_apply_hom] at hc
  rw [hc] at h
  change (((mateEquiv (upperStarLowerStarAdjunction A j')
    (upperStarLowerStarAdjunction A j)).symm
      (TwoSquare.mk _ _ _ _ (ProEtale.squareLowerStarIso A sq).hom))) = _
  apply (Equiv.symm_apply_eq _).mpr
  exact h.symm

/-- The ordinary exchange obtained by conjugating the canonical weakly etale
base-change map. Source: Stacks Project, Tag 03S6.
(blueprint: lem-fix-site-open-exchange-sheaf). -/
noncomputable def fixSiteOpenSheafExchangeIso
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (hsq : IsPullback gU j' j g) :
    openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j ⋙
        upperStar (ModuleCat.{u + 1} Λ) g ≅
      upperStar (ModuleCat.{u + 1} Λ) gU ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j' :=
  ((conjugateIsoEquiv
        ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).comp
          (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g))
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) gU).comp
          (openImmersionLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} Λ) j'))).symm
        (@asIso _ _ _ _ (ProEtale.baseChangeMap (ModuleCat.{u + 1} Λ) hsq.toCommSq)
          (ProEtale.isIso_baseChangeMap_of_isPullback (ModuleCat.{u + 1} Λ) hsq))).symm

/-- The inverse of the canonical ordinary exchange has the expected open-adjunction
transpose. Source: Stacks Project, Tag 03S6.
(blueprint: lem-fix-site-open-exchange-sheaf).

Proof: The composite-adjunction conjugation unit identity characterizes the inverse
exchange. The weakly etale base-change map is the iterated mate of the canonical
inverse-image square. Its mate unit identity and naturality reduce the composite
unit identity to the open unit identity, using injectivity of the pullback Hom
bijection. This includes arbitrary bottom maps, empty opens and the zero ring. -/
theorem fixSiteOpenSheafExchangeIso_unit (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {g : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion j']
    (hsq : IsPullback gU j' j g)
    (F : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ)) :
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j').unit.app
        ((upperStar (ModuleCat.{u + 1} Λ) gU).obj F) ≫
      (upperStar (ModuleCat.{u + 1} Λ) j').map
        ((fixSiteOpenSheafExchangeIso Λ gU j' j g hsq).inv.app F) =
    (upperStar (ModuleCat.{u + 1} Λ) gU).map
        ((openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} Λ) j).unit.app F) ≫
      (upperStarCompIso (ModuleCat.{u + 1} Λ) hsq.w).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).obj F) := by
  exact exchange_mate_unit
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j)
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j')
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) gU)
    (upperStarCompIso (ModuleCat.{u + 1} Λ) hsq.w).hom
    (ProEtale.baseChangeMap (ModuleCat.{u + 1} Λ) hsq.toCommSq)
    (pro_baseChange_eq_mate Λ hsq.toCommSq) F

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Site comparison intertwines the two specified ordinary sheaf exchanges.
Source: Stacks Project, Tag 03S6, with Tags 09AF and 099R.
(blueprint: lem-fix-site-open-exchange-sheaf).

Proof: Invert both composites and apply the Hom bijection for the pro-etale
open adjunction at j'. The inverse exchange is the transpose of the pulled-back
open unit followed by the inverse-image square comparison. The normalization of
the open comparison identifies the transpose of c_j inverse with N of the etale
unit followed by the canonical inverse-image comparison. Naturality moves that
unit to the beginning of both transposes. Their remaining factors agree by the
cartesian-square coherence of the canonical inverse-image comparison. Injectivity
of the Hom bijection and inversion give the equation. This is a calculation on
ordinary sheaves; localization and bounded-below restriction are not involved.
The same calculation includes empty opens, identity squares and the zero ring. -/
theorem fixSiteOpenExchangeSheaf (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {g : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : OpenImmersionSquare gU j' j g)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (upperStar (ModuleCat.{u + 1} Λ) g).map
        ((openImmersionLowerShriekComparisonUpperStarIso
          (ModuleCat.{u + 1} Λ) j).hom.app F) ≫
      (fixSiteOpenSheafExchangeIso Λ gU j' j g
        (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd)).hom.app
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).obj F) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j').map
        ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) gU).hom.app F) =
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g).hom.app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).obj F) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) X').map
        ((@asIso _ _ _ _ _ (Etale.isIso_openImmersionLowerShriekBaseChangeMap
          (ModuleCat.{u + 1} Λ)
          (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst
            sq.hom_snd))).inv.app F) ≫
    (openImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} Λ) j').hom.app
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) gU).obj F) := by
  have hsq : IsPullback gU j' j g :=
    IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
  exact exchange_comparison
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j)
    (Etale.upperStar (ModuleCat.{u + 1} Λ) j)
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j')
    (Etale.upperStar (ModuleCat.{u + 1} Λ) j')
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j) (upperStar (ModuleCat.{u + 1} Λ) j)
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j') (upperStar (ModuleCat.{u + 1} Λ) j')
    (Etale.upperStar (ModuleCat.{u + 1} Λ) g) (Etale.upperStar (ModuleCat.{u + 1} Λ) gU)
    (upperStar (ModuleCat.{u + 1} Λ) g) (upperStar (ModuleCat.{u + 1} Λ) gU)
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) U) (comparisonUpperStar (ModuleCat.{u + 1} Λ) X)
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) X') (comparisonUpperStar (ModuleCat.{u + 1} Λ) U')
    (Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j)
    (Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j')
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j)
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j')
    (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) j)
    (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) j')
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) gU)
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g)
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) j)
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) j')
    (fixSiteOpenSheafExchangeIso Λ gU j' j g hsq)
    (@asIso _ _ _ _
      (Etale.openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq)
      (Etale.isIso_openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ) hsq))
    (upperStarCompIso (ModuleCat.{u + 1} Λ) sq.w)
    (Etale.squareUpperStarIso (ModuleCat.{u + 1} Λ) sq.toCommSq.flip)
    (comparison_open_inverse_unit Λ j) (comparison_open_inverse_unit Λ j')
    (fun E ↦ by
      -- Rewrite the witness explicitly to avoid unfolding the conjugated exchange.
      have hu := fixSiteOpenSheafExchangeIso_unit Λ hsq E
      have hw : upperStarCompIso (ModuleCat.{u + 1} Λ) hsq.w =
          upperStarCompIso (ModuleCat.{u + 1} Λ) sq.w :=
        congrArg (upperStarCompIso (ModuleCat.{u + 1} Λ)) (Subsingleton.elim _ _)
      rw [hw] at hu
      exact hu)
    (fun E ↦ by
      simpa only [asIso_hom] using
        Etale.unit_map_openImmersionLowerShriekBaseChangeMap_app
          (ModuleCat.{u + 1} Λ) sq.toCommSq E)
    (fixSiteOpenExchangeSquare Λ sq.toChosenCartesianSquare) F

end AlgebraicGeometry.ProEtale
