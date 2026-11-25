/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportGraphDerivedIsoSupplement
import WeilConjectures.AlgebraicGeometry.Etale.Graph.EtaleGraphCompactificationFactorization
import WeilConjectures.AlgebraicGeometry.Etale.Graph.EtaleGraphProperPostcomposition
import WeilConjectures.AlgebraicGeometry.Etale.Graph.EtaleGraphOpenEtaleComposition
import WeilConjectures.AlgebraicGeometry.Etale.Graph.EtaleGraphProperInterchange

/-! # The proper/etale graph interchange

Source: Stacks Project, Tags 0F4L, 0F7B and 0F7J.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] lowerStar upperStar etaleLowerShriek openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  canonicalEtaleCompactSupportComparison derivedEtaleLowerShriekUpperStarAdjunction
  derivedOpenImmersionLowerShriekUpperStarAdjunction mapDerivedUpperStarLowerStarAdjunction
  rightDerivedLowerShriekIso unboundedEtaleLowerShriekCompIso unboundedEtaleLowerShriekCongr

-- Match the model functor with the small derived direct-image wrapper.
set_option allowUnsafeReducibility true in
attribute [local reducible] rightDerivedLowerStar

private lemma graph_congr_refl
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    unboundedEtaleLowerShriekCongr A (rfl : f = f) = Iso.refl _ := by
  unfold unboundedEtaleLowerShriekCongr
  rfl

private lemma graph_congr_trans
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f g h : X ⟶ Y}
    [HasCompactification f] [HasCompactification g] [HasCompactification h]
    (a : f = g) (b : g = h) :
    unboundedEtaleLowerShriekCongr A a ≪≫ unboundedEtaleLowerShriekCongr A b =
      unboundedEtaleLowerShriekCongr A (a.trans b) := by
  cases a
  cases b
  simp only [graph_congr_refl, Iso.refl_trans]

private lemma graph_compositor_congr_right
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) {g h : Y ⟶ Z}
    [HasCompactification f] [HasCompactification g] [HasCompactification h]
    [HasCompactification (f ≫ g)] [HasCompactification (f ≫ h)]
    [QuasiCompact f] [QuasiCompact (f ≫ g)] [QuasiCompact (f ≫ h)] (a : g = h) :
    unboundedEtaleLowerShriekCompIso A f g ≪≫
        unboundedEtaleLowerShriekCongr A (congrArg (fun t ↦ f ≫ t) a) =
      Functor.isoWhiskerLeft (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
        (unboundedEtaleLowerShriekCongr A a) ≪≫
          unboundedEtaleLowerShriekCompIso A f h := by
  cases a
  simp only [graph_congr_refl, Functor.isoWhiskerLeft_refl,
    Iso.trans_refl, Iso.refl_trans]

private lemma graph_compositor_square
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X W Y' Z Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian W] [IsNoetherian Y']
    [IsNoetherian Z] [IsNoetherian Y]
    (j : X ⟶ W) [IsOpenImmersion j] [QuasiCompact j]
    (q : W ⟶ Y') [IsProper q]
    (v : Y' ⟶ Y) [Etale v] [IsSeparated v] [QuasiCompact v]
    (b : W ⟶ Z) [Etale b] [IsSeparated b] [QuasiCompact b]
    (p : Z ⟶ Y) [IsProper p]
    (f : X ⟶ Y') (r : X ⟶ Z) (hf : f = j ≫ q) (hr : r = j ≫ b)
    [HasCompactification f] [HasCompactification r]
    [QuasiCompact f] [QuasiCompact r]
    (h : q ≫ v = b ≫ p) (w : f ≫ v = r ≫ p) :
    Functor.isoWhiskerRight
        (unboundedEtaleLowerShriekCompIso A j q ≪≫
          unboundedEtaleLowerShriekCongr A hf.symm)
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) v) ≪≫
      (unboundedEtaleLowerShriekCompIso A f v ≪≫
        unboundedEtaleLowerShriekCongr A w) =
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (rightDerivedLowerShriek (ModuleCat.{u + 1} A) j)
        (unboundedEtaleLowerShriekCompIso A q v ≪≫
          unboundedEtaleLowerShriekCongr A h ≪≫
          (unboundedEtaleLowerShriekCompIso A b p).symm) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (unboundedEtaleLowerShriekCompIso A j b ≪≫
          unboundedEtaleLowerShriekCongr A hr.symm)
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) p) ≪≫
      unboundedEtaleLowerShriekCompIso A r p := by
  subst f
  subst r
  have ha := unboundedEtaleLowerShriekCompIso_assoc A j q v
  have hd := unboundedEtaleLowerShriekCompIso_assoc A j b p
  have e := graph_compositor_congr_right A j h
  have ht : unboundedEtaleLowerShriekCongr A w ≪≫
      unboundedEtaleLowerShriekCongr A (Category.assoc j b p) =
    unboundedEtaleLowerShriekCongr A (Category.assoc j q v) ≪≫
      unboundedEtaleLowerShriekCongr A (congrArg (fun t ↦ j ≫ t) h) := by
    rw [graph_congr_trans, graph_congr_trans]
  simp only [graph_congr_refl, Iso.trans_refl]
  apply Iso.ext
  apply (cancel_mono
    (unboundedEtaleLowerShriekCongr A (Category.assoc j b p)).hom).1
  have he := congrArg Iso.hom e
  have hht := congrArg Iso.hom ht
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_trans,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Category.assoc] at *
  rw [hht, reassoc_of% ha, he]
  rw [hd]
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Iso.inv_hom_id_app_assoc]

private lemma graph_formal_pasting
    {C D E F G : Type*}
    [Category C] [Category D] [Category E] [Category F] [Category G]
    {J₀ J : C ⥤ D} {Q₀ Q : D ⥤ E} {V₀ V : E ⥤ G}
    {B₀ B : D ⥤ F} {P₀ P : F ⥤ G} {T : C ⥤ E}
    {R₀ R : C ⥤ F} {U : C ⥤ G}
    (dj : J₀ ≅ J) (dq : Q₀ ≅ Q) (dv : V₀ ≅ V)
    (db : B₀ ≅ B) (dp : P₀ ≅ P) (dr : R₀ ≅ R)
    (tc : J ⋙ Q ≅ T) (s : J ⋙ B ≅ R) (k : R ⋙ P ≅ U)
    (cjq : J₀ ⋙ Q₀ ≅ T) (ctv : T ⋙ V₀ ≅ U)
    (cqb : Q₀ ⋙ V₀ ≅ B₀ ⋙ P₀) (cjb : J₀ ⋙ B₀ ≅ R₀)
    (crp : R₀ ⋙ P₀ ≅ U)
    (hfac : Functor.isoWhiskerRight dj Q₀ ≪≫
      Functor.isoWhiskerLeft J dq ≪≫ tc = cjq)
    (hgraph : Functor.isoWhiskerRight dj B₀ ≪≫
      Functor.isoWhiskerLeft J db ≪≫ s = cjb ≪≫ dr)
    (hpost : Functor.isoWhiskerRight dr.symm P ≪≫
      Functor.isoWhiskerLeft R₀ dp.symm ≪≫ crp = k)
    (hassoc : Functor.isoWhiskerRight cjq V₀ ≪≫ ctv =
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft J₀ cqb ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight cjb P₀ ≪≫ crp)
    (M : C) :
    V.map (tc.hom.app M) ≫
        (Functor.isoWhiskerLeft T dv.symm ≪≫ ctv).hom.app M =
      (Functor.isoWhiskerRight dq.symm V ≪≫
        Functor.isoWhiskerLeft Q₀ dv.symm ≪≫ cqb ≪≫
        Functor.isoWhiskerRight db P₀ ≪≫ Functor.isoWhiskerLeft B dp).hom.app
          (J.obj M) ≫ P.map (s.hom.app M) ≫ k.hom.app M := by
  have hf := congr_app (congrArg Iso.hom hfac) M
  have hg := congr_app (congrArg Iso.hom hgraph) M
  have hp := congr_app (congrArg Iso.hom hpost) M
  have ha := congr_app (congrArg Iso.hom hassoc) M
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp] at hf hg hp ha ⊢
  let a := dv.hom.app (Q₀.obj (J₀.obj M)) ≫
    V.map (Q₀.map (dj.hom.app M)) ≫ V.map (dq.hom.app (J.obj M))
  have : IsIso a := by dsimp only [a]; infer_instance
  apply (cancel_epi a).1
  have hl : a ≫ V.map (tc.hom.app M) ≫ dv.inv.app (T.obj M) ≫ ctv.hom.app M =
      V₀.map (cjq.hom.app M) ≫ ctv.hom.app M := by
    dsimp only [a]
    rw [Category.assoc, Category.assoc, ← V.map_comp_assoc,
      ← V.map_comp_assoc, Category.assoc, hf]
    rw [← dv.hom.naturality_assoc, Iso.hom_inv_id_app_assoc]
  have hr : a ≫ (V.map (dq.inv.app (J.obj M)) ≫
      dv.inv.app (Q₀.obj (J.obj M)) ≫ cqb.hom.app (J.obj M) ≫
      P₀.map (db.hom.app (J.obj M)) ≫ dp.hom.app (B.obj (J.obj M))) ≫
        P.map (s.hom.app M) ≫ k.hom.app M =
      cqb.hom.app (J₀.obj M) ≫ P₀.map (cjb.hom.app M) ≫ crp.hom.app M := by
    dsimp only [a]
    simp only [Category.assoc, ← V.map_comp_assoc, Iso.hom_inv_id_app,
      V.map_id, Category.id_comp]
    rw [← dv.hom.naturality_assoc, Iso.hom_inv_id_app_assoc]
    have hn := cqb.hom.naturality (dj.hom.app M)
    dsimp only [Functor.comp_map] at hn
    rw [reassoc_of% hn]
    rw [← reassoc_of% (dp.hom.naturality (s.hom.app M))]
    rw [← P₀.map_comp_assoc, ← P₀.map_comp_assoc, Category.assoc, hg, P₀.map_comp]
    rw [Category.assoc, dp.hom.naturality_assoc]
    rw [← hp]
    simp only [← P.map_comp_assoc, Iso.hom_inv_id_app,
      P.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc]
  simpa only [Category.assoc] using hl.trans (ha.trans hr.symm)

/-- Normalization of the proper-first composition with etale sum extension.
There is no upper open-square comparison in this equation: the only geometric
interchange is the Cartesian square of the proper maps c'.g and p.
Source: Stacks Project, more-etale.tex Tags 0F7B and 0F7F (proper/quasi-finite
interchange and change of base), Tag 0F7J (composition), and Tag 0F7L, final
proof paragraph item (3); etale-cohomology.tex Tag 0F4L (graph normalization).
(blueprint: lem-pur-etale-graph-proper-tower).

Proof in words:
Expand the composition of f' and v on a nested proper/open compactification
tower. Represent an input by a K-injective complex I, and resolve its extension
by zero before taking the next proper direct image. Tag 0F7B defines the
interchange by the common proper-support identification followed by direct
image of that resolution map. The common-support sheaf composition theorem
specifies this identification by its inclusion into ordinary direct image.
Transpose under inverse image and direct image for c'.g and p. On a lift
summand, restriction carries a sheet section to the same pulled-back sheet
section; off the clopen graph both sides vanish. Gluing and sheafification
identify this transpose with inverse sum exchange. Consequently its mate is
gam, with exactly the orientation below. The open factor is the sum/open
composite-adjunction comparison s. Apply the equal sheaf maps degreewise and
compose with the derived units. Naturality and the unit equation for derived
direct-image composition give the displayed composite k on homotopy
representatives. Localization extends it to all unbounded inputs. Graph
refinement coherence and the normalized refinement equation cancel the auxiliary
towers and leave e.postcomp p at the endpoint. Identity proper maps use the
direct-image unit equation; empty graphs and zero modules give zero maps. -/
theorem etaleGraph_proper_tower
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X' Y' Y Z : Scheme.{u}}
    [IsNoetherian X'] [IsNoetherian Y'] [IsNoetherian Y] [IsNoetherian Z]
    {f' : X' ⟶ Y'} {v : Y' ⟶ Y}
    [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    [Etale v] [IsSeparated v] [QuasiCompact v]
    [HasCompactification f'] [HasCompactification v]
    [HasCompactification (f' ≫ v)] [QuasiCompact (f' ≫ v)]
    (c' : Compactification f') (p : Z ⟶ Y) [IsProper p]
    (b : c'.Z ⟶ Z) [Etale b] [IsSeparated b]
    (psq : IsPullback b c'.g p v)
    (r : X' ⟶ Z) [Etale r] [IsSeparated r] [QuasiCompact r]
    (hr : r = c'.i ≫ b) (e : Compactification r)
    [HasCompactification (r ≫ p)]
    [IsIso (((mateEquiv
      (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v inferInstance)
      (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) b inferInstance)).symm
      (TwoSquare.mk _ _ _ _ (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A)
        psq.toCommSq).hom)))]
    (M : DerivedCategoryModule A X') :
    let ba := derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) b inferInstance
    let j'a := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) c'.i
    let s := (conjugateIsoEquiv
      (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) r inferInstance)
      (j'a.comp ba)).symm
      (Functor.mapDerivedCategoryNatIso
        (upperStarComp (ModuleCat.{u + 1} A) c'.i b r hr) ≪≫
        (Functor.mapDerivedCategoryCompIso _ _).symm)
    let sumEx := ((mateEquiv
      (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v inferInstance)
      ba).symm (TwoSquare.mk _ _ _ _
        (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) psq.toCommSq).hom))
    let gam := (mateEquiv
      (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c'.g)
      (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
      (TwoSquare.mk _ _ _ _ (inv sumEx)))
    let dv := (rightDerivedLowerShriekIso A
      (HasCompactification.compactification v)).symm ≪≫
      canonicalEtaleCompactSupportComparison A v (HasCompactification.compactification v)
    let w : f' ≫ v = r ≫ p :=
      (congrArg (fun h : X' ⟶ Y' ↦ h ≫ v) c'.comm).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun h ↦ c'.i ≫ h) psq.w.symm).trans
            ((Category.assoc _ _ _).symm.trans (congrArg (fun h ↦ h ≫ p) hr.symm))))
    let rho := Functor.isoWhiskerLeft
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f') dv.symm ≪≫
      unboundedEtaleLowerShriekCompIso A f' v ≪≫ unboundedEtaleLowerShriekCongr A w
    let k := Functor.isoWhiskerRight
      (canonicalEtaleCompactSupportComparison A r e).symm
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) p) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) e.i).mapDerivedCategory
        (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e.g p) ≪≫
      rightDerivedLowerShriekIso A (e.postcomp p)
    (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory.map
        ((rightDerivedLowerShriekIso A c').hom.app M) ≫ rho.hom.app M =
      gam.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c'.i).mapDerivedCategory.obj M) ≫
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) p).map (s.hom.app M) ≫ k.hom.app M := by
  let : IsLocallyNoetherian c'.Z := LocallyOfFiniteType.isLocallyNoetherian c'.g
  let : CompactSpace c'.Z := QuasiCompact.compactSpace_of_compactSpace c'.g
  let : IsNoetherian c'.Z := ⟨⟩
  let : QuasiCompact c'.i := c'.quasiCompact_openImmersion inferInstance
  let ba := derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) b inferInstance
  let j'a := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) c'.i
  let s := (conjugateIsoEquiv
    (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) r inferInstance)
    (j'a.comp ba)).symm
    (Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} A) c'.i b r hr) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm)
  let sumEx := ((mateEquiv
    (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v inferInstance)
    ba).symm (TwoSquare.mk _ _ _ _
      (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) psq.toCommSq).hom))
  let gam := (mateEquiv
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c'.g)
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
    (TwoSquare.mk _ _ _ _ (inv sumEx)))
  let dv := (rightDerivedLowerShriekIso A
    (HasCompactification.compactification v)).symm ≪≫
    canonicalEtaleCompactSupportComparison A v (HasCompactification.compactification v)
  let w : f' ≫ v = r ≫ p :=
    (congrArg (fun h : X' ⟶ Y' ↦ h ≫ v) c'.comm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun h ↦ c'.i ≫ h) psq.w.symm).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (fun h ↦ h ≫ p) hr.symm))))
  let rho := Functor.isoWhiskerLeft
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f') dv.symm ≪≫
    unboundedEtaleLowerShriekCompIso A f' v ≪≫ unboundedEtaleLowerShriekCongr A w
  let k := Functor.isoWhiskerRight
    (canonicalEtaleCompactSupportComparison A r e).symm
    (rightDerivedLowerStar (ModuleCat.{u + 1} A) p) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) e.i).mapDerivedCategory
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e.g p) ≪≫
    rightDerivedLowerShriekIso A (e.postcomp p)
  let dr := (rightDerivedLowerShriekIso A e).symm ≪≫
    canonicalEtaleCompactSupportComparison A r e
  let ct := unboundedEtaleLowerShriekCompIso A f' v ≪≫
    unboundedEtaleLowerShriekCongr A w
  let qb := unboundedEtaleLowerShriekCompIso A c'.g v ≪≫
    unboundedEtaleLowerShriekCongr A psq.w.symm ≪≫
    (unboundedEtaleLowerShriekCompIso A b p).symm
  let jb := unboundedEtaleLowerShriekCompIso A c'.i b ≪≫
    unboundedEtaleLowerShriekCongr A hr.symm
  have hf := graph_compactification_factorization A c'
  have hg₀ := graph_open_etale_composition A c'.i b r hr e
  have hp₀ := graph_proper_postcomposition A e p
  have hp : Functor.isoWhiskerRight dr.symm
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) p) ≪≫
      Functor.isoWhiskerLeft (rightDerivedLowerShriek (ModuleCat.{u + 1} A) r)
        (graphChosenProperComparison A p).symm ≪≫
      unboundedEtaleLowerShriekCompIso A r p = k := by
    apply Iso.ext
    apply NatTrans.ext
    funext K
    have hK := congr_app (congrArg Iso.hom hp₀) K
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app] at hK
    simp only [dr, k, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
      NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
      Functor.map_comp, Category.id_comp, Category.assoc]
    rw [(graphChosenProperComparison A p).inv.naturality_assoc, hK]
    simp only [Category.assoc, Category.id_comp]
    erw [(graphChosenProperComparison A p).inv_hom_id_app_assoc]
  have ha := graph_compositor_square A c'.i c'.g v b p f' r c'.comm hr psq.w.symm w
  have hh := graph_formal_pasting
    (graphChosenOpenComparison A c'.i) (graphChosenProperComparison A c'.g)
    (graphChosenEtaleComparison A v) (graphChosenEtaleComparison A b)
    (graphChosenProperComparison A p) dr (rightDerivedLowerShriekIso A c') s k
    (unboundedEtaleLowerShriekCompIso A c'.i c'.g ≪≫
      unboundedEtaleLowerShriekCongr A c'.comm.symm) ct qb jb
    (unboundedEtaleLowerShriekCompIso A r p) hf
    (by simpa only [jb, dr, Iso.trans_assoc] using hg₀) hp ha M
  have hγ := graph_proper_interchange A c'.g p b v psq
  have hγ' : (Functor.isoWhiskerRight (graphChosenProperComparison A c'.g).symm
      (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft (rightDerivedLowerShriek (ModuleCat.{u + 1} A) c'.g)
        (graphChosenEtaleComparison A v).symm ≪≫ qb ≪≫
      Functor.isoWhiskerRight (graphChosenEtaleComparison A b)
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) p) ≪≫
      Functor.isoWhiskerLeft
        (etaleLowerShriek (ModuleCat.{u + 1} A) b inferInstance).mapDerivedCategory
        (graphChosenProperComparison A p)).hom = gam := by
    simpa only [qb, Iso.trans_assoc] using hγ
  rw [hγ'] at hh
  unfold graphChosenEtaleComparison at hh
  exact hh

end AlgebraicGeometry.Etale
