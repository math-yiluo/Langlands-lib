/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Open.OpenSupportPullbackModel
public import WeilConjectures.Compactification.RefinementOfIsPullback
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement

/-! # Proper/open exchange along one cartesian refinement
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStar lowerStar openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.mapDerivedCategoryNatIso
  mapDerivedCategoryOpenImmersionLowerShriekComp
  mapDerivedCategoryOpenImmersionLowerShriekCongr

private noncomputable abbrev supportPrecomp
    {X Y V : Scheme.{u}} {f : X ⟶ Y} (a : V ⟶ X) [IsOpenImmersion a]
    (c : Compactification f) : Compactification (a ≫ f) := c.precomp a

private noncomputable abbrev supportTriangleLeft
    {X Y U V : Scheme.{u}} {f : X ⟶ Y}
    {j : U ⟶ Y} [IsOpenImmersion j] {a : V ⟶ X} [IsOpenImmersion a]
    {p : V ⟶ U} (sq : IsPullback a p f j) (c : Compactification f) :
    Compactification.Triangle p j where
  cf := c.ofIsPullback sq
  cg := Compactification.ofIsOpenImmersion j
  cfg := (supportPrecomp a c).copy sq.w.symm
  q := pullback.fst c.g j
  p := c.g
  i_q := c.ofIsPullback_i_fst sq
  p_g := (Category.comp_id _)
  isPullback := (IsPullback.of_hasPullback c.g j).flip

private noncomputable abbrev supportTriangleRight
    {X Y V : Scheme.{u}} {f : X ⟶ Y} (a : V ⟶ X) [IsOpenImmersion a]
    (c : Compactification f) : Compactification.Triangle a f where
  cf := Compactification.ofIsOpenImmersion a
  cg := c
  cfg := supportPrecomp a c
  q := c.i
  p := 𝟙 c.Z
  i_q := rfl
  p_g := Category.id_comp _
  isPullback := by
    change IsPullback (𝟙 X) c.i c.i (𝟙 c.Z)
    exact IsPullback.of_horiz_isIso ⟨by simp⟩

private noncomputable def openSupportId
    (F : CompactSupportFormalism) {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    F.shriek (Compactification.ofIsOpenImmersion j) ≅ F.sh j :=
  Functor.isoWhiskerLeft _ (F.pfId Y) ≪≫ Functor.rightUnitor _

private noncomputable def supportLeft
    (F : CompactSupportFormalism) [F.HasProperExchange]
    {X Y U V : Scheme.{u}} {f : X ⟶ Y}
    {j : U ⟶ Y} [IsOpenImmersion j] {a : V ⟶ X} [IsOpenImmersion a]
    {p : V ⟶ U} (sq : IsPullback a p f j) (c : Compactification f) :
    F.shriek (c.ofIsPullback sq) ⋙ F.sh j ≅ F.shriek (supportPrecomp a c) :=
  Functor.isoWhiskerLeft _ (openSupportId F j).symm ≪≫
    F.compIso (supportTriangleLeft sq c)

private noncomputable def supportRight
    (F : CompactSupportFormalism) [F.HasProperExchange]
    {X Y V : Scheme.{u}} {f : X ⟶ Y} (a : V ⟶ X) [IsOpenImmersion a]
    (c : Compactification f) :
    F.sh a ⋙ F.shriek c ≅ F.shriek (supportPrecomp a c) :=
  Functor.isoWhiskerRight (openSupportId F a).symm _ ≪≫
    F.compIso (supportTriangleRight a c)

private lemma supportRight_hom_app
    (F : CompactSupportFormalism) [F.HasProperExchange]
    {X Y V : Scheme.{u}} {f : X ⟶ Y} (a : V ⟶ X) [IsOpenImmersion a]
    (c : Compactification f) (K : F.obj V) :
    (supportRight F a c).hom.app K =
      (F.pf c.g).map ((F.shComp' a c.i (a ≫ c.i) rfl).inv.app K) := by
  have hw : 𝟙 X ≫ c.i = c.i ≫ 𝟙 c.Z := by simp
  have := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F)
    (IsPullback.of_horiz_isIso (fst := 𝟙 X) (snd := c.i)
      (f := c.i) (g := 𝟙 c.Z) ⟨hw⟩)
  have h := congr_app (F.exchange_id_horiz c.i hw) ((F.sh a).obj K)
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.leftUnitor_hom_app,
    Functor.rightUnitor_inv_app, Category.comp_id, Functor.comp_obj, Functor.id_obj] at h
  simp only [supportRight, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerRight_app]
  rw [CompactSupportFormalism.compIso_hom_app]
  dsimp only [supportTriangleRight, supportPrecomp, Compactification.ofIsOpenImmersion,
    Compactification.precomp]
  rw [h, F.pfComp'_id_left_inv_app]
  simp only [openSupportId, Iso.trans_inv, Functor.isoWhiskerLeft_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_inv_app,
    CompactSupportFormalism.shriek, ExchangeFormalism.shriek,
    Functor.comp_map, Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp]
  rw [(F.pfId c.Z).hom.naturality]
  dsimp only [Compactification.ofIsOpenImmersion]
  simp only [← Functor.map_comp_assoc, Category.id_comp, Iso.inv_hom_id_app,
    Iso.inv_hom_id_app_assoc, Functor.id_map, CategoryTheory.Functor.map_id]
  change (F.pf c.g).map ((F.sh c.i).map (𝟙 ((F.sh a).obj K)) ≫
    (F.shComp' a c.i (a ≫ c.i) rfl).inv.app K) = _
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]

private lemma supportLeft_hom_app
    (F : CompactSupportFormalism) [F.HasProperExchange]
    {X Y U V : Scheme.{u}} {f : X ⟶ Y}
    {j : U ⟶ Y} [IsOpenImmersion j] {a : V ⟶ X} [IsOpenImmersion a]
    {p : V ⟶ U} (sq : IsPullback a p f j) (c : Compactification f)
    (K : F.obj V) :
    (supportLeft F sq c).hom.app K =
      have := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F)
        (c.isPullback_g_ofIsPullback sq)
      (F.exchange (c.ofIsPullback sq).g (pullback.fst c.g j) j c.g
        (c.isPullback_g_ofIsPullback sq).w).app
          ((F.sh (c.ofIsPullback sq).i).obj K) ≫
        (F.pf c.g).map ((F.shComp' (c.ofIsPullback sq).i (pullback.fst c.g j)
          (a ≫ c.i) (c.ofIsPullback_i_fst sq)).inv.app K) := by
  simp only [supportLeft, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [CompactSupportFormalism.compIso_hom_app]
  dsimp only [supportTriangleLeft, supportPrecomp, Compactification.copy,
    Compactification.precomp, Compactification.ofIsOpenImmersion]
  rw [F.pfComp'_id_right_inv_app]
  simp only [openSupportId, Iso.trans_inv, Functor.isoWhiskerLeft_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_inv_app]
  rw [(F.pfId Y).hom.naturality]
  let M := (F.sh j).obj ((F.shriek (c.ofIsPullback sq)).obj K)
  have := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F)
    (c.isPullback_g_ofIsPullback sq)
  let e := (F.exchange (c.ofIsPullback sq).g (pullback.fst c.g j) j c.g
    (c.isPullback_g_ofIsPullback sq).w).app
      ((F.sh (c.ofIsPullback sq).i).obj K) ≫
    (F.pf c.g).map ((F.shComp' (c.ofIsPullback sq).i (pullback.fst c.g j)
      (a ≫ c.i) (c.ofIsPullback_i_fst sq)).inv.app K)
  change (𝟙 M ≫ (F.pfId Y).inv.app M) ≫ (F.pfId Y).hom.app M ≫ e = e
  simp only [Category.id_comp, Iso.inv_hom_id_app_assoc]

private abbrev supportPrecompRefinement
    {X Y V : Scheme.{u}} {f : X ⟶ Y} (a : V ⟶ X) [IsOpenImmersion a]
    {c d : Compactification f} (r : c.Refinement d) :
    (supportPrecomp a c).Refinement (supportPrecomp a d) where
  hom := r.hom
  i_hom := by simp only [supportPrecomp, Compactification.precomp_i,
    Category.assoc, r.i_hom]
  hom_g := r.hom_g

private lemma supportPrecompRefinement_cartesian
    {X Y V : Scheme.{u}} {f : X ⟶ Y} (a : V ⟶ X) [IsOpenImmersion a]
    {c d : Compactification f} (r : c.Refinement d)
    (hr : IsPullback c.i (𝟙 X) r.hom d.i) :
    IsPullback (supportPrecomp a c).i (𝟙 V)
      (supportPrecompRefinement a r).hom (supportPrecomp a d).i := by
  exact ((IsPullback.of_horiz_isIso (fst := 𝟙 V) (snd := a)
    (f := a) (g := 𝟙 X) ⟨by simp⟩).paste_vert hr.flip).flip

private noncomputable abbrev supportTriangleLeftHom
    {X Y U V : Scheme.{u}} {f : X ⟶ Y}
    {j : U ⟶ Y} [IsOpenImmersion j] {a : V ⟶ X} [IsOpenImmersion a]
    {p : V ⟶ U} (sq : IsPullback a p f j) {c d : Compactification f}
    (r : c.Refinement d) (hr : IsPullback c.i (𝟙 X) r.hom d.i) :
    (supportTriangleLeft sq c).Hom (supportTriangleLeft sq d) where
  rf := r.ofIsPullback sq
  rg := Compactification.Refinement.id _
  rfg :=
    { hom := r.hom
      i_hom := (supportPrecompRefinement a r).i_hom
      hom_g := r.hom_g }
  q_comm := r.ofIsPullback_hom_fst sq
  p_comm := by simpa using r.hom_g.symm
  isPullback_rf := r.isPullback_ofIsPullback sq hr
  isPullback_rg := by
    change IsPullback j (𝟙 U) (𝟙 Y) j
    exact IsPullback.of_vert_isIso ⟨by simp⟩

private noncomputable abbrev supportTriangleRightHom
    {X Y V : Scheme.{u}} {f : X ⟶ Y} (a : V ⟶ X) [IsOpenImmersion a]
    {c d : Compactification f} (r : c.Refinement d)
    (hr : IsPullback c.i (𝟙 X) r.hom d.i) :
    (supportTriangleRight a c).Hom (supportTriangleRight a d) where
  rf := Compactification.Refinement.id _
  rg := r
  rfg := supportPrecompRefinement a r
  q_comm := by simpa using r.i_hom.symm
  p_comm := by
    change 𝟙 c.Z ≫ r.hom = r.hom ≫ 𝟙 d.Z
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  isPullback_rf := by
    change IsPullback a (𝟙 V) (𝟙 X) a
    exact IsPullback.of_vert_isIso ⟨by simp⟩
  isPullback_rg := hr

private lemma supportLeft_naturality
    (F : CompactSupportFormalism) [F.HasProperExchange]
    {X Y U V : Scheme.{u}} {f : X ⟶ Y}
    {j : U ⟶ Y} [IsOpenImmersion j] {a : V ⟶ X} [IsOpenImmersion a]
    {p : V ⟶ U} (sq : IsPullback a p f j) {c d : Compactification f}
    (r : c.Refinement d) (hr : IsPullback c.i (𝟙 X) r.hom d.i) :
    Functor.whiskerRight
        (F.refinementComparison (r.ofIsPullback sq) (r.isPullback_ofIsPullback sq hr))
        (F.sh j) ≫ (supportLeft F sq c).hom =
      (supportLeft F sq d).hom ≫
        F.refinementComparison (supportPrecompRefinement a r)
          (supportPrecompRefinement_cartesian a r hr) := by
  have h := F.compIso_naturality (supportTriangleLeftHom sq r hr)
  rw [F.refinementComparison_eq_id _ _ rfl] at h
  ext K
  have hh := congr_app h K
  simp only [NatTrans.comp_app, NatTrans.hcomp_app] at hh
  change (F.compIso (supportTriangleLeft sq d)).hom.app K ≫
      (F.refinementComparison (supportPrecompRefinement a r)
        (supportPrecompRefinement_cartesian a r hr)).app K =
    (𝟙 _ ≫ (F.shriek (Compactification.ofIsOpenImmersion j)).map
      ((F.refinementComparison (r.ofIsPullback sq)
        (r.isPullback_ofIsPullback sq hr)).app K)) ≫
      (F.compIso (supportTriangleLeft sq c)).hom.app K at hh
  simp only [Category.id_comp] at hh
  simp only [supportLeft, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]
  exact (Category.assoc _ _ _).symm.trans <|
    (congrArg (fun t ↦ t ≫ (F.compIso (supportTriangleLeft sq c)).hom.app K)
    ((openSupportId F j).inv.naturality
      ((F.refinementComparison (r.ofIsPullback sq)
        (r.isPullback_ofIsPullback sq hr)).app K))).trans
    ((Category.assoc _ _ _).trans
      (congrArg (fun t ↦ (openSupportId F j).inv.app _ ≫ t) hh.symm))

private lemma supportRight_naturality
    (F : CompactSupportFormalism) [F.HasProperExchange]
    {X Y V : Scheme.{u}} {f : X ⟶ Y} (a : V ⟶ X) [IsOpenImmersion a]
    {c d : Compactification f} (r : c.Refinement d)
    (hr : IsPullback c.i (𝟙 X) r.hom d.i) :
    Functor.whiskerLeft (F.sh a) (F.refinementComparison r hr) ≫
        (supportRight F a c).hom =
      (supportRight F a d).hom ≫
        F.refinementComparison (supportPrecompRefinement a r)
          (supportPrecompRefinement_cartesian a r hr) := by
  have h := F.compIso_naturality (supportTriangleRightHom a r hr)
  rw [F.refinementComparison_eq_id _ _ rfl] at h
  ext K
  have hh := congr_app h K
  simp only [NatTrans.comp_app, NatTrans.hcomp_app] at hh
  change (F.compIso (supportTriangleRight a d)).hom.app K ≫
      (F.refinementComparison (supportPrecompRefinement a r)
        (supportPrecompRefinement_cartesian a r hr)).app K =
    ((F.refinementComparison r hr).app
        ((F.shriek (Compactification.ofIsOpenImmersion a)).obj K) ≫
      (F.shriek c).map (𝟙 _)) ≫
      (F.compIso (supportTriangleRight a c)).hom.app K at hh
  simp only [CategoryTheory.Functor.map_id, Category.comp_id] at hh
  simp only [supportRight, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]
  exact (Category.assoc _ _ _).symm.trans <|
    (congrArg (fun t ↦ t ≫ (F.compIso (supportTriangleRight a c)).hom.app K)
    ((F.refinementComparison r hr).naturality
      ((openSupportId F a).inv.app K))).symm.trans
    ((Category.assoc _ _ _).trans
      (congrArg (fun t ↦ (F.shriek d).map ((openSupportId F a).inv.app K) ≫ t) hh.symm))

attribute [local instance] unbounded_has_base_change unbounded_has_proper_exchange

attribute [local irreducible] supportLeft supportRight openSupportId
  CompactSupportFormalism.compIso ExchangeFormalism.shComp'
  ExchangeFormalism.pfComp'

private noncomputable def supportRaw
    (F : CompactSupportFormalism) [F.HasProperExchange]
    {X Y U V : Scheme.{u}} {f : X ⟶ Y}
    {j : U ⟶ Y} [IsOpenImmersion j] {a : V ⟶ X} [IsOpenImmersion a]
    {p : V ⟶ U} (sq : IsPullback a p f j) (c : Compactification f) :
    F.shriek (c.ofIsPullback sq) ⋙ F.sh j ≅ F.sh a ⋙ F.shriek c := by
  haveI := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F)
    (c.isPullback_g_ofIsPullback sq)
  haveI := CompactSupportFormalism.HasProperExchange.isIso_exchange (F := F)
    (c.isPullback_g_ofIsPullback sq)
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (asIso (F.exchange (c.ofIsPullback sq).g (pullback.fst c.g j) j c.g
        (c.isPullback_g_ofIsPullback sq).w)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((F.shComp' (c.ofIsPullback sq).i (pullback.fst c.g j)
        (a ≫ c.i) (c.ofIsPullback_i_fst sq)).symm ≪≫
        F.shComp' a c.i (a ≫ c.i) rfl) _ ≪≫
    Functor.associator _ _ _

private lemma supportRaw_factor
    (F : CompactSupportFormalism) [F.HasProperExchange]
    {X Y U V : Scheme.{u}} {f : X ⟶ Y}
    {j : U ⟶ Y} [IsOpenImmersion j] {a : V ⟶ X} [IsOpenImmersion a]
    {p : V ⟶ U} (sq : IsPullback a p f j) (c : Compactification f) :
    (supportRaw F sq c).hom ≫ (supportRight F a c).hom =
      (supportLeft F sq c).hom := by
  ext K
  simp only [NatTrans.comp_app]
  rw [supportRight_hom_app, supportLeft_hom_app]
  simp only [supportRaw, asIso_hom, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc]
  rw [← Functor.map_comp]
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  exact Category.id_comp _

private lemma supportPullback_eq_raw
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y U V : Scheme.{u}} {f : X ⟶ Y}
    {j : U ⟶ Y} [IsOpenImmersion j] {a : V ⟶ X} [IsOpenImmersion a]
    {p : V ⟶ U} (sq : IsPullback a p f j) (c : Compactification f) :
    openSupportPullbackIso Λ sq c = supportRaw (unboundedFormalism Λ) sq c := by
  let F := unboundedFormalism Λ
  have := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F)
    (c.isPullback_g_ofIsPullback sq)
  have := CompactSupportFormalism.HasProperExchange.isIso_exchange (F := F)
    (c.isPullback_g_ofIsPullback sq)
  have he : asIso (F.exchange (c.ofIsPullback sq).g (pullback.fst c.g j) j c.g
      (c.isPullback_g_ofIsPullback sq).w) =
      openImmersionLowerShriekLowerStarExchangeIso Λ
        (c.isPullback_g_ofIsPullback sq) := by
    apply Iso.ext
    exact unbounded_open_exchange Λ (c.isPullback_g_ofIsPullback sq)
  unfold supportRaw openSupportPullbackIso
  rw [he, unbounded_sh_comp, unbounded_sh_comp,
    exact_open_congr_symm Λ (c.ofIsPullback_i_fst sq)]
  simp only [mapDerivedCategoryOpenImmersionLowerShriekCongr, Iso.refl_trans,
    Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc]
  rfl

attribute [local irreducible] supportRaw openSupportPullbackIso

private lemma supportPullback_factor
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y U V : Scheme.{u}} {f : X ⟶ Y}
    {j : U ⟶ Y} [IsOpenImmersion j] {a : V ⟶ X} [IsOpenImmersion a]
    {p : V ⟶ U} (sq : IsPullback a p f j) (c : Compactification f) :
    (openSupportPullbackIso Λ sq c).hom ≫
        (supportRight (unboundedFormalism Λ) a c).hom =
      (supportLeft (unboundedFormalism Λ) sq c).hom := by
  rw [supportPullback_eq_raw]
  exact supportRaw_factor (unboundedFormalism Λ) sq c

/-- Proper/open exchange intertwines the comparison for one cartesian refinement
with its literal pullback. No common-refinement choice or graph comparison occurs. -/
theorem openSupportPullbackIso_refinement
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y U V : Scheme.{u}} {f : X ⟶ Y}
    {j : U ⟶ Y} [IsOpenImmersion j] {a : V ⟶ X} [IsOpenImmersion a]
    {p : V ⟶ U} (sq : IsPullback a p f j)
    {c d : Compactification f} (r : c.Refinement d)
    (hr : IsPullback c.i (𝟙 X) r.hom d.i) :
    Functor.whiskerRight
        (rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} Λ)
          (r.ofIsPullback sq) (r.isPullback_ofIsPullback sq hr))
        D((j)_!open[ModuleCat.{u + 1} Λ]) ≫
      (openSupportPullbackIso Λ sq c).hom =
    (openSupportPullbackIso Λ sq d).hom ≫
      Functor.whiskerLeft D((a)_!open[ModuleCat.{u + 1} Λ])
        (rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} Λ)
          r hr) := by
  let F := unboundedFormalism Λ
  have hl := supportLeft_naturality F sq r hr
  have hrr := supportRight_naturality F a r hr
  simp only [F, unbounded_refinement_comparison] at hl hrr
  change Functor.whiskerRight
      (rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} Λ)
        (r.ofIsPullback sq) (r.isPullback_ofIsPullback sq hr))
      D((j)_!open[ModuleCat.{u + 1} Λ]) ≫ (supportLeft F sq c).hom = _ at hl
  change Functor.whiskerLeft D((a)_!open[ModuleCat.{u + 1} Λ])
      (rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} Λ) r hr) ≫
      (supportRight F a c).hom = _ at hrr
  have h : Functor.whiskerRight
      (rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} Λ)
        (r.ofIsPullback sq) (r.isPullback_ofIsPullback sq hr))
      D((j)_!open[ModuleCat.{u + 1} Λ]) ≫
      (openSupportPullbackIso Λ sq c).hom ≫ (supportRight F a c).hom =
    (openSupportPullbackIso Λ sq d).hom ≫
      Functor.whiskerLeft D((a)_!open[ModuleCat.{u + 1} Λ])
        (rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} Λ)
          r hr) ≫ (supportRight F a c).hom := by
    rw [supportPullback_factor, hl, hrr, ← Category.assoc, supportPullback_factor]
  exact (cancel_mono (supportRight F a c).hom).1 (by simpa only [Category.assoc] using h)

end AlgebraicGeometry.Etale
