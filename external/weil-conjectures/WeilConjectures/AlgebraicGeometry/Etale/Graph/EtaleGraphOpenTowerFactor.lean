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
import WeilConjectures.AlgebraicGeometry.Etale.Graph.EtaleGraphEtaleOpenComposition

/-! # Graph tower factorization before endpoint normalization

Source: Stacks Project, Tags 0F4L, 0F7B and 0F7J.
(blueprint: lem-pur-etale-graph-open-tower-factor)
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

set_option allowUnsafeReducibility true in
attribute [local reducible] rightDerivedLowerStar

private lemma open_tower_pasting
    {C D E F : Type*}
    [Category C] [Category D] [Category E] [Category F]
    {V₀ V : C ⥤ D} {J₀ J : D ⥤ E} {P₀ P : E ⥤ F}
    {R₀ R : C ⥤ E} {T : D ⥤ F} {U : C ⥤ F}
    (dv : V₀ ≅ V) (dj : J₀ ≅ J) (dp : P₀ ≅ P) (dr : R₀ ≅ R)
    (tc : J ⋙ P ≅ T) (s : V ⋙ J ≅ R) (k : R ⋙ P ≅ U)
    (cvj : V₀ ⋙ J₀ ≅ R₀) (cjp : J₀ ⋙ P₀ ≅ T)
    (cvt : V₀ ⋙ T ≅ U) (crp : R₀ ⋙ P₀ ≅ U)
    (hf : Functor.isoWhiskerRight dj P₀ ≪≫
      Functor.isoWhiskerLeft J dp ≪≫ tc = cjp)
    (hg : Functor.isoWhiskerRight dv J₀ ≪≫
      Functor.isoWhiskerLeft V dj ≪≫ s = cvj ≪≫ dr)
    (hp : Functor.isoWhiskerRight dr.symm P ≪≫
      Functor.isoWhiskerLeft R₀ dp.symm ≪≫ crp = k)
    (ha : Functor.isoWhiskerLeft V₀ cjp ≪≫ cvt =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight cvj P₀ ≪≫ crp) (M : C) :
    tc.hom.app (V.obj M) ≫ T.map (dv.inv.app M) ≫
        cvt.hom.app M ≫ k.inv.app M = P.map (s.hom.app M) := by
  have hf' := congr_app (congrArg Iso.hom hf) (V.obj M)
  have hg' := congr_app (congrArg Iso.hom hg) M
  have hp' := congr_app (congrArg Iso.hom hp) M
  have ha' := congr_app (congrArg Iso.hom ha) M
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Category.id_comp] at hf' hg' hp' ha'
  let q := P₀.map (J₀.map (dv.hom.app M)) ≫
    P₀.map (dj.hom.app (V.obj M)) ≫ dp.hom.app (J.obj (V.obj M))
  have : IsIso q := by dsimp only [q]; infer_instance
  apply (cancel_epi q).1
  have hl : q ≫ tc.hom.app (V.obj M) ≫ T.map (dv.inv.app M) ≫
      cvt.hom.app M ≫ k.inv.app M =
      cjp.hom.app (V₀.obj M) ≫ cvt.hom.app M ≫ k.inv.app M := by
    dsimp only [q]
    simp only [Category.assoc]
    rw [reassoc_of% hf']
    have hn := cjp.hom.naturality (dv.hom.app M)
    dsimp only [Functor.comp_map] at hn
    rw [reassoc_of% hn]
    simp only [← T.map_comp_assoc,
      Iso.hom_inv_id_app, T.map_id, Category.id_comp]
  have hr : q ≫ P.map (s.hom.app M) ≫ k.hom.app M =
      P₀.map (cvj.hom.app M) ≫ crp.hom.app M := by
    dsimp only [q]
    simp only [Category.assoc]
    rw [dp.hom.naturality_assoc, dp.hom.naturality_assoc]
    rw [← P.map_comp_assoc, ← P.map_comp_assoc]
    simp only [Category.assoc]
    rw [hg', P.map_comp]
    simp only [Category.assoc]
    rw [← dp.hom.naturality_assoc, ← hp']
    simp only [← P.map_comp_assoc, Iso.hom_inv_id_app,
      P.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc]
  rw [hl, reassoc_of% ha']
  apply (cancel_mono (k.hom.app M)).1
  simpa only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] using hr.symm

private lemma inverse_conjugate_composite
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ L₃ : C ⥤ D} {R₁ R₂ R₃ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    (x : R₁ ≅ R₂) (y : R₃ ≅ R₂) :
    ((conjugateIsoEquiv a₁ a₂).symm x).symm ≪≫
        (conjugateIsoEquiv a₃ a₂).symm y =
      (conjugateIsoEquiv a₃ a₁).symm (y ≪≫ x.symm) := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom,
    conjugateIsoEquiv_symm_apply_hom, conjugateIsoEquiv_symm_apply_inv]
  exact conjugateEquiv_symm_comp a₃ a₂ a₁ y.hom x.inv

private lemma exact_square_triangle
    (A : Type (u + 1)) [CommRing A]
    {X X' Z Z' : Scheme.{u}}
    {v : X' ⟶ X} {j : X ⟶ Z} {j' : X' ⟶ Z'} {b : Z' ⟶ Z}
    (sq : CommSq v j' j b) :
    (Functor.mapDerivedCategoryNatIso
        (upperStarComp (ModuleCat.{u + 1} A) j' b (v ≫ j) sq.w) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm) ≪≫
      (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.flip).symm =
    Functor.mapDerivedCategoryNatIso
        (upperStarComp (ModuleCat.{u + 1} A) v j (v ≫ j) rfl) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm := by
  have hh : squareUpperStarIso (ModuleCat.{u + 1} A) sq.flip =
      (upperStarComp (ModuleCat.{u + 1} A) v j (v ≫ j) rfl).symm ≪≫
        upperStarComp (ModuleCat.{u + 1} A) j' b (v ≫ j) sq.w := by
    rw [squareUpperStarIso_flip (ModuleCat.{u + 1} A) sq]
    rfl
  have hd : Functor.mapDerivedCategoryNatIso
      (squareUpperStarIso (ModuleCat.{u + 1} A) sq.flip) =
      (Functor.mapDerivedCategoryNatIso
        (upperStarComp (ModuleCat.{u + 1} A) v j (v ≫ j) rfl)).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (upperStarComp (ModuleCat.{u + 1} A) j' b (v ≫ j) sq.w) := by
    rw [hh]
    apply Iso.ext
    simp only [Functor.mapDerivedCategoryNatIso_trans,
      Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom, Iso.symm_hom]
  unfold exactDerivedSquareUpperStarIso
  rw [hd]
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]

private lemma support_associativity
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X Y : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian Y]
    (v : U ⟶ X) [Etale v] [IsSeparated v] [QuasiCompact v]
    {f : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification v] [HasCompactification f] [HasCompactification (v ≫ f)]
    (c : Compactification f) [IsNoetherian c.Z]
    [QuasiCompact c.i] [HasCompactification c.i] [HasCompactification c.g]
    [HasCompactification (v ≫ c.i)] [HasCompactification (c.i ≫ c.g)]
    [HasCompactification ((v ≫ c.i) ≫ c.g)]
    [HasCompactification (v ≫ c.i ≫ c.g)] :
    let w : v ≫ f = (v ≫ c.i) ≫ c.g :=
      (congrArg (fun h : X ⟶ Y ↦ v ≫ h) c.comm).trans (Category.assoc _ _ _).symm
    Functor.isoWhiskerLeft (rightDerivedLowerShriek (ModuleCat.{u + 1} A) v)
        (unboundedEtaleLowerShriekCompIso A c.i c.g ≪≫
          unboundedEtaleLowerShriekCongr A c.comm.symm) ≪≫
      (unboundedEtaleLowerShriekCompIso A v f ≪≫ unboundedEtaleLowerShriekCongr A w) =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (unboundedEtaleLowerShriekCompIso A v c.i)
          (rightDerivedLowerShriek (ModuleCat.{u + 1} A) c.g) ≪≫
        unboundedEtaleLowerShriekCompIso A (v ≫ c.i) c.g := by
  rcases c with ⟨Z, p, j, h, hp, hj⟩
  subst f
  let := hp
  let := hj
  dsimp only
  simp only [unboundedEtaleLowerShriekCongr, Iso.trans_refl]
  apply Iso.ext
  apply NatTrans.ext
  funext M
  have h := congr_app (unboundedEtaleLowerShriekCompIso_assoc A v j p) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] at h
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Iso.symm_hom, Functor.associator_inv_app, Category.id_comp]
  rw [← h]
  simp only [unboundedEtaleLowerShriekCongr, Category.comp_id, Iso.refl_hom,
    NatTrans.id_app]

/-- The graph tower identity before the terminal compactification comparison.

This is the normalized identity after postcomposition with the inverse of the endpoint
comparison `k`; the original tower formula follows by cancellation.
This involves only one compact-support composition, and no proper/etale interchange.
Source: Stacks Project, etale-cohomology.tex Tag 0F4L (graph comparison), and
more-etale.tex Tags 0F7B and 0F7J (the proper/open composition tower).
(blueprint: lem-pur-etale-graph-open-tower-factor).

Proof in words:
Take the tower e over c. The every-tower composition formula writes the left
side using the compactification e.restrict of v'. Replace its inverse comparison
by the explicit graph-derived map. On sheaves, extending a sheet section first
to the clopen graph of v' and then across c.i agrees with extending it to the
graph of r = v' followed by c.i. Both sections agree on that graph and vanish
off it. The sheaf axiom, followed by sum-presheaf sheafification, identifies the
maps. Transposition under the two composite sum/open adjunctions identifies the
change of factorization with a inverse followed by s. Apply the equality
termwise, compose with the right-derived direct-image units, and use the unit
characterization of direct-image composition. The graph-derived component
formula and homotopy localization give the equality on every unbounded input.
Postcompose with the inverse of the endpoint comparison k, so the terminal
compactification disappears. The remaining equality is the graph-derived
factorization through the two conjugate adjunction comparisons a and s. The
component formula and homotopy localization identify this equality on every
unbounded input; identity opens reduce to triangle identities, and empty graphs
or zero coefficients give zero maps. -/
theorem etaleGraph_open_tower_factor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Z' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Z']
    {f : X ⟶ Y} {v' : X' ⟶ X}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [Etale v'] [IsSeparated v'] [QuasiCompact v']
    [HasCompactification f] [HasCompactification v']
    [HasCompactification (v' ≫ f)] [QuasiCompact (v' ≫ f)]
    (c : Compactification f) (j' : X' ⟶ Z') [IsOpenImmersion j']
    (b : Z' ⟶ c.Z) [Etale b] [IsSeparated b]
    (osq : CommSq v' j' c.i b)
    (e : Compactification (v' ≫ c.i))
    [HasCompactification ((v' ≫ c.i) ≫ c.g)]
    (M : DerivedCategoryModule A X') :
    let r := v' ≫ c.i
    let p := c.g
    let va := derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v' inferInstance
    let ba := derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) b inferInstance
    let ja := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) c.i
    let j'a := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j'
    let a := (conjugateIsoEquiv (va.comp ja) (j'a.comp ba)).symm
      (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) osq.flip)
    let s := (conjugateIsoEquiv
      (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) r inferInstance)
      (j'a.comp ba)).symm
      (Functor.mapDerivedCategoryNatIso
        (upperStarComp (ModuleCat.{u + 1} A) j' b r osq.w) ≪≫
        (Functor.mapDerivedCategoryCompIso _ _).symm)
    let dv' := (rightDerivedLowerShriekIso A
      (HasCompactification.compactification v')).symm ≪≫
      canonicalEtaleCompactSupportComparison A v' (HasCompactification.compactification v')
    let w : v' ≫ f = r ≫ p :=
      (congrArg (fun h : X ⟶ Y ↦ v' ≫ h) c.comm).trans (Category.assoc _ _ _).symm
    let l := Functor.isoWhiskerRight dv'.symm
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f) ≪≫
      unboundedEtaleLowerShriekCompIso A v' f ≪≫ unboundedEtaleLowerShriekCongr A w
    let k := Functor.isoWhiskerRight
      (canonicalEtaleCompactSupportComparison A r e).symm
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) p) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) e.i).mapDerivedCategory
        (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e.g p) ≪≫
      rightDerivedLowerShriekIso A (e.postcomp p)
    (rightDerivedLowerShriekIso A c).hom.app
        ((etaleLowerShriek (ModuleCat.{u + 1} A) v' inferInstance).mapDerivedCategory.obj M) ≫
      l.hom.app M ≫ k.inv.app M =
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) p).map (a.inv.app M) ≫
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) p).map (s.hom.app M) := by
  let va := derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v' inferInstance
  let ja := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) c.i
  let ba := derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) b inferInstance
  let j'a := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j'
  let ra := derivedEtaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) (v' ≫ c.i) inferInstance
  have hm := inverse_conjugate_composite (va.comp ja) (j'a.comp ba) ra
    (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) osq.flip)
    (Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} A) j' b (v' ≫ c.i) osq.w) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm)
  rw [exact_square_triangle A osq] at hm
  let : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  let : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  let : IsNoetherian c.Z := ⟨⟩
  let : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  let s₀ := (conjugateIsoEquiv ra (va.comp ja)).symm
    (Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} A) v' c.i (v' ≫ c.i) rfl) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm)
  let dr := (rightDerivedLowerShriekIso A e).symm ≪≫
    canonicalEtaleCompactSupportComparison A (v' ≫ c.i) e
  let w : v' ≫ f = (v' ≫ c.i) ≫ c.g :=
    (congrArg (fun h : X ⟶ Y ↦ v' ≫ h) c.comm).trans (Category.assoc _ _ _).symm
  let ct := unboundedEtaleLowerShriekCompIso A v' f ≪≫ unboundedEtaleLowerShriekCongr A w
  let k := Functor.isoWhiskerRight
      (canonicalEtaleCompactSupportComparison A (v' ≫ c.i) e).symm
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) c.g) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) e.i).mapDerivedCategory
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e.g c.g) ≪≫
    rightDerivedLowerShriekIso A (e.postcomp c.g)
  have hf := graph_compactification_factorization A c
  have hg := graph_etale_open_composition A v' c.i e
  have hp₀ := graph_proper_postcomposition A e c.g
  have hp : Functor.isoWhiskerRight dr.symm
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) c.g) ≪≫
      Functor.isoWhiskerLeft (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (v' ≫ c.i))
        (graphChosenProperComparison A c.g).symm ≪≫
      unboundedEtaleLowerShriekCompIso A (v' ≫ c.i) c.g = k := by
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
    rw [(graphChosenProperComparison A c.g).inv.naturality_assoc, hK]
    simp only [Category.assoc, Category.id_comp]
    erw [(graphChosenProperComparison A c.g).inv_hom_id_app_assoc]
  have ha := support_associativity A v' c
  have hh := open_tower_pasting
    (graphChosenEtaleComparison A v') (graphChosenOpenComparison A c.i)
    (graphChosenProperComparison A c.g) dr (rightDerivedLowerShriekIso A c) s₀ k
    (unboundedEtaleLowerShriekCompIso A v' c.i)
    (unboundedEtaleLowerShriekCompIso A c.i c.g ≪≫
      unboundedEtaleLowerShriekCongr A c.comm.symm) ct
    (unboundedEtaleLowerShriekCompIso A (v' ≫ c.i) c.g)
    hf (by simpa only [s₀, ra, va, ja, dr, Iso.trans_assoc] using hg) hp ha M
  have hm' := congrArg (fun t ↦ (rightDerivedLowerStar (ModuleCat.{u + 1} A) c.g).map
    (t.hom.app M)) hm
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp] at hm'
  rw [← hm'] at hh
  simpa only [graphChosenEtaleComparison, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, ct, w, k, va, ja, ba, j'a, ra] using hh

end AlgebraicGeometry.Etale
