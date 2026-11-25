/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportGraphDerivedIsoSupplement
import WeilConjectures.AlgebraicGeometry.Etale.Graph.EtaleGraphOpenTower
import WeilConjectures.AlgebraicGeometry.Etale.Graph.EtaleGraphProperTower

/-! # The normalized compactification tower for etale horizontal composition

Source: Stacks Project, Tags 0F7B, 0F7F, 0F7J and 0F7L
(blueprint: lem-pur-etale-horizontal-support-tower).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

-- The statement uses these constructions through their interfaces.
attribute [local irreducible] lowerStar upperStar etaleLowerShriek openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  canonicalEtaleCompactSupportComparison derivedEtaleLowerShriekUpperStarAdjunction
  derivedOpenImmersionLowerShriekUpperStarAdjunction mapDerivedUpperStarLowerStarAdjunction
  rightDerivedLowerShriekIso unboundedEtaleLowerShriekCompIso unboundedEtaleLowerShriekCongr

private lemma compactSupportCongr_symm
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} {f g : X ⟶ Y}
    [HasCompactification f] [HasCompactification g] (w : f = g) :
    (unboundedEtaleLowerShriekCongr A w).symm = unboundedEtaleLowerShriekCongr A w.symm := by
  subst w
  simp only [unboundedEtaleLowerShriekCongr, Iso.refl_symm]

private lemma compactSupportCongr_trans
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} {f g h : X ⟶ Y}
    [HasCompactification f] [HasCompactification g] [HasCompactification h]
    (w : f = g) (w' : g = h) :
    unboundedEtaleLowerShriekCongr A w ≪≫ unboundedEtaleLowerShriekCongr A w' =
      unboundedEtaleLowerShriekCongr A (w.trans w') := by
  subst w
  subst w'
  simp only [unboundedEtaleLowerShriekCongr, Iso.refl_trans]

private lemma mapIso_cancel
    {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {X Y : C} (i : X ≅ Y) {Z : D} (h : F.obj X ⟶ Z) :
    F.map i.hom ≫ F.map i.inv ≫ h = h := by
  rw [← F.map_comp_assoc, i.hom_inv_id, F.map_id X, Category.id_comp]

private lemma compactSupportTower_cancel
    {C : Type*} [Category* C] {A₀ A₁ A₂ A₃ A₄ A₅ A₆ : C}
    (d : A₀ ⟶ A₁) (l : A₁ ⟶ A₂) [Mono l] (rho : A₀ ⟶ A₂)
    (u : A₀ ⟶ A₃) (g : A₃ ⟶ A₄) (a : A₄ ⟶ A₅) (t : A₅ ⟶ A₁)
    (ai : A₅ ⟶ A₄) (s : A₄ ⟶ A₆) (k : A₆ ⟶ A₂) (q : A₃ ⟶ A₀)
    (hd : d ≫ l = rho) (hl : t ≫ l = ai ≫ s ≫ k)
    (ha : a ≫ ai ≫ s ≫ k = s ≫ k) (hr : q ≫ rho = g ≫ s ≫ k)
    (ht : u ≫ q ≫ rho = rho) : d = u ≫ g ≫ a ≫ t := by
  apply (cancel_mono l).1
  rw [hd]
  simp only [Category.assoc]
  rw [hl, ha, ← hr]
  exact ht.symm

/-- The canonical graph comparisons put compact-support composition in the proper/open
compactification normal form. This identity is before either horizontal counit is applied.
The proper factor is the right-adjoint mate of inverse etale sum exchange under the
inverse-image/direct-image adjunctions. In particular it does not involve inverse proper
base change, or the full compact-support exchange for f.
Source: Stacks Project, Tags 0F7B and 0F7F for proper/quasi-finite interchange,
Tag 0F7J for composition, and Tag 0F7L, item (3), for its base-change compatibility;
Tag 0F4L for the canonical graph comparison
(blueprint: lem-pur-etale-horizontal-support-tower).

Proof in words:
1. Choose a compactification d of v' followed by f, and set e=d.ofComp c. For the
   other factorization use d transported by sq.w, a compactification q of v, and its
   ofComp tower. Expand both composition maps by their proper/open tower equations.
   The comparison cocycles and the equality of the two composites identify their
   terminal models through a common proper refinement.
2. For an etale map the inverse canonical comparison is the explicit derived graph
   map. At the sheaf level its composite into direct image extends a sheet section
   by zero from its clopen graph. Restricting this graph along j and along j' gives
   the same graph. Its section is unchanged there and zero on the complement.
   Transpose under the two sum/evaluation adjunctions: the resulting open factor is
   the unique composite-left-adjoint comparison a for the inverse-image square.
3. The remaining proper/quasi-finite interchange is the map of Tag 0F7B. On a
   K-injective complex I on the upper left scheme, resolve the extension by zero
   along the upper horizontal arrow by a K-injective complex K. The map is the
   composite of the common proper-support identification on I with the direct
   image of that resolution map. The sheaf identification is specified by the common
   proper-support inclusion. Its inverse-image transpose is inverse etale sum
   exchange: restriction pulls a sheet and its section to the pulled-back sheet.
   On that graph both constructions are the same section, and off it both are zero.
   The sheaf axiom and sum-presheaf sheafification prove equality of these sheaf
   arrows. Thus transposition under the two proper inverse-image/direct-image
   adjunctions gives precisely gam, with the direction in the statement.
4. Apply the equal sheaf arrows degreewise, followed by the total-derived units.
   The formula compactSupportDerivedComparison_app fixes the derived graph maps on
   every homotopy representative. Represent proper direct images by K-injectives
   and resolve each open or sum extension before its next direct image. Naturality
   of the units and the unit characterization of derived direct-image composition
   identify the two resulting morphisms. Localization makes this an equality of
   natural transformations on the entire unbounded categories.
5. Canonical graph refinement coherence and the normalized proper-refinement
   equation cancel the refining towers. Associate the surviving factors to obtain
   S_v(t' inverse), gam at J'(M), P(a at M), and t at S_v'(M). Identity graphs use
   the graph identity and direct-image right unit; empty graphs and zero
   coefficients give zero on both sides. No equality of derived morphisms is
   inferred merely from agreement of their stalk maps. -/
theorem etaleHorizontalSupport_tower
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {v : Y' ⟶ Y} {v' : X' ⟶ X}
    [IsSeparated f] [IsSeparated f'] [IsSeparated v] [IsSeparated v']
    [Etale v] [Etale v'] [LocallyOfFiniteType f] [LocallyOfFiniteType f']
    [LocallyOfFiniteType v] [LocallyOfFiniteType v']
    [QuasiCompact f] [QuasiCompact f'] [QuasiCompact v] [QuasiCompact v']
    [HasCompactification f] [HasCompactification f'] [HasCompactification v]
    [HasCompactification v'] [HasCompactification (v' ≫ f)]
    [HasCompactification (f' ≫ v)] [QuasiCompact (v' ≫ f)]
    [QuasiCompact (f' ≫ v)] (sq : IsPullback v' f' f v)
    (c : Compactification f)
    [IsIso (((mateEquiv
      (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v inferInstance)
      (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
        (pullback.fst c.g v) inferInstance)).symm
      (TwoSquare.mk _ _ _ _ (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A)
        (IsPullback.of_hasPullback c.g v).toCommSq).hom)))]
    (M : DerivedCategoryModule A X') :
    let cs := c.ofIsPullback sq
    let va := derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v' inferInstance
    let ba := derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
      (pullback.fst c.g v) inferInstance
    let ja := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) c.i
    let j'a := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) cs.i
    let a := (conjugateIsoEquiv (va.comp ja) (j'a.comp ba)).symm
      (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A)
        (c.isPullback_i_ofIsPullback sq).toCommSq.flip)
    let sumEx := ((mateEquiv
      (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v inferInstance)
      (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
        (pullback.fst c.g v) inferInstance)).symm
      (TwoSquare.mk _ _ _ _ (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A)
        (IsPullback.of_hasPullback c.g v).toCommSq).hom))
    let gam := (mateEquiv
      (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
        (pullback.snd c.g v))
      (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.g)
      (TwoSquare.mk _ _ _ _ (inv sumEx)))
    let dv' := (rightDerivedLowerShriekIso A
      (HasCompactification.compactification v')).symm ≪≫
        canonicalEtaleCompactSupportComparison A v' (HasCompactification.compactification v')
    let dv := (rightDerivedLowerShriekIso A
      (HasCompactification.compactification v)).symm ≪≫
        canonicalEtaleCompactSupportComparison A v (HasCompactification.compactification v)
    let delta := Functor.isoWhiskerRight dv'.symm
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f) ≪≫
        unboundedEtaleLowerShriekCompIso A v' f ≪≫
        unboundedEtaleLowerShriekCongr A sq.toCommSq.w ≪≫
        (unboundedEtaleLowerShriekCompIso A f' v).symm ≪≫
        Functor.isoWhiskerLeft
          (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f') dv
    delta.inv.app M =
      (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory.map
          ((rightDerivedLowerShriekIso A cs).inv.app M) ≫
        gam.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) cs.i).mapDerivedCategory.obj M) ≫
        (rightDerivedLowerStar (ModuleCat.{u + 1} A) c.g).map
          (a.hom.app M) ≫
        (rightDerivedLowerShriekIso A c).hom.app
          ((etaleLowerShriek (ModuleCat.{u + 1} A) v' inferInstance).mapDerivedCategory.obj M) := by
  dsimp only
  let cs := c.ofIsPullback sq
  let va := derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v' inferInstance
  let ba := derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
    (pullback.fst c.g v) inferInstance
  let ja := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) c.i
  let j'a := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) cs.i
  let a := (conjugateIsoEquiv (va.comp ja) (j'a.comp ba)).symm
    (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A)
      (c.isPullback_i_ofIsPullback sq).toCommSq.flip)
  let sumEx := ((mateEquiv
    (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v inferInstance)
    (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
      (pullback.fst c.g v) inferInstance)).symm
    (TwoSquare.mk _ _ _ _ (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback c.g v).toCommSq).hom))
  let gam := (mateEquiv
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
      (pullback.snd c.g v))
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.g)
    (TwoSquare.mk _ _ _ _ (inv sumEx)))
  let dv' := (rightDerivedLowerShriekIso A
    (HasCompactification.compactification v')).symm ≪≫
      canonicalEtaleCompactSupportComparison A v' (HasCompactification.compactification v')
  let dv := (rightDerivedLowerShriekIso A
    (HasCompactification.compactification v)).symm ≪≫
      canonicalEtaleCompactSupportComparison A v (HasCompactification.compactification v)
  let delta := Functor.isoWhiskerRight dv'.symm
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f) ≪≫
      unboundedEtaleLowerShriekCompIso A v' f ≪≫
      unboundedEtaleLowerShriekCongr A sq.toCommSq.w ≪≫
      (unboundedEtaleLowerShriekCompIso A f' v).symm ≪≫
      Functor.isoWhiskerLeft
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f') dv
  change delta.inv.app M =
    (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory.map
        ((rightDerivedLowerShriekIso A cs).inv.app M) ≫
      gam.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) cs.i).mapDerivedCategory.obj M) ≫
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) c.g).map (a.hom.app M) ≫
      (rightDerivedLowerShriekIso A c).hom.app
        ((etaleLowerShriek (ModuleCat.{u + 1} A) v' inferInstance).mapDerivedCategory.obj M)
  let : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  let : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  let : IsNoetherian c.Z := ⟨⟩
  let : IsLocallyNoetherian cs.Z := LocallyOfFiniteType.isLocallyNoetherian cs.g
  let : CompactSpace cs.Z := QuasiCompact.compactSpace_of_compactSpace cs.g
  let : IsNoetherian cs.Z := ⟨⟩
  let r := v' ≫ c.i
  let p := c.g
  let e := (HasCompactification.compactification (v' ≫ f)).ofComp c
  let : HasCompactification (r ≫ p) := (e.postcomp p).hasCompactification
  let osq := (c.isPullback_i_ofIsPullback sq).toCommSq
  let s := (conjugateIsoEquiv
    (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) r inferInstance)
    (j'a.comp ba)).symm
    (Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} A) cs.i (pullback.fst c.g v) r osq.w) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm)
  let k := Functor.isoWhiskerRight
    (canonicalEtaleCompactSupportComparison A r e).symm
    (rightDerivedLowerStar (ModuleCat.{u + 1} A) p) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) e.i).mapDerivedCategory
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e.g p) ≪≫
    rightDerivedLowerShriekIso A (e.postcomp p)
  have w₁ : v' ≫ f = r ≫ p :=
    (congrArg (fun h : X ⟶ Y ↦ v' ≫ h) c.comm).trans (Category.assoc _ _ _).symm
  have w₂ : f' ≫ v = r ≫ p := sq.w.symm.trans w₁
  let l := Functor.isoWhiskerRight dv'.symm
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f) ≪≫
    unboundedEtaleLowerShriekCompIso A v' f ≪≫ unboundedEtaleLowerShriekCongr A w₁
  let rho := Functor.isoWhiskerLeft
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f') dv.symm ≪≫
    unboundedEtaleLowerShriekCompIso A f' v ≪≫ unboundedEtaleLowerShriekCongr A w₂
  have hl := etaleGraph_open_tower A c cs.i (pullback.fst c.g v) osq e M
  change (rightDerivedLowerShriekIso A c).hom.app
      ((etaleLowerShriek (ModuleCat.{u + 1} A) v' inferInstance).mapDerivedCategory.obj M) ≫
      l.hom.app M =
    (rightDerivedLowerStar (ModuleCat.{u + 1} A) p).map (a.inv.app M) ≫
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) p).map (s.hom.app M) ≫
      k.hom.app M at hl
  have hr := etaleGraph_proper_tower A cs p (pullback.fst c.g v)
    (IsPullback.of_hasPullback c.g v) r osq.w e M
  change (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory.map
      ((rightDerivedLowerShriekIso A cs).hom.app M) ≫ rho.hom.app M =
    gam.app ((openImmersionLowerShriek (ModuleCat.{u + 1} A) cs.i).mapDerivedCategory.obj M) ≫
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) p).map (s.hom.app M) ≫
      k.hom.app M at hr
  have hcongr : (unboundedEtaleLowerShriekCongr A sq.w).symm ≪≫
      unboundedEtaleLowerShriekCongr A w₁ = unboundedEtaleLowerShriekCongr A w₂ := by
    rw [compactSupportCongr_symm, compactSupportCongr_trans]
  have hdelta : delta.symm ≪≫ l = rho := by
    dsimp only [delta, l, rho]
    simp only [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc,
      ← Functor.isoWhiskerLeft_symm, ← Functor.isoWhiskerRight_symm,
      Iso.self_symm_id_assoc, Iso.symm_self_id_assoc, hcongr]
  have hd : delta.inv.app M ≫ l.hom.app M = rho.hom.app M := by
    exact congr_app (congrArg Iso.hom hdelta) M
  have ha := mapIso_cancel (rightDerivedLowerStar (ModuleCat.{u + 1} A) p) (a.app M)
    ((rightDerivedLowerStar (ModuleCat.{u + 1} A) p).map (s.hom.app M) ≫ k.hom.app M)
  have ht := mapIso_cancel
    (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory
    ((rightDerivedLowerShriekIso A cs).app M).symm (rho.hom.app M)
  exact compactSupportTower_cancel (delta.inv.app M) (l.hom.app M) (rho.hom.app M)
    ((etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory.map
      ((rightDerivedLowerShriekIso A cs).inv.app M))
    (gam.app ((openImmersionLowerShriek (ModuleCat.{u + 1} A) cs.i).mapDerivedCategory.obj M))
    ((rightDerivedLowerStar (ModuleCat.{u + 1} A) p).map (a.hom.app M))
    ((rightDerivedLowerShriekIso A c).hom.app
      ((etaleLowerShriek (ModuleCat.{u + 1} A) v' inferInstance).mapDerivedCategory.obj M))
    ((rightDerivedLowerStar (ModuleCat.{u + 1} A) p).map (a.inv.app M))
    ((rightDerivedLowerStar (ModuleCat.{u + 1} A) p).map (s.hom.app M)) (k.hom.app M)
    ((etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory.map
      ((rightDerivedLowerShriekIso A cs).hom.app M)) hd hl ha hr ht

end AlgebraicGeometry.Etale
