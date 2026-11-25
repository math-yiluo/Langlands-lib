/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Local.DiagonalLocalChernRealization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedPullbackCoherence
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Local.DiagonalLocalChernRootPullback
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Local.DiagonalLocalChernCoefficientPullback
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Completed.DiagonalCompletedLocalChernLift
import WeilConjectures.AlgebraicGeometry.SmoothPurity.TowerChernPullback
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.IsoId
import all WeilConjectures.AlgebraicGeometry.OpenPinnedSingleTensorRestrictionFactors

/-! # Horizontal realization of whole-system Chern pullback -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor CondensedRing.upperStar
  CompletedRealization.singleUnit CompletedRealization.shiftedLine

set_option backward.defeqAttrib.useBackward true in
-- Compare normalized endpoints through the derived and module-object presentations.
private theorem pullEndpoint_iso_unique
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] {X S : Scheme.{u}} {f : X ⟶ S}
    {M : Modules R S} {N : Modules R X}
    {m m' : (upperStar Ab.{u + 1} f).obj M.X ⟶ N.X}
    (a : PullEndpoint R f M N m) (b : PullEndpoint R f M N m')
    (hm : m = m') : a.iso = b.iso := by
  cases hm
  refine Iso.ext (((CondensedRing.upperStarLowerStarAdjunction R f).homEquiv M N).injective
    (Mod.hom_ext _ _ ?_))
  exact a.normalization.trans b.normalization.symm

set_option backward.defeqAttrib.useBackward true in
-- Compare normalized endpoints through the derived and module-object presentations.
private theorem unitEndpoint_iso_eq
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X S : Scheme.{u}} (f : X ⟶ S)
    (c : UnitPullEndpoint R f) :
    c.iso = (Functor.Monoidal.εIso (CondensedRing.upperStar R f)).symm := by
  let d : UnitPullEndpoint R f :=
    { iso := (Functor.Monoidal.εIso (CondensedRing.upperStar R f)).symm
      normalization := by
        erw [CondensedRing.homEquiv_εIso_inv_hom]
        rfl }
  exact pullEndpoint_iso_unique c d rfl

set_option backward.defeqAttrib.useBackward true in
-- Compare normalized endpoints through the derived and module-object presentations.
private theorem unitEndpoint_derived_eq
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X S : Scheme.{u}} (f : X ⟶ S)
    (c : UnitPullEndpoint R f) :
    c.derived = (CondensedRing.leftDerivedUpperStarUnitIso R f).hom := by
  rw [PullEndpoint.derived, unitEndpoint_iso_eq]
  simp only [singlePullback, Iso.symm_hom, Iso.app_hom]
  rw [CondensedRing.leftDerivedUpperStarUnitIso_hom_eq]
  rw [Functor.singleFunctorCompLeftDerivedFunctorIso]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Category.assoc]
  rw [← AlgebraicGeometry.exact_single_hom]
  rw [← Functor.leftDerivedFunctorIsoMapDerivedCategory_hom_fac]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc]
  simp only [Functor.mapHomotopyCategorySingleHom,
    Functor.mapHomotopyCategoryFactors_hom_app_eq_id]
  erw [Category.id_comp]
  simp only [Functor.map_comp]
  rfl

-- Compare normalized endpoints through the derived and module-object presentations.
private theorem realizationLinePullMap_eq (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) :
    diagonalRealizationLinePullMap l f = spIntegralComparison f l (bottomField l) := by
  unfold diagonalRealizationLinePullMap
  exact ((upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _).symm_apply_apply _

-- Compare normalized endpoints through the derived and module-object presentations.
private theorem derivedUnit_transport
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X S : Scheme.{u}}
    {a b : X ⟶ S} (h : a = b) :
    (Functor.leftDerivedFunctorNatIso _ (CondensedRing.upperStarCongr R h)).hom.app
        (unit R S) ≫ (CondensedRing.leftDerivedUpperStarUnitIso R b).hom =
      (CondensedRing.leftDerivedUpperStarUnitIso R a).hom := by
  subst b
  rw [CondensedRing.upperStarCongr_self, Functor.leftDerivedFunctorNatIso_refl]
  simp

-- Prove compositor cancellation before instantiating the large derived module categories.
private theorem unit_square_of_compositors {C : Type*} [Category C]
    {A B D E T : C} (i : A ≅ B) (j : D ≅ E) (t : A ⟶ D)
    (a : E ⟶ T) (b : B ⟶ T) (u : A ⟶ T) (v : D ⟶ T)
    (hi : i.hom ≫ b = u) (hj : j.hom ≫ a = v) (ht : t ≫ v = u) :
    (i.inv ≫ t ≫ j.hom) ≫ a = b := by
  rw [Category.assoc, Category.assoc, hj, ht, ← hi, Iso.inv_hom_id_assoc]

-- Compare normalized endpoints through the derived and module-object presentations.
private theorem derivedUnit_square
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (hX : X' ⟶ X) (hS : S' ⟶ S)
    (h : f' ≫ hS = hX ≫ f) (cF : UnitPullEndpoint R f)
    (cF' : UnitPullEndpoint R f') (c : UnitPullEndpoint R hS)
    (d : UnitPullEndpoint R hX) :
    let θ := (CondensedRing.leftDerivedUpperStarComp R f' hS).symm ≪≫
      Functor.leftDerivedFunctorNatIso _ (CondensedRing.upperStarCongr R h) ≪≫
      CondensedRing.leftDerivedUpperStarComp R hX f
    θ.hom.app (unit R S) ≫ (derivedUpper R hX).map cF.derived ≫ d.derived =
      (derivedUpper R f').map c.derived ≫ cF'.derived := by
  dsimp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  simp only [unitEndpoint_derived_eq]
  exact unit_square_of_compositors
    ((CondensedRing.leftDerivedUpperStarComp R f' hS).app (unit R S))
    ((CondensedRing.leftDerivedUpperStarComp R hX f).app (unit R S))
    ((Functor.leftDerivedFunctorNatIso _ (CondensedRing.upperStarCongr R h)).hom.app
      (unit R S)) _ _ _ _
    (CondensedRing.leftDerivedUpperStarComp_hom_app_unit R f' hS)
    (CondensedRing.leftDerivedUpperStarComp_hom_app_unit R hX f)
    (derivedUnit_transport R h)

-- Compare normalized endpoints through the derived and module-object presentations.
private theorem normalized_pullback_arrow
    {A B C D E E' : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category E']
    (H : A ⥤ B) (F : A ⥤ C) (F' : B ⥤ D) (P : C ⥤ D)
    (J : E ⥤ C) (G : E ⥤ E') (J' : E' ⥤ D)
    (T : F ⋙ P ≅ H ⋙ F') (M : J ⋙ P ⟶ G ⋙ J')
    {U L : A} {U' L' : B} {V W : E} {V' W' : E'}
    (cu : H.obj U ≅ U') (cl : H.obj L ≅ L')
    (a : F.obj U ⟶ J.obj V) (b : F.obj L ⟶ J.obj W)
    (a' : F'.obj U' ⟶ J'.obj V') (b' : F'.obj L' ⟶ J'.obj W')
    (q : G.obj V ⟶ V') (t : G.obj W ⟶ W')
    (z : U ⟶ L) (θ : V ⟶ W) (θ' : V' ⟶ W')
    (hz : F.map z ≫ b = a ≫ J.map θ)
    (hθ : G.map θ ≫ t = q ≫ θ')
    (hu : T.inv.app U ≫ P.map a ≫ M.app V ≫ J'.map q = F'.map cu.hom ≫ a')
    (hl : T.inv.app L ≫ P.map b ≫ M.app W ≫ J'.map t = F'.map cl.hom ≫ b') :
    F'.map (cu.inv ≫ H.map z ≫ cl.hom) ≫ b' = a' ≫ J'.map θ' := by
  have hn := T.inv.naturality z
  have hm := M.naturality θ
  simp only [Functor.comp_map] at hn hm
  calc
    _ = F'.map cu.inv ≫ F'.map (H.map z) ≫ (F'.map cl.hom ≫ b') := by
      simp only [Functor.map_comp, Category.assoc]
    _ = F'.map cu.inv ≫ F'.map (H.map z) ≫ T.inv.app L ≫
        P.map b ≫ M.app W ≫ J'.map t := by rw [← hl]
    _ = F'.map cu.inv ≫ T.inv.app U ≫ P.map (F.map z) ≫
        P.map b ≫ M.app W ≫ J'.map t := by rw [reassoc_of% hn]
    _ = F'.map cu.inv ≫ T.inv.app U ≫ P.map a ≫
        P.map (J.map θ) ≫ M.app W ≫ J'.map t := by
      rw [← P.map_comp_assoc, hz, P.map_comp]
      simp only [Category.assoc]
    _ = F'.map cu.inv ≫ T.inv.app U ≫ P.map a ≫
        M.app V ≫ J'.map (G.map θ) ≫ J'.map t := by rw [reassoc_of% hm]
    _ = F'.map cu.inv ≫ (T.inv.app U ≫ P.map a ≫ M.app V ≫ J'.map q) ≫
        J'.map θ' := by
      rw [← J'.map_comp, hθ, J'.map_comp]
      simp only [Category.assoc]
    _ = _ := by
      rw [hu]
      simp only [Category.assoc, ← F'.map_comp_assoc, Iso.inv_hom_id, F'.map_id,
        Category.id_comp]

private theorem pullEndpoint_shift_eq
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] {X S : Scheme.{u}} {f : X ⟶ S}
    {M : Modules R S} {N : Modules R X}
    {m m' : (upperStar Ab.{u + 1} f).obj M.X ⟶ N.X}
    (a : PullEndpoint R f M N m) (b : PullEndpoint R f M N m')
    (h : a.iso = b.iso) : a.shift = b.shift := by
  unfold PullEndpoint.shift PullEndpoint.derived
  rw [h]

private theorem realized_arrow_transport
    {A C : Type*} [Category C] {U V W Z : C}
    (F : A → (V ⟶ Z)) (a : U ⟶ V) (b : U ⟶ W)
    {x y : A} {t t' : W ⟶ Z} (hx : x = y) (ht : t = t')
    (h : a ≫ F x = b ≫ t) : a ≫ F y = b ≫ t' := by
  subst y
  subst t'
  exact h

-- Assemble the independent tower, completed, and condensed comparison diagrams.
/-- Whole-system pullback is preserved by the specified completed realizations.

Source: diagonal coefficient changes (3), naturality of the whole Kummer system.
(blueprint: lem-diagonal-local-chern-horizontal-realization).

Proof: use naturality of the Picard-to-H1 extension and of the Kummer boundary
before taking any finite projection. The coefficient and root comparisons
identify the pulled tower class with the tower class of the pulled Picard line.
Restrict this equality to the constant coefficient system and take its derived
limit. Both completed unit and shifted completed line are complete; full
faithfulness of scalar restriction and the invertible line-limit comparison
identify the resulting completed arrows. The underlying-sheaf normalizations of
the exact realizations identify the realized comparison with the actual
condensed inverse image. The unit endpoint is uniquely fixed by its ordinary
adjunct; composition of these unit endpoints agrees with the derived pullback
composition comparison. The root-normalized line endpoint similarly identifies
the shifted target comparison. Compose these identifications around the square;
this gives the displayed equality of local arrows, without taking any right
adjunct or decomposing the pulled Picard class. -/
theorem diagonalLocalChern_horizontal_realization (l : ℕ) [Fact l.Prime]
    {X S X' S' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian S] [IsNoetherian X'] [IsNoetherian S']
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    [DiagonalTraceLocalizations l X'] [DiagonalTraceLocalizations l S']
    (f : X ⟶ S) (f' : X' ⟶ S') (hX : X' ⟶ X) (hS : S' ⟶ S)
    (h : f' ≫ hS = hX ≫ f)
    (hunit : IsUnit (l : Γ(S, ⊤))) (hunit' : IsUnit (l : Γ(S', ⊤)))
    (p : DiagonalTrace.Presentation l (ULift.{u} (Padic l)) f)
    (p' : DiagonalTrace.Presentation l (ULift.{u} (Padic l)) f')
    (eX : CompletedRealization l X) (eX' : CompletedRealization l X')
    (cF : UnitPullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (cF' : UnitPullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) f')
    (line : PullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) hX
      (zlLine l X) (zlLine l X') (spIntegralComparison hX l (bottomField l)))
    (c : UnitPullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) hS)
    (z : DiagonalTrace.completedUnit l X ⟶
      (DiagonalTrace.completedLine l X)⟦(2 : ℤ)⟧)
    (w : DiagonalTrace.completedUnit l X' ⟶
      (DiagonalTrace.completedLine l X')⟦(2 : ℤ)⟧)
    (hz : ModelLocalChernNormalized l p z)
    (hw : (diagonalCompletedUnderlying l X').map w ≫
      DiagonalTrace.shiftedComparison (diagonalCompletedUnderlying l X')
        (p'.restrictionX.F.mapDerivedCategory ⋙ p'.LX.R)
        (p'.coefficientsX.lineMap l (ULift.{u} (Padic l)) p'.LX) 2 =
      p'.coefficientsX.unitMap l (ULift.{u} (Padic l)) p'.LX ≫
        p'.LX.R.map (p'.restrictionX.F.mapDerivedCategory.map
          (SpTowerClasses.firstChern l (ULift.{u} (Padic l)) p'.chernX
            (Scheme.Pic.map hX
              (Scheme.Pic.map p.model.model.hom (SpTowerClasses.hyperplanePic S)))))) :
    let Λ := Profinite.continuousMapRingObj.{u} ℤ_[l]
    let θ := (CondensedRing.leftDerivedUpperStarComp Λ f' hS).symm ≪≫
      Functor.leftDerivedFunctorNatIso _ (CondensedRing.upperStarCongr Λ h) ≪≫
      CondensedRing.leftDerivedUpperStarComp Λ hX f
    θ.hom.app (unit Λ S) ≫
        (derivedUpper Λ hX).map (cF.derived ≫ eX.localChern l X z) ≫ line.shift =
      (derivedUpper Λ f').map c.derived ≫ cF'.derived ≫ eX'.localChern l X' w := by
  have hXunit : IsUnit (l : Γ(X, ⊤)) := by
    simpa only [map_natCast] using hunit.map f.appTop.hom
  have hXunit' : IsUnit (l : Γ(X', ⊤)) := by
    simpa only [map_natCast] using hunit'.map f'.appTop.hom
  -- Select witnesses without rebuilding the large square as an elimination motive.
  have r := Classical.choice (diagonalRealization_pullback l hX hXunit' hXunit eX' eX)
  have d := Classical.choice (diagonalLocalChern_pullback_data l hX p p' hXunit)
  have hu := diagonalLocalChern_coefficient_pullback l hX p p'
    hXunit hXunit' eX eX' r d
  have hl := diagonalLocalChern_root_pullback l hX p p' hXunit hXunit' eX eX' r d
  let H := (diagonalRealizationPull l hX).mapDerivedCategory
  let F := diagonalCompletedUnderlying l X
  let F' := diagonalCompletedUnderlying l X'
  let P := (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) hX).mapDerivedCategory
  let J := p.restrictionX.F.mapDerivedCategory ⋙ p.LX.R
  let J' := p'.restrictionX.F.mapDerivedCategory ⋙ p'.LX.R
  let G := SpTowerShriek.pull l (ULift.{u} (Padic l)) d.base d.geometry
  let cu := diagonalRealizationPullSingle l hX r.completedUnit
  let cl := diagonalRealizationPullShift l hX r.completedLine 2
  let L := Scheme.Pic.map p.model.model.hom (SpTowerClasses.hyperplanePic S)
  let old := SpTowerClasses.firstChern l (ULift.{u} (Padic l)) p.chernX L
  let new := SpTowerClasses.firstChern l (ULift.{u} (Padic l)) p'.chernX
    (Scheme.Pic.map hX L)
  let q := (d.coefficient.derivedIso l (ULift.{u} (Padic l))).hom
  let t := (G.commShiftIso (2 : ℤ)).hom.app
      (SpTowerClasses.line l (ULift.{u} (Padic l)) p.chernX) ≫
    ((d.line.derivedIso l (ULift.{u} (Padic l))).hom)⟦(2 : ℤ)⟧'
  have htower : G.map old ≫ t = q ≫ new := by
    let M := (fromSkeleton X.Modules).obj L.val
    have hM : Scheme.Pic.ofIsInvertible M = L :=
      Scheme.Pic.ofIsInvertible_fromSkeleton L
    have hM' : Scheme.Pic.ofIsInvertible ((Scheme.Modules.pullback hX).obj M) =
        Scheme.Pic.map hX L := by
      apply Scheme.Pic.ext
      rfl
    simpa only [hM, hM'] using tower_firstChern_pullback l (ULift.{u} (Padic l)) hX
      hXunit' hXunit d.base d.geometry p.chernX p'.chernX
      p.normalizedX p'.normalizedX d.coefficient d.line M
  let pulled := cu.inv ≫ H.map z ≫ cl.hom
  have hpulled : F'.map pulled ≫ DiagonalTrace.shiftedComparison F' J'
      (p'.coefficientsX.lineMap l (ULift.{u} (Padic l)) p'.LX) 2 =
      p'.coefficientsX.unitMap l (ULift.{u} (Padic l)) p'.LX ≫ J'.map new := by
    exact normalized_pullback_arrow
      (E := DerivedCategory
        (SpTowerClasses.Systems X (SpTowerClasses.Arings l (ULift.{u} (Padic l)) X)))
      (E' := DerivedCategory
        (SpTowerClasses.Systems X' (SpTowerClasses.Arings l (ULift.{u} (Padic l)) X')))
      H F F' P J G J' (d.completedSquare l) (d.comparison l) cu cl
      (p.coefficientsX.unitMap l (ULift.{u} (Padic l)) p.LX)
      (DiagonalTrace.shiftedComparison F J
        (p.coefficientsX.lineMap l (ULift.{u} (Padic l)) p.LX) 2)
      (p'.coefficientsX.unitMap l (ULift.{u} (Padic l)) p'.LX)
      (DiagonalTrace.shiftedComparison F' J'
        (p'.coefficientsX.lineMap l (ULift.{u} (Padic l)) p'.LX) 2)
      q t z old new (by simpa only [ModelLocalChernNormalized, Functor.comp_map,
        diagonalCompletedUnderlying, DiagonalTrace.completedUnit, F, J, old, L]
          using hz) htower hu hl
  have heq : pulled = w :=
    (DiagonalTrace.diagonalCompletedLocalChern_lift l p' hXunit' new).unique hpulled hw
  have hlineIso := pullEndpoint_iso_unique r.line line (realizationLinePullMap_eq l hX)
  have hline := pullEndpoint_shift_eq r.line line hlineIso
  have harrow := realized_arrow_transport (eX'.localChern l X') r.unit.derived
    ((derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) hX).map
      (eX.localChern l X z)) heq hline (r.arrow z)
  have hunitSquare := derivedUnit_square (Profinite.continuousMapRingObj.{u} ℤ_[l])
    f f' hX hS h cF cF' c r.unit
  simpa only [Functor.map_comp, Category.assoc, harrow] using
    congrArg (fun q ↦ q ≫ eX'.localChern l X' w) hunitSquare

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
