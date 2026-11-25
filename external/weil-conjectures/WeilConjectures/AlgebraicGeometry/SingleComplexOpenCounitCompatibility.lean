/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenBaseChangeComparisons
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenPinnedComposition
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenPinnedAdjunction
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenPullbackCounitRepresentative
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenPinnedCounitUnit
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-! # Open pullback squares and restricted counits

Source: Stacks Project, Tags 08FE, 08HY and 0D5S.
(blueprint: lem-pc-t2-open-counit-compatibility).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem counit_square_of_unit
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (a : L ⊣ R) {A B E H : C} {W Z : D}
    (t₁ : A ⟶ B) (t₂ : B ⟶ E) (d : E ⟶ R.obj Z)
    (q : A ⟶ H) (u : H ⟶ R.obj W) (v : W ⟶ Z) (p : L.obj H ⟶ W)
    (hu : t₁ ≫ t₂ ≫ d = q ≫ u ≫ R.map v)
    (hp : L.map u ≫ a.counit.app W = p) :
    L.map (t₁ ≫ t₂) ≫ (L.map d ≫ a.counit.app Z) = L.map q ≫ p ≫ v := by
  rw [← L.map_comp_assoc, Category.assoc, hu, L.map_comp, L.map_comp]
  simp only [Category.assoc]
  have hn := a.counit.naturality v
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [hn]
  rw [← Category.assoc (L.map u), hp]

/-- The canonical pullback comparison across a commuting square of open inclusions.
Source: Stacks Project, Tag 0D5S, applied to the constructed open pullback comparisons.
(blueprint: def-pc-t2-open-pullback-square-iso). -/
noncomputable def singleComplexOpenPullbackSquareIso
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (s : X ⟶ Y) (U : Y.Opens) (U' : X.Opens)
    (j : U'.toScheme ⟶ U.toScheme) (hj : j ≫ U.ι = U'.ι ≫ s) :
    (schemeOpenRestriction Y U).mapDerivedCategory ⋙ derivedPullback j ≅
      derivedPullback s ⋙ (schemeOpenRestriction X U').mapDerivedCategory := by
  classical
  let c := @singleComplexOpenPinnedComposition.{u, w} _
  let d := Functor.isoWhiskerRight (singleComplexOpenPullbackIso Y U).symm
      (derivedPullback j) ≪≫
    c j U.ι ≪≫ eqToIso (congrArg (fun k ↦ derivedPullback k) hj) ≪≫
      (c U'.ι s).symm ≪≫
        Functor.isoWhiskerLeft (derivedPullback s) (singleComplexOpenPullbackIso X U')
  refine NatIso.ofComponents (fun M ↦
    (derivedPullback j).mapIso ((singleComplexOpenPullbackIso Y U).symm.app M) ≪≫
      (c j U.ι).app M ≪≫
      eqToIso (congrArg (fun k ↦ (derivedPullback k).obj M) hj) ≪≫
      (c U'.ι s).symm.app M ≪≫
      (singleComplexOpenPullbackIso X U').app ((derivedPullback s).obj M)) ?_
  intro M N v
  simpa only [d, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Iso.app_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.mapIso_hom,
    eqToIso.hom, eqToHom_app, Category.assoc] using d.hom.naturality v

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The sectionwise direct-image comparison is the mate of the open pullback square.
Source: Stacks Project, cohomology.tex, Tags 08FE, 08BS and 08HY.
(blueprint: lem-pc-t2-open-counit-compatibility).

Proof: Compute direct image on a K-injective complex. Open restriction preserves
K-injectivity, since exact extension by zero is its left adjoint. The underived
comparison used in singleComplexOpenDirectImageIso is the sectionwise identity
on inverse-image opens. Under the tensor-pullback adjunction its mate is the
open pullback comparison: both counit composites evaluate the same restricted
tensor on sections. Derive this equality using the right-derived factorization
identities and the left-derived counits defining the composition comparisons.
The Hom equivalences of the chosen adjunctions are pinned to these same counits
and right-derived units by exists_schemeDerivedAdjunction. Thus the equality on
representatives descends to the displayed equality in the derived category.
This is an identity of natural transformations, including empty opens and zero
objects; no boundedness assumption is used. -/
theorem singleComplexOpen_counit_compatibility
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (K : schemeDerivedCategory X) :
    let a := @singleComplexOpenPinnedAdjunction.{u, w} _
    let RX := (schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory
    (derivedPullback (f ∣_ V)).map ((singleComplexOpenDirectImageIso f V).hom.app K) ≫
        (a (f ∣_ V)).counit.app (RX.obj K) =
      (singleComplexOpenPullbackSquareIso f V (f ⁻¹ᵁ V) (f ∣_ V)
        (morphismRestrict_ι f V)).hom.app ((schemeDerivedDirectImage f).obj K) ≫
          RX.map ((a f).counit.app K) := by
  classical
  let a := @singleComplexOpenPinnedAdjunction.{u, w} _
  let RX := (schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory
  let RY := (schemeOpenRestriction Y V).mapDerivedCategory
  let L₀ := derivedPullback (f ∣_ V)
  let F := schemeDerivedDirectImage f
  let P := F ⋙ RY ⋙ L₀
  let α : P ⟶ RX :=
    Functor.whiskerRight (singleComplexOpenDirectImageIso f V).hom L₀ ≫
      Functor.whiskerLeft RX (a (f ∣_ V)).counit
  let β : P ⟶ RX :=
    Functor.whiskerLeft F
        (singleComplexOpenPullbackSquareIso f V (f ⁻¹ᵁ V) (f ∣_ V)
          (morphismRestrict_ι f V)).hom ≫
      Functor.whiskerRight (a f).counit RX
  have hrep (I : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) [I.IsKInjective] :
      α.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj I)) =
        β.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj I)) := by
    let J := (HomotopyCategory.quotient _ (.up ℤ)).obj I
    let rY := schemeOpenRestriction Y V
    let rX := schemeOpenRestriction X (f ⁻¹ᵁ V)
    let G := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    let G₀ := RingedSpace.moduleDirectImage (f ∣_ V).toLRSHom.toShHom
    let t := rY.mapDerivedCategoryFactorsh.inv.app
        ((G.mapHomotopyCategory (.up ℤ)).obj J) ≫
      RY.map (G.rightDerivedFunctorUnit.app J)
    have : IsIso (G.rightDerivedFunctorUnit.app J) := inferInstance
    have : IsIso t := inferInstance
    rw [← cancel_epi (L₀.map t)]
    change L₀.map t ≫ (L₀.map ((singleComplexOpenDirectImageIso f V).hom.app _) ≫
        (a (f ∣_ V)).counit.app _) = _
    refine (counit_square_of_unit (a (f ∣_ V)) _ _ _ _ _ _ _
      (singleComplexOpen_directImage_unit f V J)
      (singleComplexOpen_pinned_counit_unit (f ∣_ V)
        ((rX.mapHomotopyCategory (.up ℤ)).obj J))).trans ?_
    have hp := singleComplexOpen_pullback_counit_representative f V J
    simpa only [singleComplexOpenPullbackSquareIso, β, t, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatIso.ofComponents_hom_app,
      Category.assoc] using hp.symm
  obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective K
  have he : K ≅ DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient _ (.up ℤ)).obj I) :=
    e ≪≫ ((DerivedCategory.quotientCompQhIso _).app I).symm
  change α.app K = β.app K
  apply (cancel_mono (RX.map he.hom)).1
  exact (α.naturality he.hom).symm.trans
    ((congrArg (fun k ↦ P.map he.hom ≫ k) (hrep I)).trans (β.naturality he.hom))


end AlgebraicGeometry
