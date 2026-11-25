/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerClasses
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.TowerIntegralClassPullback
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Chern.TowerChernReductionPullback
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Chern.TowerChernScalarPullback

/-! # Coefficient realization of integral tower classes and pullback

Source: blueprint classes proof (2), and lem-sp-tower-chern-pullback, steps 4--7
(blueprint: lem-sp-tower-chern-realization-pullback).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The actual successive derived coefficient extension, before applying it to a class.
Source: classes (2) (blueprint: lem-sp-tower-chern-realization-pullback). -/
def chernRealization {T : Scheme.{u}} (c : Chern l E T) :
    DerivedCategory (Ab T) ⥤ D T (Arings l E T) :=
  c.reduction.derived ⋙ c.scalar.T

/-- The composite of the two specified coefficient-unit identifications.
Source: classes (2) (blueprint: lem-sp-tower-chern-realization-pullback). -/
def chernSource {T : Scheme.{u}} (c : Chern l E T) :
    (chernRealization l E c).obj
        ((DerivedCategory.singleFunctor (Ab T) 0).obj (integers T)) ≅
      unit T (Arings l E T) :=
  c.scalar.T.mapIso c.unitIso ≪≫ c.scalarUnit

/-- Realization of the full-units target, with positive Kummer kernel and scalar counit.
Source: classes (2) (blueprint: lem-sp-tower-chern-realization-pullback). -/
def chernTarget {T : Scheme.{u}} (c : Chern l E T) :
    (chernRealization l E c).obj
        (((DerivedCategory.singleFunctor (Ab T) 0).obj (units T))⟦(1 : ℤ)⟧) ⟶
      (line l E c)⟦(2 : ℤ)⟧ :=
  c.scalar.T.map c.rootIso.hom ≫
    (c.scalar.T.commShiftIso (2 : ℤ)).hom.app
      ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj c.rootModule) ≫
    (lineComparison l E c)⟦(2 : ℤ)⟧'

/-- The first Chern definition factors through integral realization.
Source: classes (2) (blueprint: lem-sp-tower-chern-realization-pullback). -/
theorem firstChern_eq_realization {T : Scheme.{u}} (c : Chern l E T) (L : T.Pic) :
    firstChern l E c L =
      (chernSource l E c).inv ≫ (chernRealization l E c).map (lineBundleClass T L) ≫
        chernTarget l E c := by
  simp only [firstChern, firstChernR, chernSource, chernRealization, chernTarget,
    Iso.trans_inv, CategoryTheory.Functor.mapIso_inv, CategoryTheory.Functor.comp_map,
    CategoryTheory.Functor.map_comp, Category.assoc]

private theorem scalar_comparison_paste
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {C' : Type u₃} [Category.{v₃} C'] {D' : Type u₄} [Category.{v₄} D']
    (S : C ⥤ D) (S' : C' ⥤ D') (P : C ⥤ C') (Q : D ⥤ D')
    (κ : S ⋙ Q ⟶ P ⋙ S')
    {M U : C} {M' U' : C'} {V : D} {V' : D'}
    (a : M ⟶ U) (a' : M' ⟶ U') (r : P.obj M ⟶ M') (t : P.obj U ⟶ U')
    (v : S.obj U ⟶ V) (v' : S'.obj U' ⟶ V') (w : Q.obj V ⟶ V')
    (hr : r ≫ a' = P.map a ≫ t)
    (hs : κ.app U ≫ S'.map t ≫ v' = Q.map v ≫ w) :
    κ.app M ≫ S'.map r ≫ S'.map a' ≫ v' = Q.map (S.map a ≫ v) ≫ w := by
  calc
    _ = κ.app M ≫ S'.map (r ≫ a') ≫ v' := by
      simp only [Functor.map_comp, Category.assoc]
    _ = κ.app M ≫ S'.map (P.map a ≫ t) ≫ v' := by rw [hr]
    _ = Q.map (S.map a) ≫ κ.app U ≫ S'.map t ≫ v' := by
      simpa only [Functor.map_comp, Functor.comp_map, Category.assoc] using
        congrArg (fun z ↦ z ≫ S'.map t ≫ v') (κ.naturality a).symm
    _ = Q.map (S.map a) ≫ (Q.map v ≫ w) := by rw [hs]
    _ = _ := by simp only [Functor.map_comp, Category.assoc]

/-- Geometric inverse image commutes with the successive coefficient realization. The
comparison is natural on all integral derived objects, has the coefficient-unit source,
and carries the full-units target map to the specified root-tensor comparison. This
assertion involves no line bundle or Chern class.
Source: blueprint classes proof (2); lem-sp-tower-chern-pullback, steps 4--7
(blueprint: lem-sp-tower-chern-realization-pullback).

Proof: first construct the exact inverse image of the intermediate R-module
systems and its scalar-extension comparison kappa by tower_chernScalar_pullback.
Then apply tower_chernReduction_pullback to that same inverse image, obtaining
rho between integral reductions. Whisker kappa on the left by the reduction on Y,
whisker rho on the right by scalar extension on X, and compose to obtain eta.
For either endpoint, combine the two reduction factors under scalar extension,
substitute rho's endpoint equation, and use naturality of kappa with respect to
the unit or root identification. Kappa's endpoint equation then gives exactly
the required coefficient or line comparison. Functoriality of scalar extension
and pullback supplies the final composition equations. The private lemma
scalar_comparison_paste proves this calculation uniformly for both endpoints.
All comparisons are in the derived categories of whole systems. -/
theorem tower_chernRealization_pullback
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (_hX : IsUnit (l : Γ(X, ⊤))) (_hY : IsUnit (l : Γ(Y, ⊤)))
    (b : SpTowerShriek.Base l E) (g : SpTowerShriek.Geometry l E b f)
    (cY : Chern l E Y) (cX : Chern l E X)
    (_nY : cY.Normalized l E) (_nX : cX.Normalized l E)
    (θ₀ : CoefficientPullback l E b f g) (θ₁ : LinePullback l E f g cY cX) :
    ∃ η : chernRealization l E cY ⋙ SpTowerShriek.pull l E b g ⟶
        (abPull f).mapDerivedCategory ⋙ chernRealization l E cX,
      η.app ((DerivedCategory.singleFunctor (Ab Y) 0).obj (integers Y)) ≫
          (chernRealization l E cX).map (integerDerivedPull f) ≫
          (chernSource l E cX).hom =
        (SpTowerShriek.pull l E b g).map (chernSource l E cY).hom ≫
          (θ₀.derivedIso l E).hom ∧
      η.app (((DerivedCategory.singleFunctor (Ab Y) 0).obj (units Y))⟦(1 : ℤ)⟧) ≫
          (chernRealization l E cX).map (unitsDerivedPull f) ≫ chernTarget l E cX =
        (SpTowerShriek.pull l E b g).map (chernTarget l E cY) ≫
          ((SpTowerShriek.pull l E b g).commShiftIso (2 : ℤ)).hom.app (line l E cY) ≫
          ((θ₁.derivedIso l E).hom)⟦(2 : ℤ)⟧' := by
  obtain ⟨d, κ, hκ₀, hκ₁⟩ :=
    tower_chernScalar_pullback l E f _hX _hY b g cY cX _nY _nX θ₀ θ₁
  obtain ⟨ρ, hρ₀, hρ₁⟩ :=
    tower_chernReduction_pullback l E f _hX _hY cY cX _nY _nX d
  let η : chernRealization l E cY ⋙ SpTowerShriek.pull l E b g ⟶
      (abPull f).mapDerivedCategory ⋙ chernRealization l E cX :=
    Functor.whiskerLeft cY.reduction.derived κ ≫ Functor.whiskerRight ρ cX.scalar.T
  refine ⟨η, ?_, ?_⟩
  · have h := scalar_comparison_paste cY.scalar.T cX.scalar.T
      d.pull.mapDerivedCategory (SpTowerShriek.pull l E b g) κ
      cY.unitIso.hom
      (cX.reduction.derived.map (integerDerivedPull f) ≫ cX.unitIso.hom)
      (ρ.app ((DerivedCategory.singleFunctor (Ab Y) 0).obj (integers Y)))
      d.derivedUnit.hom cY.scalarUnit.hom cX.scalarUnit.hom
      (θ₀.derivedIso l E).hom hρ₀ hκ₀
    simpa only [η, chernRealization, chernSource, Iso.trans_hom, Functor.mapIso_hom,
      Functor.comp_map, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.map_comp, Category.assoc] using h
  · have h := scalar_comparison_paste cY.scalar.T cX.scalar.T
      d.pull.mapDerivedCategory (SpTowerShriek.pull l E b g) κ
      cY.rootIso.hom
      (cX.reduction.derived.map (unitsDerivedPull f) ≫ cX.rootIso.hom)
      (ρ.app (((DerivedCategory.singleFunctor (Ab Y) 0).obj (units Y))⟦(1 : ℤ)⟧))
      (d.derivedRoot 2).hom (scalarRootTarget cY) (scalarRootTarget cX)
      (((SpTowerShriek.pull l E b g).commShiftIso (2 : ℤ)).hom.app (line l E cY) ≫
        ((θ₁.derivedIso l E).hom)⟦(2 : ℤ)⟧') hρ₁ hκ₁
    simpa only [η, chernRealization, chernTarget, scalarRootTarget,
      Functor.comp_map, Functor.comp_obj, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.map_comp, Category.assoc,
      D, Systems, SpTowerShriek.S, SpTowerShriek.B, SpTowerShriek.tau,
      WeilConjectures.SemilinearSections.D, WeilConjectures.SemilinearSections.DS,
      WeilConjectures.SemilinearSections.Systems] using! h

end AlgebraicGeometry.ProEtale.SpTowerClasses
