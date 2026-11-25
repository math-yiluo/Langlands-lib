/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerClasses
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowersAbelian
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Chern.TowerChernRealizationPullback

/-! # Pullback of the Kummer Chern morphism in coefficient towers

Source: blueprint, sec-smooth-purity/sk-prop-sp-tower-geometric,
classes proof paragraph (2) (blueprint: lem-sp-tower-chern-pullback).
The equality is in the ordinary derived category of entire varying-ring systems.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

open SpTowerClasses

/-- Kummer Chern morphisms commute with arbitrary scheme pullback, with the unit
and root-tensor comparisons normalized on sections and the canonical shift comparison.
Source: blueprint classes proof (2) (blueprint: lem-sp-tower-chern-pullback).

Proof plan:
1. Exact inverse image on the system topos transports the integral, finite and
O_E/ell^n coefficient systems. Root pullback respects the power transitions
(lem-coef-semilinear-derived-sections; lemma-inverse-image-coefficient-sheaves--2).
2. Glue the line-bundle extension by (u,m)_b -> (g_ab^m u,m)_a; its fibre at 1
is the frame torsor of L. Its constant-system boundary is lineBundleClass
(lemma-cohomology-multiplicative-group--3; lemma-cohomology-multiplicative-group--3;
ext-one-extension-classification).
3. Pullback of units gives (u,m) -> (a(u),m) between these extensions, so
naturality of short-exact-sequence boundaries transports the integral class.
No isomorphism on all units and no flatness of the scheme morphism is needed.
4. Apply unit-normalized derived scalar extension on the entire diagram;
algebra-diagram-pullback-extension-coherence identifies the source comparisons.
5. Resolve Z/ell^n by [Z --ell^n--> Z] with transition (ell,1). Tensoring with
units has its only cohomology in degree -1, namely the roots tower. The positive
kernel inclusion fixes the target normalization. The homotopy h^0 = identity
gives j inverse b = -p v inverse, the same connecting-morphism sign convention.
6. On these models the pulled map is (a,a); on kernels it is exactly root
pullback. Fully faithful shifted single functors identify these whole-system
maps, rather than relying on faithfulness of finite-level evaluation.
7. Extend to O_E/ell^n using successive-derived-quotient-normalization.
Compatible root generators make the root tower flat; the target comparison is
u tensor b -> r(u) tensor b and respects u tensor b -> u^ell tensor bar(b).
The source is the coefficient-unit comparison, giving the displayed equality.
-/
theorem tower_firstChern_pullback
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (_hX : IsUnit (l : Γ(X, ⊤))) (_hY : IsUnit (l : Γ(Y, ⊤)))
    (b : SpTowerShriek.Base l E) (g : SpTowerShriek.Geometry l E b f)
    (cY : Chern l E Y) (cX : Chern l E X)
    (_nY : cY.Normalized l E) (_nX : cX.Normalized l E)
    (θ₀ : CoefficientPullback l E b f g) (θ₁ : LinePullback l E f g cY cX)
    (L : Y.Modules) [Scheme.Modules.IsInvertible L] :
    (SpTowerShriek.pull l E b g).map
        (firstChern l E cY (Scheme.Pic.ofIsInvertible L)) ≫
      ((SpTowerShriek.pull l E b g).commShiftIso (2 : ℤ)).hom.app (line l E cY) ≫
      ((θ₁.derivedIso l E).hom)⟦(2 : ℤ)⟧' =
    (θ₀.derivedIso l E).hom ≫
      firstChern l E cX (Scheme.Pic.ofIsInvertible ((Scheme.Modules.pullback f).obj L)) := by
  obtain ⟨η, hs, ht⟩ := tower_chernRealization_pullback l E f _hX _hY b g
    cY cX _nY _nX θ₀ θ₁
  let P := SpTowerShriek.pull l E b g
  let R := chernRealization l E cX
  let classY := lineBundleClass Y (Scheme.Pic.ofIsInvertible L)
  let classX := lineBundleClass X
    (Scheme.Pic.ofIsInvertible ((Scheme.Modules.pullback f).obj L))
  have hn := η.naturality classY
  change P.map ((chernRealization l E cY).map classY) ≫ η.app _ =
    η.app _ ≫ R.map ((abPull f).mapDerivedCategory.map classY) at hn
  have hi : (abPull f).mapDerivedCategory.map classY ≫ unitsDerivedPull f =
      integerDerivedPull f ≫ classX := tower_integralClass_pullback f L
  have hu : P.map (chernSource l E cY).inv ≫ η.app _ ≫
      R.map (integerDerivedPull f) =
        (θ₀.derivedIso l E).hom ≫ (chernSource l E cX).inv := by
    apply (cancel_mono (chernSource l E cX).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hs]
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id,
      Category.id_comp]
  have hc : P.map ((chernRealization l E cY).map classY) ≫
      P.map (chernTarget l E cY) ≫
      (P.commShiftIso (2 : ℤ)).hom.app (line l E cY) ≫
      ((θ₁.derivedIso l E).hom)⟦(2 : ℤ)⟧' =
        η.app _ ≫ R.map (integerDerivedPull f) ≫ R.map classX ≫ chernTarget l E cX := by
    calc
      _ = P.map ((chernRealization l E cY).map classY) ≫
          η.app _ ≫ R.map (unitsDerivedPull f) ≫ chernTarget l E cX := by
            rw [ht]
      _ = η.app _ ≫ R.map ((abPull f).mapDerivedCategory.map classY) ≫
          R.map (unitsDerivedPull f) ≫ chernTarget l E cX := by
            simpa only [Category.assoc] using
              congrArg (fun k ↦ k ≫ R.map (unitsDerivedPull f) ≫ chernTarget l E cX) hn
      _ = _ := by
        rw [← R.map_comp_assoc, hi, R.map_comp]
        simp only [Category.assoc]
  rw [firstChern_eq_realization, firstChern_eq_realization]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  change P.map (chernSource l E cY).inv ≫
    (P.map ((chernRealization l E cY).map classY) ≫ P.map (chernTarget l E cY) ≫
      (P.commShiftIso (2 : ℤ)).hom.app (line l E cY) ≫
      ((θ₁.derivedIso l E).hom)⟦(2 : ℤ)⟧') = _
  rw [hc]
  simpa only [Category.assoc] using
    congrArg (fun k ↦ k ≫ R.map classX ≫ chernTarget l E cX) hu

end AlgebraicGeometry.ProEtale
