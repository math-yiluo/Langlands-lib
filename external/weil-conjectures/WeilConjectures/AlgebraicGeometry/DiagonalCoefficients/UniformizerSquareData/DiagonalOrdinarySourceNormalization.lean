/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerSquareData.DiagonalOrdinarySourceMaps
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalSourceAdjunctionTransport
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientUnitNormalization

/-! # Normalization of the ordinary supported source square

Source: diagonal tower coefficient changes (1), scalar units and finite constants.
(blueprint: lem-diagonal-ordinary-source-normalization).
-/

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

-- Use the module-sheaf abelian structure of GeoCartierClass.
attribute [local instance 100000] sheafIsAbelian
attribute [local instance 200000] AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
attribute [local instance 300000] CommRing.toRing
attribute [local instance 400000] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] derivedScalars quotientLine quotientLineMap cyclicLine cyclicLineMap
  Functor.leftDerivedFunctor Mod.derivedExtendMapDerivedCategoryAdjunction
  HasDerivedCategory.standard DerivedCategory.singleFunctors HomotopyCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ
  Functor.mapDerivedCategory Functor.mapDerivedCategorySingleFunctor
  CondensedRing.lowerStar Profinite.continuousMapRingSheaf
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.ofIsGrothendieckAbelian

attribute [local semireducible] UniformizerSquareData.cyclicEndpoints
  UniformizerSquareData.quotientEndpoints

attribute [local instance] UniformizerSquareData.inverse_additive
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem finite_transpose_underlying
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] {B : Type (u + 1)} [CommRing B]
    {X : Scheme.{u}} (e : FiniteRealization R B X) (M : Modules R X)
    (N : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B))
    (f : e.F.obj M ⟶ N) :
    (e.F.asEquivalence.toAdjunction.homEquiv _ _ f).hom ≫
        (UniformizerSquareData.inverseUnderlying e N).hom =
      e.underlying.inv.app M ≫
        (sheafCompose (Scheme.ProEt.topology X)
          (forget₂ (ModuleCat.{u + 1} B) Ab.{u + 1})).map f := by
  exact equivalence_forget_transpose e.F.asEquivalence
    (sheafCompose (Scheme.ProEt.topology X) (forget₂ (ModuleCat.{u + 1} B) Ab.{u + 1}))
    (Mod.forget _) e.underlying f

private theorem inverse_underlying_naturality
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] {B : Type (u + 1)} [CommRing B]
    {X : Scheme.{u}} (e : FiniteRealization R B X)
    {M N : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)} (f : M ⟶ N) :
    (e.F.asEquivalence.inverse.map f).hom ≫
        (UniformizerSquareData.inverseUnderlying e N).hom =
      (UniformizerSquareData.inverseUnderlying e M).hom ≫
        (sheafCompose (Scheme.ProEt.topology X)
          (forget₂ (ModuleCat.{u + 1} B) Ab.{u + 1})).map f := by
  exact equivalence_forget_inverse_naturality e.F.asEquivalence
    (sheafCompose (Scheme.ProEt.topology X) (forget₂ (ModuleCat.{u + 1} B) Ab.{u + 1}))
    (Mod.forget _) e.underlying f

attribute [local semireducible] CondensedRing.lowerStar

private theorem supported_underlying
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] (Y : Scheme.{u})
    (v : Mod.regular (condensedRingObj R (ProjectiveLine Y)) ⟶
      (Mod.comap (coefficientMap a (ProjectiveLine Y))).obj
        (Mod.regular (condensedRingObj S (ProjectiveLine Y)))) :
    (supportMap a Y v).hom = (lowerStar Ab.{u + 1} (diagonalImmersion Y)).map v.hom := by
  unfold supportMap
  simp only [Mod.comp_hom', CondensedRing.lowerStar_map_hom]
  have h := Mod.comapMapModComapIso_hom_app_hom
    (lowerStar Ab.{u + 1} (diagonalImmersion Y))
    (coefficientMap a (ProjectiveLine Y)) (coefficientMap a (diagonalSurface Y))
    (condensedPushforwardHom R (diagonalImmersion Y))
    (condensedPushforwardHom S (diagonalImmersion Y))
    (condensedPushforwardHom_comp_map_coefficientMap a (diagonalImmersion Y)).symm
    (Mod.regular (condensedRingObj S (ProjectiveLine Y)))
  have hi : ((CondensedRing.comapLowerStarIso a (diagonalImmersion Y)).inv.app
      (Mod.regular (condensedRingObj S (ProjectiveLine Y)))).hom = 𝟙 _ := by
    have hc := congrArg Mod.Hom.hom
      ((CondensedRing.comapLowerStarIso a (diagonalImmersion Y)).inv_hom_id_app
        (Mod.regular (condensedRingObj S (ProjectiveLine Y))))
    change _ ≫ _ = 𝟙 _ at hc
    erw [h, Category.comp_id] at hc
    exact hc
  erw [hi, Category.comp_id]

private theorem normalized_composites
    {C : Type*} [Category C] {X Y Z Z' T T' A B A' B' : C}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z')
    (u : Z ⟶ T) (v : T ⟶ A) (u' : Z' ⟶ T') (v' : T' ⟶ B)
    (m : B ⟶ A) (cA : A ≅ A') (cB : B ≅ B') (φ : B' ⟶ A')
    (f : Z ⟶ A') (g : Z' ⟶ B')
    (hf : u ≫ v ≫ cA.hom = f) (hg : u' ≫ v' ≫ cB.hom = g)
    (hm : m ≫ cA.hom = cB.hom ≫ φ) (h : a ≫ b ≫ f = c ≫ g ≫ φ) :
    a ≫ b ≫ u ≫ v = c ≫ u' ≫ v' ≫ m := by
  apply (cancel_mono cA.hom).mp
  simp only [Category.assoc]
  rw [hm, hf, reassoc_of% hg]
  exact h

open CategoryTheory.MonoidalCategory MonObj in
private theorem padic_unital_maps_ext (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) (r : ℕ)
    (T : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj T]
    (hT : (l ^ r) • 𝟙 T = 0)
    (f g : condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X ⟶ T)
    [IsMonHom f] [IsMonHom g] : f = g := by
  apply diagonal_padic_unit_ext l X r T hT f g
  rw [IsMonHom.one_hom f, IsMonHom.one_hom g]

private theorem normalized_ordinary_square
    {C : Type*} [Category C] {X U V Z U' V' : C}
    (v : X ⟶ U) (w : X ⟶ V) (s : U ⟶ Z) (r : V ⟶ Z)
    (cu : U ≅ U') (cv : V ≅ V') (cz : Z ≅ U')
    (m : V' ⟶ U') (f : X ⟶ U') (g : X ⟶ V')
    (hs : s = cu.hom ≫ cz.inv) (hr : r ≫ cz.hom = cv.hom ≫ m)
    (hv : v ≫ cu.hom = f) (hw : w ≫ cv.hom = g) (h : f = g ≫ m) :
    v ≫ s = w ≫ r := by
  apply (cancel_mono cz.hom).mp
  simp only [Category.assoc, hs, Iso.inv_hom_id, Category.comp_id, hr]
  rw [hv, ← Category.assoc, hw, h]

private theorem supported_endpoint_underlying
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    {a : R ⟶ S} [IsMonHom a] {Y : Scheme.{u}}
    (c : Endpoint a (Mod.regular (condensedRingObj R (ProjectiveLine Y)))
      (Mod.regular (condensedRingObj S (ProjectiveLine Y)))
      (coefficientMap a (ProjectiveLine Y)))
    (d : Endpoint a (source R Y) (source S Y) (supportMap a Y c.semilinear.hom).hom) :
    d.semilinear.hom.hom =
      (lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
        (coefficientMap a (ProjectiveLine Y)) := by
  exact d.semilinear.underlying.trans
    ((supported_underlying a Y c.semilinear.hom).trans
      (congrArg (lowerStar Ab.{u + 1} (diagonalImmersion Y)).map c.semilinear.underlying))

private theorem finite_source_transpose_underlying
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] {A : Type (u + 1)} [CommRing A] {Y : Scheme.{u}}
    (eP : FiniteRealization R A (ProjectiveLine Y))
    (eW : FiniteRealization R A (diagonalSurface Y))
    (c : FiniteSourceComparison R A Y eP eW) :
    (eW.F.asEquivalence.toAdjunction.homEquiv _ _ c.iso.hom).hom ≫
        (UniformizerSquareData.inverseUnderlying eW _).hom =
      (lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
        (eP.underlying.inv.app (Mod.regular _) ≫
          (sheafCompose (Scheme.ProEt.topology (ProjectiveLine Y))
            (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})).map eP.unitIso.hom) := by
  exact (finite_transpose_underlying eW _ _ c.iso.hom).trans (eq_of_heq c.normalization)

private theorem two_maps_normalized
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y Z W : C} {T : D}
    (f : F.obj X ⟶ F.obj Y) (g : F.obj Y ⟶ F.obj Z)
    (h : F.obj Z ⟶ T) (u : T ⟶ F.obj W)
    (a : X ⟶ Y) (b : Y ⟶ Z) (r : Z ⟶ W)
    (hf : f = F.map a) (hg : g = F.map b) (hh : h ≫ u = F.map r) :
    ((f ≫ g) ≫ h) ≫ u = F.map (a ≫ b ≫ r) := by
  rw [Category.assoc, hh, hf, hg, ← F.map_comp, ← F.map_comp, Category.assoc]

private theorem one_map_normalized
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y Z : C} {T : D} (f : F.obj X ⟶ F.obj Y)
    (h : F.obj Y ⟶ T) (u : T ⟶ F.obj Z) (a : X ⟶ Y) (r : Y ⟶ Z)
    (hf : f = F.map a) (hh : h ≫ u = F.map r) :
    (f ≫ h) ≫ u = F.map (a ≫ r) := by
  rw [Category.assoc, hh, hf, ← F.map_comp]

private theorem mapped_coefficient_square
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y Z Z' T T' A B : C}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z')
    (u : Z ⟶ T) (v : T ⟶ A) (u' : Z' ⟶ T') (v' : T' ⟶ B) (m : B ⟶ A)
    (h : a ≫ b ≫ u ≫ v = c ≫ u' ≫ v' ≫ m) :
    F.map (a ≫ b ≫ u ≫ v) = F.map (c ≫ u' ≫ v') ≫ F.map m := by
  rw [← F.map_comp]
  apply congrArg F.map
  simpa only [Category.assoc] using h

namespace UniformizerSquareData

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
  {E : PadicAlgCl.FiniteIntermediateField l} {π : PadicAlgCl.integers l E} {n : ℕ}
  {A : Type (u + 1)} [CommRing A] {hA : ((l ^ (n + 1) : ℕ) : A) = 0}
  (q : UniformizerSquareData l Y E π n A hA)

private theorem ordinary_coefficient_eq :
    coefficientMap (integralMap l E) (ProjectiveLine Y) ≫
        coefficientMap (quotientMap l E π n) (ProjectiveLine Y) ≫
        q.eP.underlying.inv.app
          (Mod.regular (condensedRingObj
            (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) (ProjectiveLine Y))) ≫
        (sheafCompose (Scheme.ProEt.topology (ProjectiveLine Y))
          (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})).map q.eP.unitIso.hom =
      coefficientMap (cyclicMap l n) (ProjectiveLine Y) ≫
        q.cyclic.eP.underlying.inv.app
            (Mod.regular (condensedRingObj
              (Profinite.continuousMapRingObj.{u} (ZMod (l ^ (n + 1)))) (ProjectiveLine Y))) ≫
        (sheafCompose (Scheme.ProEt.topology (ProjectiveLine Y))
          (forget₂ (ModuleCat.{u + 1} (diagonalResidue.{u} l n)) Ab.{u + 1})).map
            q.cyclic.eP.unitIso.hom ≫
        (sheafCompose (Scheme.ProEt.topology (ProjectiveLine Y))
          (forget₂ (ModuleCat.{u + 1} (diagonalResidue.{u} l n)) Ab.{u + 1})).map
            q.maps.source := by
  let X := ProjectiveLine Y
  let UA := sheafCompose (Scheme.ProEt.topology X)
    (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})
  let UB := sheafCompose (Scheme.ProEt.topology X)
    (forget₂ (ModuleCat.{u + 1} (diagonalResidue.{u} l n)) Ab.{u + 1})
  let cA := finiteConstantAbComparison A X
  let cB := finiteConstantAbComparison (diagonalResidue.{u} l n) X
  let φ := (sfbConstantRing X).map
    (RingCat.ofHom (cartierResidueAlgebra l (n + 1) A hA))
  have hn : cB.inv ≫ UB.map q.maps.source ≫ cA.hom = φ.hom :=
    normalized_constant_map (cartierResidueAlgebra l (n + 1) A hA) X
      q.maps.source q.maps.source_normalization
  have hc : UB.map q.maps.source ≫ cA.hom = cB.hom ≫ φ.hom := by
    calc
      _ = cB.hom ≫ (cB.inv ≫ UB.map q.maps.source ≫ cA.hom) := by
        simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      _ = _ := congrArg (fun f ↦ cB.hom ≫ f) hn
  have hA' : (l ^ (n + 1)) • 𝟙 (AddCommGrpCat.of A) = 0 := by
    ext a
    change (l ^ (n + 1)) • a = 0
    erw [nsmul_eq_mul, hA, zero_mul]
  have hT : (l ^ (n + 1)) • 𝟙 (((sfbConstantRing X).obj (RingCat.of A)).X) = 0 := by
    have ht := congrArg (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map hA'
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero] at ht
    exact ht
  have hcoeff : coefficientMap (integralMap l E) X ≫
      coefficientMap (quotientMap l E π n) X ≫ q.eP.coefficient.hom.hom =
      coefficientMap (cyclicMap l n) X ≫ q.cyclic.eP.coefficient.hom.hom ≫ φ.hom := by
    exact padic_unital_maps_ext l X (n + 1) _ hT _ _
  exact normalized_composites
    (coefficientMap (integralMap l E) X) (coefficientMap (quotientMap l E π n) X)
    (coefficientMap (cyclicMap l n) X)
    (q.eP.underlying.inv.app (Mod.regular _)) (UA.map q.eP.unitIso.hom)
    (q.cyclic.eP.underlying.inv.app (Mod.regular _)) (UB.map q.cyclic.eP.unitIso.hom)
    (UB.map q.maps.source) cA cB φ.hom q.eP.coefficient.hom.hom
    q.cyclic.eP.coefficient.hom.hom q.eP.unit_normalization q.cyclic.eP.unit_normalization
    hc hcoeff

private theorem quotient_underlying :
    q.quotientOrdinary.hom ≫
        (inverseUnderlying q.eW
          ((lowerStar (ModuleCat.{u + 1} A) (diagonalImmersion Y)).obj
            (geoCartierConstant A (ProjectiveLine Y)))).hom =
      (lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
        (coefficientMap (integralMap l E) (ProjectiveLine Y) ≫
          coefficientMap (quotientMap l E π n) (ProjectiveLine Y) ≫
          q.eP.underlying.inv.app (Mod.regular _) ≫
          (sheafCompose (Scheme.ProEt.topology (ProjectiveLine Y))
            (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})).map q.eP.unitIso.hom) := by
  unfold quotientOrdinary quotientScalarOrdinary
  exact two_maps_normalized
    (X := condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) (ProjectiveLine Y))
    (Y := condensedRingObj
      (Profinite.continuousMapRingObj.{u} (PadicAlgCl.integers l E)) (ProjectiveLine Y))
    (Z := condensedRingObj
      (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) (ProjectiveLine Y))
    (W := (sheafCompose (Scheme.ProEt.topology (ProjectiveLine Y))
      (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})).obj
        (geoCartierConstant A (ProjectiveLine Y)))
    (lowerStar Ab.{u + 1} (diagonalImmersion Y))
    q.route.first.supported.semilinear.hom.hom q.route.second.supported.semilinear.hom.hom
    (q.eW.F.asEquivalence.toAdjunction.homEquiv _ _ q.sourceComparison.iso.hom).hom
    (inverseUnderlying q.eW
      ((lowerStar (ModuleCat.{u + 1} A) (diagonalImmersion Y)).obj
        (geoCartierConstant A (ProjectiveLine Y)))).hom
    (coefficientMap (integralMap l E) (ProjectiveLine Y))
    (coefficientMap (quotientMap l E π n) (ProjectiveLine Y))
    (q.eP.underlying.inv.app (Mod.regular _) ≫
      (sheafCompose (Scheme.ProEt.topology (ProjectiveLine Y))
        (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})).map q.eP.unitIso.hom)
    (supported_endpoint_underlying (q.route.first.units (ProjectiveLine Y))
      q.route.first.supported)
    (supported_endpoint_underlying (q.route.second.units (ProjectiveLine Y))
      q.route.second.supported)
    (finite_source_transpose_underlying q.eP q.eW q.sourceComparison)

private theorem cyclic_underlying :
    q.cyclicOrdinary.hom ≫
        (inverseUnderlying q.cyclic.eW
          ((lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} l n))
            (diagonalImmersion Y)).obj
              (geoCartierConstant (diagonalResidue.{u} l n) (ProjectiveLine Y)))).hom =
      (lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
        (coefficientMap (cyclicMap l n) (ProjectiveLine Y) ≫
          q.cyclic.eP.underlying.inv.app (Mod.regular _) ≫
          (sheafCompose (Scheme.ProEt.topology (ProjectiveLine Y))
            (forget₂ (ModuleCat.{u + 1} (diagonalResidue.{u} l n)) Ab.{u + 1})).map
              q.cyclic.eP.unitIso.hom) := by
  unfold cyclicOrdinary
  exact one_map_normalized
    (X := condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) (ProjectiveLine Y))
    (Y := condensedRingObj (Profinite.continuousMapRingObj.{u}
      (ZMod (l ^ (n + 1)))) (ProjectiveLine Y))
    (Z := (sheafCompose (Scheme.ProEt.topology (ProjectiveLine Y))
      (forget₂ (ModuleCat.{u + 1} (diagonalResidue.{u} l n)) Ab.{u + 1})).obj
        (geoCartierConstant (diagonalResidue.{u} l n) (ProjectiveLine Y)))
    (lowerStar Ab.{u + 1} (diagonalImmersion Y))
    q.cyclic.supported.semilinear.hom.hom
    (q.cyclic.eW.F.asEquivalence.toAdjunction.homEquiv _ _
      q.cyclic.sourceComparison.iso.hom).hom
    (inverseUnderlying q.cyclic.eW
      ((lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} l n))
        (diagonalImmersion Y)).obj
          (geoCartierConstant (diagonalResidue.{u} l n) (ProjectiveLine Y)))).hom
    (coefficientMap (cyclicMap l n) (ProjectiveLine Y))
    (q.cyclic.eP.underlying.inv.app (Mod.regular _) ≫
      (sheafCompose (Scheme.ProEt.topology (ProjectiveLine Y))
        (forget₂ (ModuleCat.{u + 1} (diagonalResidue.{u} l n)) Ab.{u + 1})).map
          q.cyclic.eP.unitIso.hom)
    (supported_endpoint_underlying (q.cyclic.units (ProjectiveLine Y)) q.cyclic.supported)
    (finite_source_transpose_underlying q.cyclic.eP q.cyclic.eW q.cyclic.sourceComparison)

/-- Normalized finite realizations give the ordinary supported source square.
Source: coefficient changes (1). (blueprint: lem-diagonal-ordinary-source-normalization).
Proof: forget module structure and cancel the inverse realization counit. The supplied
normalizations reduce the maps to diagonal pushforwards of coefficient-unit maps.
The unit and multiplication by the killing power jointly cover the pulled-back
l-adic ring, so the two unital maps agree. The source map is its constant-generator
map by sheafification uniqueness. -/
theorem ordinary_source_eq
    (s : q.quotientRight ≅ q.restriction ⋙ q.cyclicRight)
    (hs : q.RestrictionNormalized s) :
    q.quotientOrdinary ≫ s.hom.app _ = q.cyclicOrdinary ≫ q.cyclicRight.map q.sourceMap := by
  refine Mod.hom_ext _ _ ?_
  simp only [Mod.comp_hom']
  let P := (lowerStar (ModuleCat.{u + 1} A) (diagonalImmersion Y)).obj
    (geoCartierConstant A (ProjectiveLine Y))
  let B := (lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} l n))
    (diagonalImmersion Y)).obj (geoCartierConstant (diagonalResidue.{u} l n) (ProjectiveLine Y))
  refine normalized_ordinary_square q.quotientOrdinary.hom q.cyclicOrdinary.hom
    (s.hom.app P).hom (q.cyclicRight.map q.sourceMap).hom
    (inverseUnderlying q.eW P) (inverseUnderlying q.cyclic.eW B)
    (inverseUnderlying q.cyclic.eW (q.restriction.obj P))
    ((sheafCompose (Scheme.ProEt.topology (diagonalSurface Y))
      (forget₂ (ModuleCat.{u + 1} (diagonalResidue.{u} l n)) Ab.{u + 1})).map q.sourceMap)
    _ _ (hs P) (inverse_underlying_naturality q.cyclic.eW q.sourceMap)
    q.quotient_underlying q.cyclic_underlying ?_
  have hm :
      (sheafCompose (Scheme.ProEt.topology (diagonalSurface Y))
        (forget₂ (ModuleCat.{u + 1} (diagonalResidue.{u} l n)) Ab.{u + 1})).map q.sourceMap =
      (lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
        ((sheafCompose (Scheme.ProEt.topology (ProjectiveLine Y))
          (forget₂ (ModuleCat.{u + 1} (diagonalResidue.{u} l n)) Ab.{u + 1})).map
            q.maps.source) := rfl
  have h := mapped_coefficient_square (lowerStar Ab.{u + 1} (diagonalImmersion Y))
    (coefficientMap (integralMap l E) (ProjectiveLine Y))
    (coefficientMap (quotientMap l E π n) (ProjectiveLine Y))
    (coefficientMap (cyclicMap l n) (ProjectiveLine Y))
    (q.eP.underlying.inv.app (Mod.regular _))
    ((sheafCompose (Scheme.ProEt.topology (ProjectiveLine Y))
      (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})).map q.eP.unitIso.hom)
    (q.cyclic.eP.underlying.inv.app (Mod.regular _))
    ((sheafCompose (Scheme.ProEt.topology (ProjectiveLine Y))
      (forget₂ (ModuleCat.{u + 1} (diagonalResidue.{u} l n)) Ab.{u + 1})).map
        q.cyclic.eP.unitIso.hom)
    ((sheafCompose (Scheme.ProEt.topology (ProjectiveLine Y))
      (forget₂ (ModuleCat.{u + 1} (diagonalResidue.{u} l n)) Ab.{u + 1})).map q.maps.source)
    q.ordinary_coefficient_eq
  exact h.trans (congrArg (fun k ↦
    (lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
      (coefficientMap (cyclicMap l n) (ProjectiveLine Y) ≫
        q.cyclic.eP.underlying.inv.app (Mod.regular _) ≫
        (sheafCompose (Scheme.ProEt.topology (ProjectiveLine Y))
          (forget₂ (ModuleCat.{u + 1} (diagonalResidue.{u} l n)) Ab.{u + 1})).map
            q.cyclic.eP.unitIso.hom) ≫ k) hm.symm)

end UniformizerSquareData
end AlgebraicGeometry.ProEtale.DiagonalCoefficients
