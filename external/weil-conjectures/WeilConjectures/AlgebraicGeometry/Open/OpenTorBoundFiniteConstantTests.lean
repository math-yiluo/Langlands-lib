/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Algebra.Homology.DerivedCategory.Plus

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import WeilConjectures.CategoryTheory.Finite.FiniteCDDerivedUpperBound
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheaf
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-!
# Finite constant-module Tor tests for an open direct image
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Fully faithful precomposition gives the universal property of a factorization. -/
private theorem kan_of_full_whiskering
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (L : C ⥤ D) (G : D ⥤ E)
    [((Functor.whiskeringLeft C D E).obj L).Full]
    [((Functor.whiskeringLeft C D E).obj L).Faithful]
    {F : C ⥤ E} (e : F ≅ L ⋙ G) : G.IsLeftKanExtension e.hom := by
  let W := (Functor.whiskeringLeft C D E).obj L
  refine ⟨⟨IsInitial.ofUniqueHom
    (fun Y ↦ StructuredArrow.homMk (W.preimage (e.inv ≫ Y.hom)) ?_) ?_⟩⟩
  · change e.hom ≫ W.map (W.preimage (e.inv ≫ Y.hom)) = Y.hom
    rw [W.map_preimage]
    simp
  · intro Y m
    apply StructuredArrow.hom_ext
    apply W.map_injective
    change W.map m.right = W.map (W.preimage (e.inv ≫ Y.hom))
    rw [W.map_preimage]
    have h := m.w
    change e.hom ≫ W.map m.right = Y.hom at h
    rw [← h]
    simp

set_option backward.isDefEq.respectTransparency false in
private theorem upper_bound_rightDerived
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (e : ℤ) (he : 0 ≤ e)
    (hF : ∀ (q : ℤ) (X : C), e < q → IsZero
      ((_root_.DerivedCategory.homologyFunctor D q).obj
        (F.rightDerivedFunctor.obj ((_root_.DerivedCategory.singleFunctor C 0).obj X))))
    (b : ℤ) (E : _root_.DerivedCategory C)
    (hE : ∀ q, b < q → IsZero ((_root_.DerivedCategory.homologyFunctor C q).obj E)) :
    ∀ q, b + e < q → IsZero ((_root_.DerivedCategory.homologyFunctor D q).obj
      (F.rightDerivedFunctor.obj E)) := by
  have hclassical (q : ℕ) (hq : e < (q : ℤ)) (X : C) :
      IsZero ((F.rightDerived q).obj X) :=
    (hF q X hq).of_iso (F.homologyRightDerivedFunctorObjSingleFunctorIso X q).symm
  obtain ⟨RF, α, hRF, hbound⟩ := finiteCDDerivedUpperBound F e he hclassical
  let π := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let G := F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ _root_.DerivedCategory.Qh
  let eG : π ⋙ G ≅ F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      _root_.DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ))
        _root_.DerivedCategory.Qh ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (_root_.DerivedCategory.quotientCompQhIso D)
  let β := eG.inv ≫ Functor.whiskerLeft π F.rightDerivedFunctorUnit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (_root_.DerivedCategory.quotientCompQhIso C).hom
      F.rightDerivedFunctor
  have : G.IsLeftKanExtension eG.inv := kan_of_full_whiskering π G eG.symm
  have : F.rightDerivedFunctor.IsLeftKanExtension F.rightDerivedFunctorUnit :=
    Functor.IsRightDerivedFunctor.isLeftKanExtension _ _
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
  have : F.rightDerivedFunctor.IsRightDerivedFunctor β
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) := by
    constructor
    exact (Functor.isLeftKanExtension_iff_postcompose eG.inv
      _root_.DerivedCategory.Q (_root_.DerivedCategory.quotientCompQhIso C)
      F.rightDerivedFunctorUnit β (by rfl)).mp inferInstance
  have := hRF
  let i := Functor.rightDerivedUnique RF F.rightDerivedFunctor α β
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
  intro q hq
  exact (hbound b E hE q hq).of_iso
    ((_root_.DerivedCategory.homologyFunctor D q).mapIso (i.app E).symm)

set_option backward.isDefEq.respectTransparency false in
private theorem lower_bound_rightDerived
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive]
    (a : ℤ) (E : _root_.DerivedCategory C)
    (hE : ∀ q, q < a → IsZero ((_root_.DerivedCategory.homologyFunctor C q).obj E)) :
    ∀ q, q < a → IsZero ((_root_.DerivedCategory.homologyFunctor D q).obj
      (F.rightDerivedFunctor.obj E)) := by
  have hge : E.IsGE a := (_root_.DerivedCategory.isGE_iff E a).mpr hE
  let Eplus : _root_.DerivedCategory.Plus C := ⟨E, ⟨a, hge⟩⟩
  have : Eplus.IsGE a :=
    (_root_.DerivedCategory.Plus.isGE_ι_obj_iff Eplus a).mp hge
  obtain ⟨I, hI, ⟨i⟩⟩ :=
    _root_.DerivedCategory.Plus.exists_injective_nonempty_iso Eplus a
  let J : CochainComplex C ℤ := ((InjectiveObject.ι C).mapHomologicalComplex (.up ℤ)).obj I.obj
  have : J.IsStrictlyGE a := inferInstance
  have : J.IsKInjective := inferInstance
  let iJ : _root_.DerivedCategory.Q.obj J ≅ E :=
    _root_.DerivedCategory.Plus.ι.mapIso i
  intro q hq
  let K : CochainComplex D ℤ := (F.mapHomologicalComplex (.up ℤ)).obj J
  have hz := (K.exactAt_of_isGE a q hq).isZero_homology
  exact hz.of_iso
    (((_root_.DerivedCategory.homologyFunctor D q).mapIso
      (F.rightDerivedFunctor.mapIso iJ.symm ≪≫ F.rightDerivedFunctorObjQIso J)) ≪≫
      (_root_.DerivedCategory.homologyFunctorFactors D q).app _)

/-- The finite constant-module tensor tests of `Rj_*L` vanish outside `[a,b+e]`. -/
theorem open_tor_bound_finite_constant_tests
    (p : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] [CharP k p]
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ p)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (_hA : ∃ n : ℕ, ∀ x : A, (l ^ n) • x = 0)
    {V T : Scheme.{u}}
    (aV : V ⟶ Spec (.of k)) (aT : T ⟶ Spec (.of k))
    [LocallyOfFiniteType aV] [QuasiCompact aV]
    [LocallyOfFiniteType aT] [QuasiCompact aT]
    (j : V ⟶ T) (_hj : j ≫ aT = aV) [IsOpenImmersion j] [QuasiCompact j]
    (a b e : ℤ) (_hab : a ≤ b) (_he : 0 ≤ e)
    (L : DerivedCategory.Plus (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (_hL : DerivedCategory.hasTorAmplitudeIn A V a b
      (DerivedCategory.Plus.ι.obj L))
    (_hvanish : ∀ (q : ℤ)
      (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)),
      e < q → IsZero
        ((_root_.DerivedCategory.homologyFunctor
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) q).obj
          ((rightDerivedLowerStar (ModuleCat.{u + 1} A) j).obj
            ((_root_.DerivedCategory.singleFunctor
              (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj F))))
    (_hproj : ∀ (M : ModuleCat.{u + 1} A), Finite M → IsIso
      (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) j).app
        (DerivedCategory.Plus.ι.obj L)).app
        ((_root_.DerivedCategory.singleFunctor
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj
          ((constantSheaf T.smallEtaleTopology
            (ModuleCat.{u + 1} A)).obj M)))) :
    ∀ (M : ModuleCat.{u + 1} A), Finite M → ∀ (q : ℤ),
      q < a ∨ b + e < q → IsZero
        ((_root_.DerivedCategory.homologyFunctor
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) q).obj
          (((derivedTensor (ModuleCat.{u + 1} A) T).obj
            ((rightDerivedLowerStar (ModuleCat.{u + 1} A) j).obj
              (DerivedCategory.Plus.ι.obj L))).obj
            ((_root_.DerivedCategory.singleFunctor
              (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj
              ((constantSheaf T.smallEtaleTopology
                (ModuleCat.{u + 1} A)).obj M)))) := by
  intro M hM q hq
  let MV := (constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M
  let MT := (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M
  let E := ((derivedTensor (ModuleCat.{u + 1} A) V).obj
    (DerivedCategory.Plus.ι.obj L)).obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj MV)
  let F := lowerStar (ModuleCat.{u + 1} A) j
  have hE (r : ℤ) (hr : r < a ∨ b < r) :
      IsZero ((_root_.DerivedCategory.homologyFunctor _ r).obj E) := _hL MV r hr
  have hz : IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
      (F.rightDerivedFunctor.obj E)) := by
    rcases hq with hq | hq
    · exact lower_bound_rightDerived F a E (fun r hr ↦ hE r (Or.inl hr)) q hq
    · exact upper_bound_rightDerived F e _he _hvanish b E
        (fun r hr ↦ hE r (Or.inr hr)) q hq
  let c : (upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor.obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj MT) ≅
        (_root_.DerivedCategory.singleFunctor _ 0).obj MV :=
    (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) j).app MT ≪≫
      (_root_.DerivedCategory.singleFunctor _ 0).mapIso
        ((constantSheafCompUpperStarIso (Λ := A) j).app M)
  have := _hproj M hM
  let i := asIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) j).app
    (DerivedCategory.Plus.ι.obj L)).app
      ((_root_.DerivedCategory.singleFunctor _ 0).obj MT))
  exact hz.of_iso ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
    (i ≪≫ F.rightDerivedFunctor.mapIso
      (((derivedTensor (ModuleCat.{u + 1} A) V).obj
        (DerivedCategory.Plus.ι.obj L)).mapIso c)))

end AlgebraicGeometry.Etale
