/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorComparisonDescent
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
import WeilConjectures.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat

/-! # Unit comparison for derived pullback

Source: Stacks Project, Cohomology, Tag 079U, lemma-pullback-tensor-product,
and section-derived-pullback; the parent descent proof, step 3.
(blueprint: lem-pc-derived-pullback-tensor-unit-counit).
-/

@[expose] public section

universe uModel wModel

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

attribute [local instance]
  tensorDescentPullbackDescentModuleTensor
  tensorDescentModuleSymmetric
  tensorDescentModulePreadditive
  tensorDescentModuleClosed
  tensorDescentModuleGrothendieck
  tensorDescentModuleResolutions
  tensorDescentModuleDerivedMonoidal
  tensorDescentPullbackDescentQLax

/-- The supplied left-derived counit is invertible at the tensor-unit complex.
Source: Stacks Project, Cohomology, Tag 06YJ, lemma-derived-pullback,
and Tag 079U; parent unit proof, step 1.
(blueprint: lem-pc-derived-pullback-tensor-unit-counit).
Proof: the unit complex is the structure sheaf in degree zero. Tensoring with the
structure sheaf is the identity, so it is flat; its single complex is K-flat.
The recorded derived pullback is computed on K-flat complexes. The equalities hF
and hmap identify the supplied F with the recorded tensor pullback as a functor.
Whisker this identification with the homotopy quotient and localization. Uniqueness
of the left-derived counit identifies the supplied counit with the recorded one,
up to the invertible comparison of left-derived functors. Its component at this
K-flat complex is thus invertible. This includes the zero-ring and empty-scheme cases. -/
theorem derivedPullback_tensor_unit_counit_isIso {T X : Scheme.{uModel}} (g : T ⟶ X)
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings T.toRingedSpace))]
    (F : SheafOfModules.{uModel} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{uModel} (moduleRings T.toRingedSpace))
    (hF : ∀ M, F.obj M = Scheme.Modules.tensorPullbackObj g M)
    (hmap : ∀ {M N} (a : M ⟶ N),
      F.map a = eqToHom (hF M) ≫ Scheme.Modules.tensorPullbackMap g a ≫
        eqToHom (hF N).symm)
    [F.Additive]
    (ε : DerivedCategory.Qh ⋙ derivedPullback g ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hε : (derivedPullback g).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso
        (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)))
    : IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (𝟙_ (CochainComplex
          (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ)))) := by
  have hFE : F = Scheme.Modules.tensorPullback g :=
    CategoryTheory.Functor.ext hF (fun _ _ a ↦ hmap a)
  subst F
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
      F₀, hF₀, hmap₀, hF₀add, ε₀, hderived₀, htri, hε₀⟩ :=
    (derivedPullback_spec g)
  have hF₀E : F₀ = Scheme.Modules.tensorPullback g :=
    CategoryTheory.Functor.ext hF₀ (fun _ _ a ↦ hmap₀ a)
  subst F₀
  let A := SheafOfModules.{uModel} (moduleRings X.toRingedSpace)
  let U : CochainComplex A ℤ := 𝟙_ _
  have hflat : SheafOfModules.IsFlat (𝟙_ A) := by
    change exactFunctor A A (tensorRight (𝟙_ A))
    exact (exactFunctor A A).prop_of_iso (rightUnitorNatIso A).symm
      (by rw [exactFunctor_iff]; exact ⟨inferInstance, inferInstance⟩)
  have hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i → CategoryTheory.Limits.IsZero (U.X i) := by
    refine ⟨0, fun i hi ↦ ?_⟩
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  have hterms : ∀ i : ℤ, SheafOfModules.IsFlat (U.X i) := by
    intro i
    by_cases hi : i = 0
    · subst i
      let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ A)
      exact (exactFunctor _ _).prop_of_iso
        ((curriedTensor A).flip.mapIso e.symm) hflat
    · exact (ObjectProperty.flat_of_isZero
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)).2
  have hU := CochainComplex.isKFlat_of_boundedAbove_flat_ringedSpace
    X.toRingedSpace U hbounded hterms
  have := hε₀ U hU
  let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  have : (derivedPullback g).IsLeftDerivedFunctor ε W := hε
  have : (derivedPullback g).IsLeftDerivedFunctor ε₀ W := hderived₀
  let e := Functor.leftDerivedUnique (derivedPullback g) (derivedPullback g) ε ε₀ W
  have he : e.hom.app (DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj U)) ≫
      ε₀.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj U) =
      ε.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj U) := by
    simp [e, Functor.leftDerivedNatIso]
  rw [← he]
  infer_instance

/-- Termwise pullback of the unit complex, using the specified underived monoidal unit.
Source: Stacks Project, Tag 079U, parent unit proof, step 1.
(blueprint: lem-pc-derived-pullback-tensor-unit-counit). -/
noncomputable def tensorPullback_unitHomotopyIso {T X : Scheme.{uModel}}
    (F : SheafOfModules.{uModel} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{uModel} (moduleRings T.toRingedSpace)) [F.Additive]
    (mF : F.CoreMonoidal) :
    𝟙_ (HomotopyCategory
      (SheafOfModules.{uModel} (moduleRings T.toRingedSpace)) (ComplexShape.up ℤ)) ≅
      (F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        (𝟙_ (HomotopyCategory
          (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ))) :=
  (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso mF.εIso ≪≫
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app _).symm) ≪≫
    ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app _).symm

/-- Explicit derived unit comparison, obtained by inverting the counit at the unit.
Source: Stacks Project, Tags 06YJ and 079U, parent unit proof, step 1.
(blueprint: lem-pc-derived-pullback-tensor-unit-counit).
All data are the supplied unit maps and counit; no arbitrary existence witness is chosen. -/
noncomputable def derivedPullback_tensorUnitIso {T X : Scheme.{uModel}} (g : T ⟶ X)
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings T.toRingedSpace))]
    (F : SheafOfModules.{uModel} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{uModel} (moduleRings T.toRingedSpace)) [F.Additive]
    (mF : F.CoreMonoidal)
    (ε : DerivedCategory.Qh ⋙ derivedPullback g ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [IsIso (ε.app (𝟙_ (HomotopyCategory
      (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ))))] :
    𝟙_ (schemeDerivedCategory T) ≅ (derivedPullback g).obj (𝟙_ (schemeDerivedCategory X)) := by
  let AX := SheafOfModules.{uModel} (moduleRings X.toRingedSpace)
  let AT := SheafOfModules.{uModel} (moduleRings T.toRingedSpace)
  let QX := DerivedCategory.Qh (C := AX)
  let QT := DerivedCategory.Qh (C := AT)
  have hX : IsIso (Functor.LaxMonoidal.ε QX) := DerivedCategory.isIso_ε_Qh AX
  have hT : IsIso (Functor.LaxMonoidal.ε QT) := DerivedCategory.isIso_ε_Qh AT
  let eX : 𝟙_ (schemeDerivedCategory X) ≅ QX.obj (𝟙_ _) :=
    asIso (Functor.LaxMonoidal.ε QX)
  let eT : 𝟙_ (schemeDerivedCategory T) ≅ QT.obj (𝟙_ _) :=
    asIso (Functor.LaxMonoidal.ε QT)
  let eF := QT.mapIso (tensorPullback_unitHomotopyIso F mF)
  let eε := asIso (ε.app (𝟙_ (HomotopyCategory AX (ComplexShape.up ℤ))))
  exact eT ≪≫ eF ≪≫ eε.symm ≪≫ (derivedPullback g).mapIso eX.symm

end AlgebraicGeometry
