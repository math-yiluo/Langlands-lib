/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-! # Scalar restriction and normalized slice extension

Source: Stacks Project, Modules on Sites, Tags 03DI, 03CY and 03DJ
(blueprint: lem-cbc-ringed-open-scalar-adjunction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe c v r w t h
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules
namespace RingedOpenScalar

/-- The two unit and counit equations, with the restriction comparison displayed.
Source: Stacks 03DI (blueprint: lem-cbc-ringed-open-scalar-adjunction). -/
def Equations {A B C D : Type t} [Category.{h} A] [Category.{h} B]
    [Category.{h} C] [Category.{h} D]
    {JS : A ⥤ C} {JR : B ⥤ D} {rU : A ⥤ B} {rT : C ⥤ D}
    {qS : C ⥤ A} {qR : D ⥤ B}
    (e : JS ⋙ rT ≅ rU ⋙ JR) (d : rT ⋙ qR ≅ qS ⋙ rU)
    (adjS : JS ⊣ qS) (adjR : JR ⊣ qR) : Prop :=
  (∀ N : A, rU.map (adjS.unit.app N) ≫ d.inv.app (JS.obj N) ≫
    qR.map (e.hom.app N) = adjR.unit.app (rU.obj N)) ∧
  (∀ Q : C, e.hom.app (qS.obj Q) ≫ JR.map (d.inv.app Q) ≫
    adjR.counit.app (rT.obj Q) = rT.map (adjS.counit.app Q))
/-- The canonical exact-derived square, retaining the standard composition factors.
Source: Stacks 015F (blueprint: lem-cbc-ringed-open-scalar-adjunction). -/
def derivedSquare {A B C D : Type t} [Category.{h} A] [Category.{h} B]
    [Category.{h} C] [Category.{h} D] [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (K : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [K.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K] (e : F ⋙ G ≅ H ⋙ K) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
      H.mapDerivedCategory ⋙ K.mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso F G ≪≫
    Functor.mapDerivedCategoryNatIso e ≪≫ (Functor.mapDerivedCategoryCompIso H K).symm

/-- All termwise and localized forms of the two equations for the same square.
The tower index 0 denotes the original index 1.
Source: Stacks 03DI, 03DJ, 015F
(blueprint: lem-cbc-ringed-open-scalar-adjunction). -/
def Transport {A B C D : Type t} [Category.{h} A] [Category.{h} B]
    [Category.{h} C] [Category.{h} D] [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ C)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ D)]
    {JS : A ⥤ C} {JR : B ⥤ D} {rU : A ⥤ B} {rT : C ⥤ D}
    {qS : C ⥤ A} {qR : D ⥤ B}
    [JS.Additive] [JR.Additive] [rU.Additive] [rT.Additive] [qS.Additive] [qR.Additive]
    [PreservesFiniteLimits JS] [PreservesFiniteColimits JS]
    [PreservesFiniteLimits JR] [PreservesFiniteColimits JR]
    [PreservesFiniteLimits rU] [PreservesFiniteColimits rU]
    [PreservesFiniteLimits rT] [PreservesFiniteColimits rT]
    [PreservesFiniteLimits qS] [PreservesFiniteColimits qS]
    [PreservesFiniteLimits qR] [PreservesFiniteColimits qR]
    (e : JS ⋙ rT ≅ rU ⋙ JR) (d : rT ⋙ qR ≅ qS ⋙ rU)
    (adjS : JS ⊣ qS) (adjR : JR ⊣ qR) : Prop := by
  letI : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ A C).obj JS) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ A C).obj JS) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ B D).obj JR) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ B D).obj JR) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ A B).obj rU) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ A B).obj rU) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj rT) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj rT) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ C A).obj qS) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ C A).obj qS) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ D B).obj qR) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ D B).obj qR) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  exact
    Equations e d adjS adjR ∧
    Equations
      (JS := JS.mapHomologicalComplex (.up ℤ))
      (JR := JR.mapHomologicalComplex (.up ℤ))
      (rU := rU.mapHomologicalComplex (.up ℤ))
      (rT := rT.mapHomologicalComplex (.up ℤ))
      (qS := qS.mapHomologicalComplex (.up ℤ))
      (qR := qR.mapHomologicalComplex (.up ℤ))
      (NatIso.mapHomologicalComplex e (.up ℤ))
      (NatIso.mapHomologicalComplex d (.up ℤ))
      (adjS.mapHomologicalComplex (.up ℤ)) (adjR.mapHomologicalComplex (.up ℤ)) ∧
    Equations (derivedSquare JS rT rU JR e) (derivedSquare rT qR qS rU d)
      (OpenTensorNormalization.exactDerivedAdjunction adjS)
      (OpenTensorNormalization.exactDerivedAdjunction adjR) ∧
    Equations
      (JS := (Functor.whiskeringRight ℕᵒᵖ A C).obj JS)
      (JR := (Functor.whiskeringRight ℕᵒᵖ B D).obj JR)
      (rU := (Functor.whiskeringRight ℕᵒᵖ A B).obj rU)
      (rT := (Functor.whiskeringRight ℕᵒᵖ C D).obj rT)
      (qS := (Functor.whiskeringRight ℕᵒᵖ C A).obj qS)
      (qR := (Functor.whiskeringRight ℕᵒᵖ D B).obj qR)
      ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso e)
      ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso d)
      (adjS.whiskerRight ℕᵒᵖ) (adjR.whiskerRight ℕᵒᵖ) ∧
    Equations
      (JS := ((Functor.whiskeringRight ℕᵒᵖ A C).obj JS).mapHomologicalComplex (.up ℤ))
      (JR := ((Functor.whiskeringRight ℕᵒᵖ B D).obj JR).mapHomologicalComplex (.up ℤ))
      (rU := ((Functor.whiskeringRight ℕᵒᵖ A B).obj rU).mapHomologicalComplex (.up ℤ))
      (rT := ((Functor.whiskeringRight ℕᵒᵖ C D).obj rT).mapHomologicalComplex (.up ℤ))
      (qS := ((Functor.whiskeringRight ℕᵒᵖ C A).obj qS).mapHomologicalComplex (.up ℤ))
      (qR := ((Functor.whiskeringRight ℕᵒᵖ D B).obj qR).mapHomologicalComplex (.up ℤ))
      (NatIso.mapHomologicalComplex ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso e) (.up ℤ))
      (NatIso.mapHomologicalComplex ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso d) (.up ℤ))
      ((adjS.whiskerRight ℕᵒᵖ).mapHomologicalComplex (.up ℤ))
      ((adjR.whiskerRight ℕᵒᵖ).mapHomologicalComplex (.up ℤ)) ∧
    Equations
      (derivedSquare ((Functor.whiskeringRight ℕᵒᵖ _ _).obj JS)
        ((Functor.whiskeringRight ℕᵒᵖ _ _).obj rT)
        ((Functor.whiskeringRight ℕᵒᵖ _ _).obj rU) ((Functor.whiskeringRight ℕᵒᵖ _ _).obj JR)
        ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso e))
      (derivedSquare ((Functor.whiskeringRight ℕᵒᵖ _ _).obj rT)
        ((Functor.whiskeringRight ℕᵒᵖ _ _).obj qR)
        ((Functor.whiskeringRight ℕᵒᵖ _ _).obj qS) ((Functor.whiskeringRight ℕᵒᵖ _ _).obj rU)
        ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso d))
      (OpenTensorNormalization.exactDerivedAdjunction (adjS.whiskerRight ℕᵒᵖ))
      (OpenTensorNormalization.exactDerivedAdjunction (adjR.whiskerRight ℕᵒᵖ))


section EquationCalculus

variable {A B C D : Type t} [Category.{h} A] [Category.{h} B]
  [Category.{h} C] [Category.{h} D]
  {JS : A ⥤ C} {JR : B ⥤ D} {rU : A ⥤ B} {rT : C ⥤ D}
  {qS : C ⥤ A} {qR : D ⥤ B}
  (e : JS ⋙ rT ≅ rU ⋙ JR) (d : rT ⋙ qR ≅ qS ⋙ rU)
  (adjS : JS ⊣ qS) (adjR : JR ⊣ qR)

private theorem inverseMate_of_unit
    (hu : ∀ N : A, rU.map (adjS.unit.app N) ≫ d.inv.app (JS.obj N) ≫
      qR.map (e.hom.app N) = adjR.unit.app (rU.obj N)) :
    ((mateEquiv adjS adjR).symm (TwoSquare.mk _ _ _ _ d.inv)) = e.inv := by
  ext N
  apply (adjR.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change adjR.unit.app (rU.obj N) ≫ qR.map
      (((mateEquiv adjS adjR).symm (TwoSquare.mk _ _ _ _ d.inv)).app N) = _
  have h := unit_mateEquiv_symm adjS adjR (TwoSquare.mk _ _ _ _ d.inv) N
  change rU.map (adjS.unit.app N) ≫ d.inv.app (JS.obj N) =
    adjR.unit.app (rU.obj N) ≫ qR.map
      (((mateEquiv adjS adjR).symm (TwoSquare.mk _ _ _ _ d.inv)).app N) at h
  rw [← h, ← hu N]
  simp only [Category.assoc]
  rw [← qR.map_comp, Iso.hom_inv_id_app]
  erw [qR.map_id]
  erw [Category.comp_id]

private theorem equations_of_inverseMate
    (hm : ((mateEquiv adjS adjR).symm (TwoSquare.mk _ _ _ _ d.inv)) = e.inv) :
    Equations e d adjS adjR := by
  have hu (N : A) := unit_mateEquiv_symm adjS adjR (TwoSquare.mk _ _ _ _ d.inv) N
  have hc (Q : C) := mateEquiv_counit_symm adjS adjR (TwoSquare.mk _ _ _ _ d.inv) Q
  change (∀ N, _) ∧ (∀ Q, _)
  constructor
  · intro N
    have hu' := hu N
    change rU.map (adjS.unit.app N) ≫ d.inv.app (JS.obj N) =
      adjR.unit.app (rU.obj N) ≫ qR.map
        (((mateEquiv adjS adjR).symm (TwoSquare.mk _ _ _ _ d.inv)).app N) at hu'
    rw [hm] at hu'
    rw [reassoc_of% hu']
    rw [← qR.map_comp, Iso.inv_hom_id_app]
    erw [qR.map_id]
    rw [Category.comp_id]
  · intro Q
    have hc' := hc Q
    change JR.map (d.inv.app Q) ≫ adjR.counit.app (rT.obj Q) =
      (((mateEquiv adjS adjR).symm (TwoSquare.mk _ _ _ _ d.inv)).app (qS.obj Q)) ≫
        rT.map (adjS.counit.app Q) at hc'
    rw [hm] at hc'
    rw [hc', Iso.hom_inv_id_app_assoc]

variable [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [JS.Additive] [JR.Additive] [rU.Additive] [rT.Additive] [qS.Additive] [qR.Additive]

private theorem equations_complex (he : Equations e d adjS adjR) :
    Equations
      (JS := JS.mapHomologicalComplex (.up ℤ))
      (JR := JR.mapHomologicalComplex (.up ℤ))
      (rU := rU.mapHomologicalComplex (.up ℤ))
      (rT := rT.mapHomologicalComplex (.up ℤ))
      (qS := qS.mapHomologicalComplex (.up ℤ))
      (qR := qR.mapHomologicalComplex (.up ℤ))
      (NatIso.mapHomologicalComplex e (.up ℤ))
      (NatIso.mapHomologicalComplex d (.up ℤ))
      (adjS.mapHomologicalComplex (.up ℤ)) (adjR.mapHomologicalComplex (.up ℤ)) := by
  constructor
  · intro N
    apply HomologicalComplex.Hom.ext
    funext i
    exact he.1 (N.X i)
  · intro Q
    apply HomologicalComplex.Hom.ext
    funext i
    exact he.2 (Q.X i)

omit [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [JS.Additive] [JR.Additive] [rU.Additive] [rT.Additive] [qS.Additive] [qR.Additive] in
private theorem equations_tower (he : Equations e d adjS adjR) :
    Equations
      (JS := (Functor.whiskeringRight ℕᵒᵖ A C).obj JS)
      (JR := (Functor.whiskeringRight ℕᵒᵖ B D).obj JR)
      (rU := (Functor.whiskeringRight ℕᵒᵖ A B).obj rU)
      (rT := (Functor.whiskeringRight ℕᵒᵖ C D).obj rT)
      (qS := (Functor.whiskeringRight ℕᵒᵖ C A).obj qS)
      (qR := (Functor.whiskeringRight ℕᵒᵖ D B).obj qR)
      ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso e)
      ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso d)
      (adjS.whiskerRight ℕᵒᵖ) (adjR.whiskerRight ℕᵒᵖ) := by
  constructor
  · intro N
    ext n
    simpa [Adjunction.whiskerRight] using he.1 (N.obj n)
  · intro Q
    ext n
    simpa [Adjunction.whiskerRight] using he.2 (Q.obj n)

variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
  [PreservesFiniteLimits JS] [PreservesFiniteColimits JS]
  [PreservesFiniteLimits JR] [PreservesFiniteColimits JR]
  [PreservesFiniteLimits rU] [PreservesFiniteColimits rU]
  [PreservesFiniteLimits rT] [PreservesFiniteColimits rT]
  [PreservesFiniteLimits qS] [PreservesFiniteColimits qS]
  [PreservesFiniteLimits qR] [PreservesFiniteColimits qR]

private theorem derivedSquare_symm :
    derivedSquare rU JR JS rT e.symm = (derivedSquare JS rT rU JR e).symm := by
  apply Iso.ext
  simp only [derivedSquare, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    Functor.mapDerivedCategoryNatIso_symm, Iso.symm_inv, Category.assoc]

private theorem equations_derived (he : Equations e d adjS adjR) :
    Equations (derivedSquare JS rT rU JR e) (derivedSquare rT qR qS rU d)
      (OpenTensorNormalization.exactDerivedAdjunction adjS)
      (OpenTensorNormalization.exactDerivedAdjunction adjR) := by
  have hm := inverseMate_of_unit e d adjS adjR he.1
  have : IsIso
      ((mateEquiv adjS adjR).symm (TwoSquare.mk _ _ _ _ d.symm.hom)) := by
    change IsIso ((mateEquiv adjS adjR).symm (TwoSquare.mk _ _ _ _ d.inv))
    rw [hm]
    infer_instance
  have hiso : asIso
      ((mateEquiv adjS adjR).symm (TwoSquare.mk _ _ _ _ d.symm.hom)) = e.symm := by
    apply Iso.ext
    exact hm
  have hd := (exact_localization_inverse_mate adjS adjR d.symm).2.1
  rw [hiso] at hd
  change ((mateEquiv (OpenTensorNormalization.exactDerivedAdjunction adjS)
      (OpenTensorNormalization.exactDerivedAdjunction adjR)).symm
      (TwoSquare.mk _ _ _ _ (derivedSquare qS rU rT qR d.symm).hom)) =
        (derivedSquare rU JR JS rT e.symm).hom at hd
  rw [derivedSquare_symm, derivedSquare_symm] at hd
  exact equations_of_inverseMate _ _ _ _ hd

end EquationCalculus
private theorem transport_of_equations {A B C D : Type t} [Category.{h} A] [Category.{h} B]
    [Category.{h} C] [Category.{h} D] [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ C)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ D)]
    {JS : A ⥤ C} {JR : B ⥤ D} {rU : A ⥤ B} {rT : C ⥤ D}
    {qS : C ⥤ A} {qR : D ⥤ B}
    [JS.Additive] [JR.Additive] [rU.Additive] [rT.Additive] [qS.Additive] [qR.Additive]
    [PreservesFiniteLimits JS] [PreservesFiniteColimits JS]
    [PreservesFiniteLimits JR] [PreservesFiniteColimits JR]
    [PreservesFiniteLimits rU] [PreservesFiniteColimits rU]
    [PreservesFiniteLimits rT] [PreservesFiniteColimits rT]
    [PreservesFiniteLimits qS] [PreservesFiniteColimits qS]
    [PreservesFiniteLimits qR] [PreservesFiniteColimits qR]
    (e : JS ⋙ rT ≅ rU ⋙ JR) (d : rT ⋙ qR ≅ qS ⋙ rU)
    (adjS : JS ⊣ qS) (adjR : JR ⊣ qR)
    (he : Equations e d adjS adjR) : Transport.{w} e d adjS adjR := by
  let : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ A C).obj JS) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  let : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ A C).obj JS) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  let : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ B D).obj JR) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  let : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ B D).obj JR) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  let : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ A B).obj rU) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  let : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ A B).obj rU) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  let : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj rT) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  let : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj rT) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  let : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ C A).obj qS) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  let : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ C A).obj qS) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  let : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ D B).obj qR) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  let : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ D B).obj qR) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  exact ⟨he, equations_complex e d adjS adjR he,
    equations_derived e d adjS adjR he, equations_tower e d adjS adjR he,
    equations_complex _ _ _ _ (equations_tower e d adjS adjR he),
    equations_derived _ _ _ _ (equations_tower e d adjS adjR he)⟩


variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  {R S : Sheaf J CommRingCat.{max c v r}} (U : C) (a : R ⟶ S)

/-- Forget only commutativity of the given ring sheaf.
Source: Stacks 03DA (blueprint: lem-cbc-ringed-open-scalar-adjunction). -/
abbrev rings (R : Sheaf J CommRingCat.{max c v r}) :=
  (sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R

/-- The recorded scalar restriction, on the original site.
Source: Stacks 03DA (blueprint: lem-cbc-ringed-open-scalar-adjunction). -/
abbrev scalars :=
  restrictScalars.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map a)

/-- The same recorded scalar restriction on the localized site.
Source: Stacks 03DI (blueprint: lem-cbc-ringed-open-scalar-adjunction). -/
abbrev sliceScalars : SheafOfModules.{max c v r} ((rings.{c, v, r} S).over U) ⥤
    SheafOfModules.{max c v r} ((rings.{c, v, r} R).over U) :=
  restrictScalars ((J.overPullback RingCat.{max c v r} U).map
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map a))

private theorem restrictScalarsExact {D : Type t} [Category.{h} D]
    {K : GrothendieckTopology D} {B E : Sheaf K RingCat.{r}}
    [HasSheafify K AddCommGrpCat.{r}] [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
    (b : B ⟶ E) : PreservesFiniteLimits (restrictScalars.{r} b) ∧
      PreservesFiniteColimits (restrictScalars.{r} b) := by
  let F := restrictScalars.{r} b
  let : PreservesFiniteColimits (toSheaf.{r} B) :=
    (CategoryTheory.moduleSheaves_colimits_forgetful B).2.2.1
  let : PreservesFiniteColimits (toSheaf.{r} E) :=
    (CategoryTheory.moduleSheaves_colimits_forgetful E).2.2.1
  let : PreservesFiniteLimits (F ⋙ toSheaf.{r} B) :=
    inferInstanceAs (PreservesFiniteLimits (toSheaf.{r} E))
  let : PreservesFiniteColimits (F ⋙ toSheaf.{r} B) :=
    inferInstanceAs (PreservesFiniteColimits (toSheaf.{r} E))
  let : ReflectsFiniteColimits (toSheaf.{r} B) := inferInstance
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves F (toSheaf.{r} B),
    preservesFiniteColimits_of_reflects_of_preserves F (toSheaf.{r} B)⟩

/-- Scalar restriction is exact on either site, without flatness.
Source: Stacks 03CY, 03DI (blueprint: lem-cbc-ringed-open-scalar-adjunction).
Proof: kernels are sectionwise and retain their underlying subgroup under scalar
restriction. Cokernels are abelian sheafifications of sectionwise quotients; their
module actions agree by uniqueness of extending the quotient action. Thus scalar
restriction preserves kernels and cokernels, hence finite limits and colimits.
Its additivity is the sectionwise additivity already in Mathlib. -/
theorem scalarExact :
    PreservesFiniteLimits (scalars.{c, v, r} a) ∧
    PreservesFiniteColimits (scalars.{c, v, r} a) := by
  exact restrictScalarsExact _

set_option linter.unusedSectionVars false in
/-- Scalar exactness on the slice. Source: Stacks 03CY, 03DI
(blueprint: lem-cbc-ringed-open-scalar-adjunction).
Proof: the same sectionwise kernel and sheafified cokernel argument as scalarExact,
applied on the localized site; no flatness is used. -/
theorem sliceExact :
    PreservesFiniteLimits (sliceScalars.{c, v, r} U a) ∧
    PreservesFiniteColimits (sliceScalars.{c, v, r} U a) := by
  let : PreservesFilteredColimitsOfSize.{max c v, max c v}
      (CategoryTheory.forget AddCommGrpCat.{max c v r}) :=
    preservesFilteredColimitsOfSize_shrink.{max c v, max c v r,
      max c v, max c v r} _
  let : HasSheafify (J.over U) AddCommGrpCat.{max c v r} :=
    instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOfSmallOppositeCover.{
      max c v r, max c v r + 1, v, max c v, max c v r} _ _
  exact restrictScalarsExact _

/-- Finite-limit component of scalar exactness. Source: Stacks 03CY, 03DI
(blueprint: lem-cbc-ringed-open-scalar-adjunction). -/
instance scalarLimits : PreservesFiniteLimits (scalars.{c, v, r} a) :=
  (scalarExact.{c, v, r} a).1
/-- Finite-colimit component of scalar exactness. Source: Stacks 03CY, 03DI
(blueprint: lem-cbc-ringed-open-scalar-adjunction). -/
instance scalarColimits : PreservesFiniteColimits (scalars.{c, v, r} a) :=
  (scalarExact.{c, v, r} a).2
/-- Finite-limit component on the slice. Source: Stacks 03CY, 03DI
(blueprint: lem-cbc-ringed-open-scalar-adjunction). -/
instance sliceLimits : PreservesFiniteLimits (sliceScalars.{c, v, r} U a) :=
  (sliceExact.{c, v, r} U a).1
/-- Finite-colimit component on the slice. Source: Stacks 03CY, 03DI
(blueprint: lem-cbc-ringed-open-scalar-adjunction). -/
instance sliceColimits : PreservesFiniteColimits (sliceScalars.{c, v, r} U a) :=
  (sliceExact.{c, v, r} U a).2

/-- The canonical sectionwise identity commuting scalar and slice restriction.
Source: Stacks 03DI (blueprint: lem-cbc-ringed-open-scalar-adjunction). -/
def restrictionIso :
    scalars.{c, v, r} a ⋙ localizedSystemRestriction.{c, v, r} R U ≅
      localizedSystemRestriction.{c, v, r} S U ⋙ sliceScalars.{c, v, r} U a :=
  NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun V ↦ Iso.refl _)))

open Classical in
/-- The sheafification of an actual direct-sum generator.
Source: Stacks 03DI, 03CY (blueprint: lem-cbc-ringed-open-scalar-adjunction). -/
def generator (B : Sheaf J CommRingCat.{max c v r})
    (N : SheafOfModules.{max c v r} ((rings.{c, v, r} B).over U))
    (V : Cᵒᵖ) (phi : V.unop ⟶ U) (x : N.val.obj (op (Over.mk phi))) :
    ((localizedSystemExtension.{c, v, r} B U).obj N).val.obj V :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (rings.{c, v, r} B).obj)).unit.app
    ((extensionByZeroPresheaf.{max c v r} (rings.{c, v, r} B) U).obj N)).app V
      (DirectSum.of (fun psi : V.unop ⟶ U ↦ N.val.obj (op (Over.mk psi))) phi x)

/-- The section normalization of the fixed adjunctions, including their counits.
Source: Stacks 03DI, 03CY (blueprint: lem-cbc-ringed-open-scalar-adjunction).
Proof: transpose the identity under the direct-sum Hom correspondence of 03DI.
The unit includes a section in its structure-arrow summand and sheafifies it.
The counit evaluates every summand by the identity on that section. Uniqueness
of the sheafification extension identifies these with the fixed adjunction. -/
theorem adjunctionGenerators (B : Sheaf J CommRingCat.{max c v r}) :
    (∀ (N : SheafOfModules.{max c v r} ((rings.{c, v, r} B).over U))
      (W : (Over U)ᵒᵖ) (x : N.val.obj W),
      ((localizedSystemAdjunction.{c, v, r} B U).unit.app N).val.app W x =
        generator.{c, v, r} U B N (op W.unop.left) W.unop.hom x) ∧
    (∀ (Q : SheafOfModules.{max c v r} (rings.{c, v, r} B))
      (V : Cᵒᵖ) (phi : V.unop ⟶ U) (x : Q.val.obj V),
      ((localizedSystemAdjunction.{c, v, r} B U).counit.app Q).val.app V
        (generator.{c, v, r} U B
          ((localizedSystemRestriction.{c, v, r} B U).obj Q) V phi x) = x) := by
  have hu := (localizedSystemAdjunction_existsUnique.{c, v, r} B U).exists.choose_spec
  refine ⟨hu, ?_⟩
  intro Q V phi x
  have h := (localizedSystemAdjunction.{c, v, r} B U).right_triangle_components Q
  have hx := congrArg (fun f ↦ f.val.app (op (Over.mk phi)) x) h
  change ((localizedSystemAdjunction.{c, v, r} B U).counit.app Q).val.app V
      (((localizedSystemAdjunction.{c, v, r} B U).unit.app
        ((localizedSystemRestriction.{c, v, r} B U).obj Q)).val.app
          (op (Over.mk phi)) x) = x at hx
  exact (congrArg
    (fun y ↦ ((localizedSystemAdjunction.{c, v, r} B U).counit.app Q).val.app V y)
    (hu ((localizedSystemRestriction.{c, v, r} B U).obj Q)
      (op (Over.mk phi)) x)).symm.trans hx

/-- Sheafification on the slice in the same module universe.
Source: Stacks 03CY (blueprint: lem-cbc-ringed-open-scalar-adjunction). -/
abbrev sliceSheafify : HasSheafify (J.over U) AddCommGrpCat.{max c v r} := by
  let : PreservesFilteredColimitsOfSize.{max c v, max c v}
      (CategoryTheory.forget AddCommGrpCat.{max c v r}) :=
    preservesFilteredColimitsOfSize_shrink.{max c v, max c v r,
      max c v, max c v r} _
  exact instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOfSmallOppositeCover.{
    max c v r, max c v r + 1, v, max c v, max c v r} _ _

/-- Local bijections characterize slice sheafification equivalences.
Source: Stacks 03CY (blueprint: lem-cbc-ringed-open-scalar-adjunction). -/
abbrev sliceLocallyBijective :
    (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r} := inferInstance

/-- Use Mathlib's exact abelian structure with explicit universe arguments.
Source: Stacks 03CY (blueprint: lem-cbc-ringed-open-scalar-adjunction). -/
abbrev ambientAbelian (B : Sheaf J RingCat.{max c v r}) :
    Abelian (SheafOfModules.{max c v r} B) :=
  SheafOfModules.instAbelian.{max c v r, v, max c v r, c} B

/-- Use Mathlib's exact slice abelian structure with explicit universe arguments.
Source: Stacks 03CY (blueprint: lem-cbc-ringed-open-scalar-adjunction). -/
abbrev sliceAbelian (B : Sheaf (J.over U) RingCat.{max c v r}) :
    Abelian (SheafOfModules.{max c v r} B) :=
  @SheafOfModules.instAbelian.{max c v r, v, max c v r, max c v}
    (Over U) _ (J.over U) B (sliceSheafify.{c, v, r} U)
      (sliceLocallyBijective.{c, v, r} U)
/-- The concrete transported equations, with the recorded exactness instances explicit.
Source: Stacks 03DI, 03DJ, 015F
(blueprint: lem-cbc-ringed-open-scalar-adjunction). -/
def transportedEquations
    (e : localizedSystemExtension.{c, v, r} S U ⋙ scalars.{c, v, r} a ≅
      sliceScalars.{c, v, r} U a ⋙ localizedSystemExtension.{c, v, r} R U) : Prop := by
  letI : Abelian (SheafOfModules.{max c v r} (rings.{c, v, r} R)) :=
    ambientAbelian.{c, v, r} (rings.{c, v, r} R)
  letI : Abelian (SheafOfModules.{max c v r} ((rings.{c, v, r} R).over U)) :=
    sliceAbelian.{c, v, r} U ((rings.{c, v, r} R).over U)
  letI : Abelian (SheafOfModules.{max c v r} (rings.{c, v, r} S)) :=
    ambientAbelian.{c, v, r} (rings.{c, v, r} S)
  letI : Abelian (SheafOfModules.{max c v r} ((rings.{c, v, r} S).over U)) :=
    sliceAbelian.{c, v, r} U ((rings.{c, v, r} S).over U)
  letI : Functor.Additive (localizedSystemExtension.{c, v, r} R U) :=
    localizedSystemExtensionAdditive.{c, v, r} R U
  letI : PreservesFiniteLimits (localizedSystemExtension.{c, v, r} R U) :=
    localizedSystemExtensionLimits.{c, v, r} R U
  letI : PreservesFiniteColimits (localizedSystemExtension.{c, v, r} R U) :=
    localizedSystemExtensionColimits.{c, v, r} R U
  letI : Functor.Additive (localizedSystemRestriction.{c, v, r} R U) :=
    localizedSystemRestrictionAdditive.{c, v, r} R U
  letI : PreservesFiniteLimits (localizedSystemRestriction.{c, v, r} R U) :=
    localizedSystemRestrictionLimits.{c, v, r} R U
  letI : PreservesFiniteColimits (localizedSystemRestriction.{c, v, r} R U) :=
    localizedSystemRestrictionColimits.{c, v, r} R U
  letI : Functor.Additive (localizedSystemExtension.{c, v, r} S U) :=
    localizedSystemExtensionAdditive.{c, v, r} S U
  letI : PreservesFiniteLimits (localizedSystemExtension.{c, v, r} S U) :=
    localizedSystemExtensionLimits.{c, v, r} S U
  letI : PreservesFiniteColimits (localizedSystemExtension.{c, v, r} S U) :=
    localizedSystemExtensionColimits.{c, v, r} S U
  letI : Functor.Additive (localizedSystemRestriction.{c, v, r} S U) :=
    localizedSystemRestrictionAdditive.{c, v, r} S U
  letI : PreservesFiniteLimits (localizedSystemRestriction.{c, v, r} S U) :=
    localizedSystemRestrictionLimits.{c, v, r} S U
  letI : PreservesFiniteColimits (localizedSystemRestriction.{c, v, r} S U) :=
    localizedSystemRestrictionColimits.{c, v, r} S U
  letI : PreservesFiniteLimits (scalars.{c, v, r} a) := scalarLimits.{c, v, r} a
  letI : PreservesFiniteColimits (scalars.{c, v, r} a) := scalarColimits.{c, v, r} a
  letI : PreservesFiniteLimits (sliceScalars.{c, v, r} U a) := sliceLimits.{c, v, r} U a
  letI : PreservesFiniteColimits (sliceScalars.{c, v, r} U a) := sliceColimits.{c, v, r} U a
  exact ∀ [HasDerivedCategory.{w, max c v r, (max c v r) + 1}
        (SheafOfModules.{max c v r} (rings.{c, v, r} R))]
    [HasDerivedCategory.{w, max c v r, (max c v r) + 1}
        (SheafOfModules.{max c v r} (rings.{c, v, r} S))]
    [HasDerivedCategory.{w, max c v r, (max c v r) + 1}
    (SheafOfModules.{max c v r} ((rings.{c, v, r} R).over U))]
    [HasDerivedCategory.{w, max c v r, (max c v r) + 1}
    (SheafOfModules.{max c v r} ((rings.{c, v, r} S).over U))]
    [HasDerivedCategory.{w, max c v r, (max c v r) + 1}
        (ℕᵒᵖ ⥤ SheafOfModules.{max c v r} (rings.{c, v, r} R))]
    [HasDerivedCategory.{w, max c v r, (max c v r) + 1}
        (ℕᵒᵖ ⥤ SheafOfModules.{max c v r} (rings.{c, v, r} S))]
    [HasDerivedCategory.{w, max c v r, (max c v r) + 1}
    (ℕᵒᵖ ⥤ SheafOfModules.{max c v r} ((rings.{c, v, r} R).over U))]
    [HasDerivedCategory.{w, max c v r, (max c v r) + 1}
    (ℕᵒᵖ ⥤ SheafOfModules.{max c v r} ((rings.{c, v, r} S).over U))],
    Transport.{w, (max c v r) + 1, max c v r} e (restrictionIso.{c, v, r} U a)
    (localizedSystemAdjunction.{c, v, r} S U)
    (localizedSystemAdjunction.{c, v, r} R U)


@[irreducible] private def presheafComparison :
    extensionByZeroPresheaf.{max c v r} (rings.{c, v, r} S) U ⋙
        PresheafOfModules.restrictScalars
          ((sheafCompose J
            (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map a).hom ≅
      sliceScalars.{c, v, r} U a ⋙
        extensionByZeroPresheaf.{max c v r} (rings.{c, v, r} R) U := by
  let b := ((sheafCompose J
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map a).hom
  let P := extensionByZeroPresheaf.{max c v r} (rings.{c, v, r} S) U ⋙
    PresheafOfModules.restrictScalars b
  let Q := sliceScalars.{c, v, r} U a ⋙
    extensionByZeroPresheaf.{max c v r} (rings.{c, v, r} R) U
  refine NatIso.ofComponents (fun N ↦ PresheafOfModules.isoMk (fun V ↦
    { hom := ModuleCat.ofHom (X := (P.obj N).obj V) (Y := (Q.obj N).obj V)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
      inv := ModuleCat.ofHom (X := (Q.obj N).obj V) (Y := (P.obj N).obj V)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
      hom_inv_id := by ext x; rfl
      inv_hom_id := by ext x; rfl })
    (by intro V W f; ext x; rfl)) ?_
  intro N M f
  ext V x
  rfl

omit [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
private theorem presheafComparison_inv_apply
    (N : SheafOfModules.{max c v r} ((rings.{c, v, r} S).over U))
    (V : Cᵒᵖ) (x : extensionByZeroPresheafSection (rings.{c, v, r} S) U N V) :
    ((presheafComparison.{c, v, r} U a).inv.app N).app V x = x := by
  unfold presheafComparison
  rfl

omit [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
private theorem presheafComparison_hom_apply
    (N : SheafOfModules.{max c v r} ((rings.{c, v, r} S).over U))
    (V : Cᵒᵖ) (x : extensionByZeroPresheafSection (rings.{c, v, r} S) U N V) :
    ((presheafComparison.{c, v, r} U a).hom.app N).app V x = x := by
  unfold presheafComparison
  rfl

@[irreducible] private def sheafComparisonInv
    (N : SheafOfModules.{max c v r} ((rings.{c, v, r} S).over U)) :
    (localizedSystemExtension.{c, v, r} R U).obj
        ((sliceScalars.{c, v, r} U a).obj N) ⟶
      (scalars.{c, v, r} a).obj ((localizedSystemExtension.{c, v, r} S U).obj N) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 (rings.{c, v, r} R).obj)).symm
    ((presheafComparison.{c, v, r} U a).inv.app N ≫
      (PresheafOfModules.restrictScalars
        ((sheafCompose J
          (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map a).hom).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 (rings.{c, v, r} S).obj)).unit.app
          ((extensionByZeroPresheaf.{max c v r} (rings.{c, v, r} S) U).obj N)))

private theorem sheafComparisonInv_underlying
    (N : SheafOfModules.{max c v r} ((rings.{c, v, r} S).over U)) :
    (toSheaf.{max c v r} (rings.{c, v, r} R)).map
        (sheafComparisonInv.{c, v, r} U a N) =
      (presheafToSheaf J AddCommGrpCat.{max c v r}).map
        ((PresheafOfModules.toPresheaf _).map
          ((presheafComparison.{c, v, r} U a).inv.app N)) := by
  rw [sheafComparisonInv, PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
  apply ((CategoryTheory.sheafificationAdjunction J
    AddCommGrpCat.{max c v r}).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  change (PresheafOfModules.toPresheaf _).map
      ((presheafComparison.{c, v, r} U a).inv.app N) ≫
        CategoryTheory.toSheafify J _ = _
  exact CategoryTheory.toSheafify_naturality J _

private theorem sheafComparisonInv_isIso
    (N : SheafOfModules.{max c v r} ((rings.{c, v, r} S).over U)) :
    IsIso (sheafComparisonInv.{c, v, r} U a N) := by
  rw [← isIso_iff_of_reflects_iso _ (toSheaf.{max c v r} (rings.{c, v, r} R)),
    sheafComparisonInv_underlying]
  infer_instance
@[irreducible] private def sheafComparison :
    localizedSystemExtension.{c, v, r} S U ⋙ scalars.{c, v, r} a ≅
      sliceScalars.{c, v, r} U a ⋙ localizedSystemExtension.{c, v, r} R U := by
  have (N : SheafOfModules.{max c v r} ((rings.{c, v, r} S).over U)) :
      IsIso (sheafComparisonInv.{c, v, r} U a N) :=
    sheafComparisonInv_isIso.{c, v, r} U a N
  exact (NatIso.ofComponents (fun N ↦ asIso (sheafComparisonInv.{c, v, r} U a N))
    (by
      intro N M f
      apply (toSheaf.{max c v r} (rings.{c, v, r} R)).map_injective
      simp only [Functor.map_comp, asIso_hom, sheafComparisonInv_underlying]
      let F := presheafToSheaf J AddCommGrpCat.{max c v r}
      let T := PresheafOfModules.toPresheaf.{max c v r} (rings.{c, v, r} R).obj
      change F.map (T.map ((sliceScalars.{c, v, r} U a ⋙
          extensionByZeroPresheaf.{max c v r} (rings.{c, v, r} R) U).map f)) ≫
          F.map (T.map ((presheafComparison.{c, v, r} U a).inv.app M)) =
        F.map (T.map ((presheafComparison.{c, v, r} U a).inv.app N)) ≫
          F.map (T.map ((extensionByZeroPresheaf.{max c v r} (rings.{c, v, r} S) U ⋙
            PresheafOfModules.restrictScalars
              ((sheafCompose J
                (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map a).hom).map f))
      rw [← F.map_comp, ← F.map_comp, ← T.map_comp, ← T.map_comp]
      exact congrArg (fun g ↦ F.map (T.map g))
        ((presheafComparison.{c, v, r} U a).inv.naturality f))).symm

private theorem sheafComparison_inv_app
    (N : SheafOfModules.{max c v r} ((rings.{c, v, r} S).over U)) :
    (sheafComparison.{c, v, r} U a).inv.app N =
      sheafComparisonInv.{c, v, r} U a N := by
  unfold sheafComparison
  rfl

private theorem sheafComparisonInv_generator
    (N : SheafOfModules.{max c v r} ((rings.{c, v, r} S).over U))
    (V : Cᵒᵖ) (phi : V.unop ⟶ U) (x : N.val.obj (op (Over.mk phi))) :
    (sheafComparisonInv.{c, v, r} U a N).val.app V
        (generator.{c, v, r} U R ((sliceScalars.{c, v, r} U a).obj N) V phi x) =
      generator.{c, v, r} U S N V phi x := by
  classical
  have h : PresheafOfModules.sheafificationHomEquiv (𝟙 (rings.{c, v, r} R).obj)
      (sheafComparisonInv.{c, v, r} U a N) =
        (presheafComparison.{c, v, r} U a).inv.app N ≫
          (PresheafOfModules.restrictScalars
            ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map a).hom).map
            ((PresheafOfModules.sheafificationAdjunction
              (𝟙 (rings.{c, v, r} S).obj)).unit.app
                ((extensionByZeroPresheaf.{max c v r} (rings.{c, v, r} S) U).obj N)) := by
    rw [sheafComparisonInv, Equiv.apply_symm_apply]
  have hv := congrArg (fun f ↦ f.app V
    (DirectSum.of (fun psi : V.unop ⟶ U ↦ N.val.obj (op (Over.mk psi))) phi x)) h
  change (sheafComparisonInv.{c, v, r} U a N).val.app V
      (generator.{c, v, r} U R ((sliceScalars.{c, v, r} U a).obj N) V phi x) =
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (rings.{c, v, r} S).obj)).unit.app
        ((extensionByZeroPresheaf.{max c v r} (rings.{c, v, r} S) U).obj N)).app V
      (((presheafComparison.{c, v, r} U a).inv.app N).app V
        (DirectSum.of (fun psi : V.unop ⟶ U ↦ N.val.obj (op (Over.mk psi))) phi x)) at hv
  rw [presheafComparison_inv_apply] at hv
  exact hv

private theorem sheafComparison_generator
    (N : SheafOfModules.{max c v r} ((rings.{c, v, r} S).over U))
    (V : Cᵒᵖ) (phi : V.unop ⟶ U) (x : N.val.obj (op (Over.mk phi))) :
    ((sheafComparison.{c, v, r} U a).hom.app N).val.app V
        (generator.{c, v, r} U S N V phi x) =
      generator.{c, v, r} U R ((sliceScalars.{c, v, r} U a).obj N) V phi x := by
  rw [← sheafComparisonInv_generator.{c, v, r} U a N V phi x]
  have h := congrArg (fun f ↦ f.val.app V
    (generator.{c, v, r} U R ((sliceScalars.{c, v, r} U a).obj N) V phi x))
    (Iso.inv_hom_id_app (sheafComparison.{c, v, r} U a) N)
  rw [sheafComparison_inv_app] at h
  exact h

private theorem sheafComparison_equations :
    Equations (sheafComparison.{c, v, r} U a) (restrictionIso.{c, v, r} U a)
      (localizedSystemAdjunction.{c, v, r} S U)
      (localizedSystemAdjunction.{c, v, r} R U) := by
  apply equations_of_inverseMate
  apply inverseMate_of_unit
  intro N
  ext W x
  change ((sheafComparison.{c, v, r} U a).hom.app N).val.app (op W.unop.left)
      (((localizedSystemAdjunction.{c, v, r} S U).unit.app N).val.app W x) =
    ((localizedSystemAdjunction.{c, v, r} R U).unit.app
      ((sliceScalars.{c, v, r} U a).obj N)).val.app W x
  rw [(adjunctionGenerators.{c, v, r} U S).1,
    (adjunctionGenerators.{c, v, r} U R).1]
  exact sheafComparison_generator.{c, v, r} U a N (op W.unop.left) W.unop.hom x

/-- The identity-induced scalar/slice-extension comparison, with the fixed units,
counits, and all its termwise and localized tower identities.
Source: Stacks 03DI, 03CY, 03DJ and 015F
(blueprint: lem-cbc-ringed-open-scalar-adjunction).
Proof: (1) The direct sums, reindexing maps and induced maps on sections coincide;
the scalar action in either presentation is multiplication through a_V.
(2) Extend the inverse presheaf comparison through module sheafification. Its
underlying additive map is the sheafification of the inverse presheaf comparison,
so it is invertible. Naturality follows from that presheaf comparison. The
sheafification Hom equivalence proves the required generator normalization.
(3) The direct-sum Hom correspondence gives the generator formulas for the fixed
unit and counit, as in adjunctionGenerators.
(4) Evaluate the unit equation on a section using the generator normalization.
This unit equation identifies the inverse comparison with the inverse mate of
the restriction square. The counit equation follows from the mate identities.
(5) Restriction, extension and scalar restriction are additive and exact; kernels
are sectionwise and cokernels are sheafified sectionwise quotients.
(6) Apply the functors, isomorphisms and adjunctions levelwise to strict towers,
and degreewise to cochain complexes. Naturality preserves transition and chain
relations, and kernels and cokernels of towers are levelwise.
(7) Exact functors preserve quasi-isomorphisms. The exact-localization inverse-mate
theorem identifies the derived inverse mate with the localized comparison, using
the specified composition identifications and exactDerivedAdjunction. The mate
identities then give the derived unit and counit equations, for modules and
strict towers alike. This uses neither flatness nor bounds. -/
theorem comparison :
    ∃ p : extensionByZeroPresheaf.{max c v r} (rings.{c, v, r} S) U ⋙
        PresheafOfModules.restrictScalars
          ((sheafCompose J
            (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map a).hom ≅
      sliceScalars.{c, v, r} U a ⋙
        extensionByZeroPresheaf.{max c v r} (rings.{c, v, r} R) U,
    (∀ (N : SheafOfModules.{max c v r} ((rings.{c, v, r} S).over U))
      (V : Cᵒᵖ) (x : extensionByZeroPresheafSection (rings.{c, v, r} S) U N V),
      (p.hom.app N).app V x = x) ∧
    ∃ e : localizedSystemExtension.{c, v, r} S U ⋙ scalars.{c, v, r} a ≅
      sliceScalars.{c, v, r} U a ⋙ localizedSystemExtension.{c, v, r} R U,
    (∀ (N : SheafOfModules.{max c v r} ((rings.{c, v, r} S).over U))
      (V : Cᵒᵖ) (phi : V.unop ⟶ U) (x : N.val.obj (op (Over.mk phi))),
      (e.hom.app N).val.app V (generator.{c, v, r} U S N V phi x) =
        generator.{c, v, r} U R ((sliceScalars.{c, v, r} U a).obj N) V phi x) ∧
    Equations e (restrictionIso.{c, v, r} U a)
      (localizedSystemAdjunction.{c, v, r} S U)
      (localizedSystemAdjunction.{c, v, r} R U) ∧
    transportedEquations.{c, v, r, w} U a e := by
  refine ⟨presheafComparison.{c, v, r} U a, ?_, sheafComparison.{c, v, r} U a,
    ?_, sheafComparison_equations.{c, v, r} U a, ?_⟩
  · exact presheafComparison_hom_apply.{c, v, r} U a
  · intro N V phi x
    exact sheafComparison_generator.{c, v, r} U a N V phi x
  · let : Abelian (SheafOfModules.{max c v r} (rings.{c, v, r} R)) :=
      ambientAbelian.{c, v, r} (rings.{c, v, r} R)
    let : Abelian (SheafOfModules.{max c v r} ((rings.{c, v, r} R).over U)) :=
      sliceAbelian.{c, v, r} U ((rings.{c, v, r} R).over U)
    let : Abelian (SheafOfModules.{max c v r} (rings.{c, v, r} S)) :=
      ambientAbelian.{c, v, r} (rings.{c, v, r} S)
    let : Abelian (SheafOfModules.{max c v r} ((rings.{c, v, r} S).over U)) :=
      sliceAbelian.{c, v, r} U ((rings.{c, v, r} S).over U)
    let : Functor.Additive (localizedSystemExtension.{c, v, r} R U) :=
      localizedSystemExtensionAdditive.{c, v, r} R U
    let : PreservesFiniteLimits (localizedSystemExtension.{c, v, r} R U) :=
      localizedSystemExtensionLimits.{c, v, r} R U
    let : PreservesFiniteColimits (localizedSystemExtension.{c, v, r} R U) :=
      localizedSystemExtensionColimits.{c, v, r} R U
    let : Functor.Additive (localizedSystemRestriction.{c, v, r} R U) :=
      localizedSystemRestrictionAdditive.{c, v, r} R U
    let : PreservesFiniteLimits (localizedSystemRestriction.{c, v, r} R U) :=
      localizedSystemRestrictionLimits.{c, v, r} R U
    let : PreservesFiniteColimits (localizedSystemRestriction.{c, v, r} R U) :=
      localizedSystemRestrictionColimits.{c, v, r} R U
    let : Functor.Additive (localizedSystemExtension.{c, v, r} S U) :=
      localizedSystemExtensionAdditive.{c, v, r} S U
    let : PreservesFiniteLimits (localizedSystemExtension.{c, v, r} S U) :=
      localizedSystemExtensionLimits.{c, v, r} S U
    let : PreservesFiniteColimits (localizedSystemExtension.{c, v, r} S U) :=
      localizedSystemExtensionColimits.{c, v, r} S U
    let : Functor.Additive (localizedSystemRestriction.{c, v, r} S U) :=
      localizedSystemRestrictionAdditive.{c, v, r} S U
    let : PreservesFiniteLimits (localizedSystemRestriction.{c, v, r} S U) :=
      localizedSystemRestrictionLimits.{c, v, r} S U
    let : PreservesFiniteColimits (localizedSystemRestriction.{c, v, r} S U) :=
      localizedSystemRestrictionColimits.{c, v, r} S U
    let : PreservesFiniteLimits (scalars.{c, v, r} a) := scalarLimits.{c, v, r} a
    let : PreservesFiniteColimits (scalars.{c, v, r} a) := scalarColimits.{c, v, r} a
    let : PreservesFiniteLimits (sliceScalars.{c, v, r} U a) := sliceLimits.{c, v, r} U a
    let : PreservesFiniteColimits (sliceScalars.{c, v, r} U a) := sliceColimits.{c, v, r} U a
    dsimp only [transportedEquations]
    intro _ _ _ _ _ _ _ _
    exact transport_of_equations.{w, (max c v r) + 1, max c v r}
      (JS := localizedSystemExtension.{c, v, r} S U)
      (JR := localizedSystemExtension.{c, v, r} R U)
      (rU := sliceScalars.{c, v, r} U a) (rT := scalars.{c, v, r} a)
      (qS := localizedSystemRestriction.{c, v, r} S U)
      (qR := localizedSystemRestriction.{c, v, r} R U)
      (sheafComparison.{c, v, r} U a) (restrictionIso.{c, v, r} U a)
      (localizedSystemAdjunction.{c, v, r} S U)
      (localizedSystemAdjunction.{c, v, r} R U)
      (sheafComparison_equations.{c, v, r} U a)

end RingedOpenScalar
end SheafOfModules
