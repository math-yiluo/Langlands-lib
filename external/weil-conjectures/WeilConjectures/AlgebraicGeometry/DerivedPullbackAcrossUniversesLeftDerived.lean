/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackAcrossUniverses
public import WeilConjectures.Algebra.Homology.KFlatPullback
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Left-derived universal property after localization transport

Source: Stacks Project, Tags 06YJ and 05RU.
(blueprint: lem-sc-derived-pullback-across-universes-left-derived).
-/

@[expose] public section
set_option autoImplicit false
universe u wX wY
open CategoryTheory
namespace AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open CategoryTheory.Functor in
private theorem exists_derivedPullback_standard_leftDerived
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (h : ∀ M : SheafOfModules.{u} (moduleRings Y.toRingedSpace),
      P.obj M = SheafOfModules.changeOfRings.{u, u, u}
        (CochainComplex.tensorPullbackRingMap f.base X.sheaf Y.sheaf ⟨f.c⟩)
        (TopCat.Sheaf.inverseImageModule f.base Y.sheaf M))
    (hm : ∀ {M N : SheafOfModules.{u} (moduleRings Y.toRingedSpace)} (a : M ⟶ N),
      P.map a = eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom.{u, u, u}
        (CochainComplex.tensorPullbackRingMap f.base X.sheaf Y.sheaf ⟨f.c⟩)
        (TopCat.Sheaf.inverseImageModule f.base Y.sheaf M)
        (TopCat.Sheaf.inverseImageModuleMap f.base Y.sheaf M a) ≫
        eqToHom (h N).symm)
    [P.Additive] :
    ∃ ε : (@DerivedCategory.Qh _ _ _ (HasDerivedCategory.standard _)) ⋙ @derivedPullback X Y f
        (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) ⟶
        P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          (@DerivedCategory.Qh _ _ _ (HasDerivedCategory.standard _)),
      (@derivedPullback X Y f (HasDerivedCategory.standard _)
        (HasDerivedCategory.standard _)).IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)) := by
  classical
  let : HasDerivedCategory.{u + 1}
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) := HasDerivedCategory.standard _
  let : HasDerivedCategory.{u + 1}
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) := HasDerivedCategory.standard _
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    E, hE, hEmap, hEadd, ε, hL, htri, hK⟩ :=
      derivedPullback_spec f
  have hE' : E = Scheme.Modules.tensorPullback f :=
    CategoryTheory.Functor.ext hE (fun M N a ↦ hEmap a)
  have hP' : P = Scheme.Modules.tensorPullback f :=
    CategoryTheory.Functor.ext h (fun M N a ↦ hm a)
  subst E
  subst P
  exact ⟨ε, hL⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open CategoryTheory.Functor in
private theorem transport_derivedPullback_leftDerived
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (P : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace))
    [P.Additive]
    (ε : (@DerivedCategory.Qh _ _ _ (HasDerivedCategory.standard _)) ⋙ @derivedPullback X Y f
        (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) ⟶
      P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (@DerivedCategory.Qh _ _ _ (HasDerivedCategory.standard _)))
    (hε : (@derivedPullback X Y f (HasDerivedCategory.standard _)
      (HasDerivedCategory.standard _)).IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))) :
    ∃ ε' : DerivedCategory.Qh ⋙ derivedPullbackAcrossUniverses f ⟶
        P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh,
      (derivedPullbackAcrossUniverses f).IsLeftDerivedFunctor ε'
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)) := by
  classical
  let QY := @DerivedCategory.Qh _ _ _ (HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
  let QX := @DerivedCategory.Qh _ _ _ (HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
  let L := @derivedPullback X Y f (HasDerivedCategory.standard _)
    (HasDerivedCategory.standard _)
  let EY := schemeDerivedStandardEquivalence Y
  let EX := schemeDerivedStandardEquivalence X
  let F := P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ QX
  have hkan : L.IsRightKanExtension ε := by
    let := hε
    exact IsLeftDerivedFunctor.isRightKanExtension L ε
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
  let α : QY ⋙ (L ⋙ EX.inverse) ⟶ F ⋙ EX.inverse :=
    (Functor.associator _ _ _).inv ≫ whiskerRight ε EX.inverse
  have hα : (L ⋙ EX.inverse).IsRightKanExtension α := by
    let T := Functor.RightExtension.postcompose₂ QY F EX.inverse
    have : IsIso (𝟙 (F ⋙ EX.inverse)) := ⟨⟨𝟙 _, by simp, by simp⟩⟩
    let a : ((whiskeringRight _ _ _).obj EX.inverse) ⋙
        (whiskeringLeft _ _ _).obj QY ≅
        ((whiskeringLeft _ _ _).obj QY) ⋙ (whiskeringRight _ _ _).obj EX.inverse :=
      NatIso.ofComponents (fun G ↦ (Functor.associator QY G EX.inverse).symm)
        (by intro G H τ; ext K; simp)
    have : T.IsEquivalence := by
      change (CostructuredArrow.map₂ a.hom (𝟙 _)).IsEquivalence
      infer_instance
    have : Limits.PreservesLimit (Functor.empty.{0} (QY.RightExtension F)) T :=
      (Adjunction.isEquivalencePreservesLimits T).preservesLimitsOfShape.preservesLimit
    exact ⟨⟨Limits.IsTerminal.ofIso
      (Limits.IsTerminal.isTerminalObj T _
        (L.isUniversalOfIsRightKanExtension ε))
      (Functor.RightExtension.postcompose₂ObjMkIso EX.inverse ε)⟩⟩
  let eX : F ⋙ EX.inverse ≅
      P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
    (Functor.associator _ _ _) ≪≫ isoWhiskerLeft _
      (Localization.compUniqInverse DerivedCategory.Qh QX
        (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)))
  let β := α ≫ eX.hom
  have hβ : (L ⋙ EX.inverse).IsRightKanExtension β :=
    (Functor.isRightKanExtension_iff_of_iso₂ α β eX (Iso.refl _)
      (by simp [β])).mp hα
  let eY : DerivedCategory.Qh ⋙ EY.functor ≅ QY :=
    Localization.compUniqFunctor DerivedCategory.Qh QY
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
  let δ := (Functor.associator _ _ _).inv ≫ whiskerRight eY.hom _ ≫ β
  have hδ : (EY.functor ⋙ L ⋙ EX.inverse).IsRightKanExtension δ :=
    (Functor.isRightKanExtension_iff_postcomp₁ EY.functor eY β).mp hβ
  exact ⟨δ, ⟨hδ⟩⟩

/-- The transported pullback remains a left derived functor of the concrete tensor
pullback. Source: Stacks Project, Tags 06YJ and 05RU.
(blueprint: lem-sc-derived-pullback-across-universes-left-derived).

Proof: the object and morphism formulas identify P with scheme tensor pullback.
In the standard localization, unfold derivedPullback and take the counit and its
left-derived universal property from derivedPullback_spec. Precompose and
postcompose by the localization equivalences defining derivedPullbackAcrossUniverses.
Use the canonical factorization isomorphisms Qh ⋙ E ≅ Qh_standard for both schemes
and the associators of functor composition to transport the counit to the displayed
source and target. For any competing counit, precompose and postcompose by the inverse
 equivalences, apply the standard left-derived universal property, and transport the
unique resulting natural transformation back. Cancellation of the equivalence unit
and counit proves both factorization and uniqueness. Thus the transported comparison
is left derived without a common localization universe. This applies also to empty
schemes, zero complexes, and identity morphisms. -/
theorem exists_derivedPullbackAcrossUniverses_leftDerived
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (P : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (h : ∀ M : SheafOfModules.{u} (moduleRings Y.toRingedSpace),
      P.obj M = SheafOfModules.changeOfRings.{u, u, u}
        (CochainComplex.tensorPullbackRingMap f.base X.sheaf Y.sheaf ⟨f.c⟩)
        (TopCat.Sheaf.inverseImageModule f.base Y.sheaf M))
    (hm : ∀ {M N : SheafOfModules.{u} (moduleRings Y.toRingedSpace)} (a : M ⟶ N),
      P.map a = eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom.{u, u, u}
        (CochainComplex.tensorPullbackRingMap f.base X.sheaf Y.sheaf ⟨f.c⟩)
        (TopCat.Sheaf.inverseImageModule f.base Y.sheaf M)
        (TopCat.Sheaf.inverseImageModuleMap f.base Y.sheaf M a) ≫
        eqToHom (h N).symm)
    [P.Additive] :
    ∃ ε : DerivedCategory.Qh ⋙ derivedPullbackAcrossUniverses f ⟶
        P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh,
      (derivedPullbackAcrossUniverses f).IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
          (ComplexShape.up ℤ)) := by
  obtain ⟨ε, hε⟩ := exists_derivedPullback_standard_leftDerived f P h hm
  exact transport_derivedPullback_leftDerived f P ε hε

end AlgebraicGeometry
