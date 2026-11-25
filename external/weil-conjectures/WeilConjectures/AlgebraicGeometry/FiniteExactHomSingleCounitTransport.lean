/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.AffineSinglePushforwardUnitIso
import WeilConjectures.AlgebraicGeometry.SingleRightDerivedExactComposition
import WeilConjectures.AlgebraicGeometry.ExactDerivedAdjunctionSingleCounit
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import all Mathlib.Algebra.Homology.Localization

/-! # Canonical single-complex transport of a derived scalar counit

Source: Stacks Project, Tags 0AVW and 0AX3
(blueprint: lem-sc-finite-exact-hom-single-counit-transport). -/

@[expose] public section

section ProofAssembly

universe uC uA uB vC vA vB wC wDA wB
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace CategoryTheory
variable {C : Type uC} {A : Type uA} {B : Type uB}
  [Category.{vC} C] [Category.{vA} A] [Category.{vB} B]
  [Abelian C] [Abelian A] [Abelian B]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wDA} A]
  [HasDerivedCategory.{wB} B] [HasKInjectiveResolutions C]
  [HasKInjectiveResolutions A] [HasKInjectiveResolutions B]
omit [HasKInjectiveResolutions B] in
private theorem derivedNatIso_refl (F : C ⥤ B) [F.Additive] :
    Functor.rightDerivedFunctorNatIso (Iso.refl F) = Iso.refl F.rightDerivedFunctor := by
  ext
  simp [Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans]

private theorem assembly (F : C ⥤ A) (T : A ⥤ B) (H : B ⥤ A)
    [F.Additive] [T.Additive] [H.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [T.ReflectsIsomorphisms]
    (adj : T ⊣ H) (M : C) (L : B)
    (hcf : IsIso (DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex (F ⋙ T)
        (ComplexShape.up ℤ) 0).inv.app M) ≫
      (F ⋙ T).rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj
        ((CochainComplex.singleFunctor C 0).obj M))))
    (e : F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj M) ≅
      H.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor B 0).obj L)) :
    ∃ j : F.obj M ≅ H.obj L,
      (DerivedCategory.singleFunctor B 0).map (T.map j.hom ≫ adj.counit.app L) =
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex (F ⋙ T)
          (ComplexShape.up ℤ) 0).inv.app M) ≫
        (F ⋙ T).rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj
          ((CochainComplex.singleFunctor C 0).obj M)) ≫
        (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F T).hom.app
          ((DerivedCategory.singleFunctor C 0).obj M) ≫
        T.mapDerivedCategory.map e.hom ≫
        adj.mapDerivedCategoryRightDerivedAdjunction.counit.app
          ((DerivedCategory.singleFunctor B 0).obj L) := by
  classical
  let K := (CochainComplex.singleFunctor C 0).obj M
  let cg : (DerivedCategory.singleFunctor A 0).obj (F.obj M) ⟶
      F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj M) :=
    DerivedCategory.Q.map
    ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app M) ≫
    F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj K)
  let cf : (DerivedCategory.singleFunctor B 0).obj (T.obj (F.obj M)) ⟶
      (F ⋙ T).rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj M) :=
    DerivedCategory.Q.map
    ((HomologicalComplex.singleMapHomologicalComplex (F ⋙ T)
      (ComplexShape.up ℤ) 0).inv.app M) ≫
    (F ⋙ T).rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj K)
  let t := (T.mapDerivedCategorySingleFunctor 0).app (F.obj M)
  let g := (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F T).app
    ((DerivedCategory.singleFunctor C 0).obj M)
  have hcomp : t.inv ≫ T.mapDerivedCategory.map cg ≫ g.inv = cf :=
    F.single_rightDerived_exact_composition T M
  have : T.mapDerivedCategory.ReflectsIsomorphisms := by
    constructor
    intro P Q a ha
    rw [DerivedCategory.isIso_iff]
    intro n
    have : IsIso ((DerivedCategory.homologyFunctor _ n ⋙ T).map a) :=
      (NatIso.isIso_map_iff (T.mapDerivedCategoryHomologyFunctorIso n) a).mpr
        (by dsimp; infer_instance)
    have : IsIso (T.map ((DerivedCategory.homologyFunctor A n).map a)) := ‹_›
    exact isIso_of_reflects_iso ((DerivedCategory.homologyFunctor _ n).map a) T
  have : IsIso (t.inv ≫ T.mapDerivedCategory.map cg ≫ g.inv) := by
    rw [hcomp]
    exact hcf
  have : IsIso (T.mapDerivedCategory.map cg ≫ g.inv) :=
    IsIso.of_isIso_comp_left t.inv _
  have : IsIso (T.mapDerivedCategory.map cg) := IsIso.of_isIso_comp_right _ g.inv
  have : IsIso cg := isIso_of_reflects_iso cg T.mapDerivedCategory
  let h := H.singleFunctorCompRightDerivedFunctorIso.app L
  let d := asIso cg ≪≫ e ≪≫ h
  let S := DerivedCategory.singleFunctor A 0
  let j := S.preimageIso d
  refine ⟨j, ?_⟩
  have hj : S.map j.hom = cg ≫ e.hom ≫ h.hom := by
    change S.map (S.preimage d.hom) = _
    rw [Functor.map_preimage]
    rfl
  have hcounit := adj.exact_derivedAdjunction_single_counit L
  have heq : (DerivedCategory.singleFunctor B 0).map (T.map j.hom) =
      t.inv ≫ T.mapDerivedCategory.map (S.map j.hom) ≫
        (T.mapDerivedCategorySingleFunctor 0).hom.app (H.obj L) := by
    have hn := (T.mapDerivedCategorySingleFunctor 0).hom.naturality j.hom
    dsimp only [Functor.comp_map] at hn
    exact (t.inv_comp_eq.mpr hn).symm
  have hc : (T.mapDerivedCategorySingleFunctor 0).hom.app (H.obj L) ≫
      (DerivedCategory.singleFunctor B 0).map (adj.counit.app L) =
      T.mapDerivedCategory.map h.inv ≫
        adj.mapDerivedCategoryRightDerivedAdjunction.counit.app
          ((DerivedCategory.singleFunctor B 0).obj L) := hcounit.symm
  simp only [← Category.assoc]
  change (DerivedCategory.singleFunctor B 0).map (T.map j.hom ≫ adj.counit.app L) =
    ((cf ≫ g.hom) ≫ T.mapDerivedCategory.map e.hom) ≫
      adj.mapDerivedCategoryRightDerivedAdjunction.counit.app _
  simp only [Category.assoc]
  rw [Functor.map_comp, heq]
  simp only [Category.assoc]
  rw [hc, hj]
  simp only [Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc,
    Iso.hom_inv_id, Functor.map_id, Category.id_comp]
  rw [← hcomp]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simp only [Functor.map_comp, Category.assoc]
private theorem assembly_transport (F : C ⥤ A) (T : A ⥤ B) (H : B ⥤ A)
    (G : C ⥤ B)
    [F.Additive] [T.Additive] [H.Additive] [G.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [T.ReflectsIsomorphisms]
    (adj : T ⊣ H) (M : C) (L : B) (hFT : F ⋙ T = G)
    (hcf : IsIso (DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex G
        (ComplexShape.up ℤ) 0).inv.app M) ≫
      G.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj
        ((CochainComplex.singleFunctor C 0).obj M))))
    (γ : F.rightDerivedFunctor ⋙ T.mapDerivedCategory ≅ G.rightDerivedFunctor)
    (hγ : γ = (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F T).symm ≪≫
      Functor.rightDerivedFunctorNatIso (eqToIso hFT))
    (e : F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj M) ≅
      H.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor B 0).obj L)) :
    ∃ j : F.obj M ≅ H.obj L,
      (DerivedCategory.singleFunctor B 0).map (T.map j.hom ≫ adj.counit.app L) =
      eqToHom (congrArg (fun J : C ⥤ B =>
        (DerivedCategory.singleFunctor B 0).obj (J.obj M)) hFT) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex G
          (ComplexShape.up ℤ) 0).inv.app M) ≫
        G.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj
          ((CochainComplex.singleFunctor C 0).obj M)) ≫
        γ.inv.app ((DerivedCategory.singleFunctor C 0).obj M) ≫
        T.mapDerivedCategory.map e.hom ≫
        adj.mapDerivedCategoryRightDerivedAdjunction.counit.app
          ((DerivedCategory.singleFunctor B 0).obj L) := by
  subst G
  simp only [eqToIso_refl, derivedNatIso_refl, Iso.trans_refl] at hγ
  subst γ
  simpa only [eqToHom_refl, Category.id_comp, Iso.symm_inv] using
    assembly F T H adj M L hcf e

end CategoryTheory

end ProofAssembly

universe u wX wY wA

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem directImageAlgebra_factorization {X Y : Scheme.{u}} (f : X ⟶ Y) :
    RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f) ⋙
      SheafOfModules.restrictScalars.{u}
        (R := moduleRings Y.toRingedSpace)
        (R' := moduleRings (directImageAlgebraSpace f)) f.toRingCatSheafHom =
      RingedSpace.moduleDirectImage f.toLRSHom.toShHom := rfl

private theorem directImageAlgebra_restrictScalars_reflects
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (SheafOfModules.restrictScalars.{u}
      (R := moduleRings Y.toRingedSpace)
      (R' := moduleRings (directImageAlgebraSpace f))
      f.toRingCatSheafHom).ReflectsIsomorphisms := by
  let T := SheafOfModules.restrictScalars.{u}
    (R := moduleRings Y.toRingedSpace)
    (R' := moduleRings (directImageAlgebraSpace f)) f.toRingCatSheafHom
  have heT : T ⋙ SheafOfModules.toSheaf.{u} (moduleRings Y.toRingedSpace) ≅
      SheafOfModules.toSheaf.{u} (moduleRings (directImageAlgebraSpace f)) := Iso.refl _
  have : (T ⋙ SheafOfModules.toSheaf.{u}
      (moduleRings Y.toRingedSpace)).ReflectsIsomorphisms :=
    reflectsIsomorphisms_of_iso heT.symm
  exact reflectsIsomorphisms_of_comp T
    (SheafOfModules.toSheaf.{u} (moduleRings Y.toRingedSpace))

set_option backward.isDefEq.lazyWhnfCore false in
-- Elaborating the canonical factorization unfolds the two ring-sheaf presentations.
/-- Lift an algebra-valued derived isomorphism between single complexes, keeping
track of the scalar adjunction counit through the canonical pushforward factorization.
Source: Stacks Project, Tag 0AVW, canonical factorization; Tag 0AX3, counit comparison
(blueprint: lem-sc-finite-exact-hom-single-counit-transport).

Proof: Let F be g_* and T scalar restriction. Form the canonical comparison from
(F M)[0] to RF(M[0]) using the inverse termwise single comparison and the right-derived
unit. Under exact T and the specified canonical gamma this becomes the analogous
f_* comparison. The latter is invertible for quasi-coherent M by affine vanishing.
Exact scalar restriction reflects isomorphisms on derived categories: it commutes with
cohomology, reflects isomorphisms of modules (the underlying abelian sheaf is unchanged),
and cohomology detects derived isomorphisms. Thus the g_* comparison is invertible.
Compose it with e and the exact-H single comparison. Full faithfulness of the single
functor lifts this composite isomorphism to j. Map j by exact T and apply the derived
adjunction counit. The derived counit factorization on L[0] identifies the last two
factors with the single of adjH.counit at L. Naturality of the exact-T single comparison
and the canonical gamma factorization replace the first factors with the f_* comparison
followed by gamma inverse. This is exactly the equation stated. All comparisons are
canonical; arbitrary rescalings of gamma are excluded by hγ. The zero module and empty
schemes satisfy the same factorization and full-faithfulness identities. -/
theorem finite_exactHom_single_counit_transport
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wA} (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))]
    [IsAffineHom f]
    (M : X.Modules) (hM : M.IsQuasicoherent) (L : Y.Modules)
    [PreservesFiniteLimits (SheafOfModules.restrictScalars
      (R := moduleRings Y.toRingedSpace)
      (R' := moduleRings (directImageAlgebraSpace f)) f.toRingCatSheafHom)]
    [PreservesFiniteColimits (SheafOfModules.restrictScalars
      (R := moduleRings Y.toRingedSpace)
      (R' := moduleRings (directImageAlgebraSpace f)) f.toRingCatSheafHom)]
    (H : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))
    [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (adjH : SheafOfModules.restrictScalars
        (R := moduleRings Y.toRingedSpace)
        (R' := moduleRings (directImageAlgebraSpace f)) f.toRingCatSheafHom ⊣ H)
    (γ : RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace f) ⋙
      (SheafOfModules.restrictScalars
        (R := moduleRings Y.toRingedSpace)
        (R' := moduleRings (directImageAlgebraSpace f)) f.toRingCatSheafHom).mapDerivedCategory ≅
        schemeDerivedDirectImage f)
    (hγ : γ =
      (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
        (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f))
        (SheafOfModules.restrictScalars
        (R := moduleRings Y.toRingedSpace)
        (R' := moduleRings (directImageAlgebraSpace f)) f.toRingCatSheafHom)).symm ≪≫
      Functor.rightDerivedFunctorNatIso
        (show RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f) ⋙
          SheafOfModules.restrictScalars
        (R := moduleRings Y.toRingedSpace)
        (R' := moduleRings (directImageAlgebraSpace f)) f.toRingCatSheafHom ≅
          RingedSpace.moduleDirectImage f.toLRSHom.toShHom from Iso.refl _))
    (e : (RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace f)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M) ≅
      H.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj L)) :
    ∃ j : (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)).obj M ≅ H.obj L,
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map
          ((SheafOfModules.restrictScalars
        (R := moduleRings Y.toRingedSpace)
        (R' := moduleRings (directImageAlgebraSpace f)) f.toRingCatSheafHom).map j.hom ≫
            adjH.counit.app L) =
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex
          (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) (ComplexShape.up ℤ) 0).inv.app M) ≫
        (cast (by rfl)
          ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app
            ((HomotopyCategory.quotient _ _).obj ((CochainComplex.singleFunctor
              (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M))) :
          _ ⟶ (schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M)) ≫
        γ.inv.app ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M) ≫
        (SheafOfModules.restrictScalars
        (R := moduleRings Y.toRingedSpace)
        (R' := moduleRings (directImageAlgebraSpace f)) f.toRingCatSheafHom).mapDerivedCategory.map
          e.hom ≫
        adjH.mapDerivedCategoryRightDerivedAdjunction.counit.app
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj L) := by
  let F := RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)
  let T := SheafOfModules.restrictScalars.{u}
    (R := moduleRings Y.toRingedSpace)
    (R' := moduleRings (directImageAlgebraSpace f)) f.toRingCatSheafHom
  have : T.ReflectsIsomorphisms := directImageAlgebra_restrictScalars_reflects f
  have hFT : F ⋙ T = RingedSpace.moduleDirectImage f.toLRSHom.toShHom :=
    directImageAlgebra_factorization f
  have hf := affine_singlePushforward_unit_isIso f M hM
  rw [← eqToIso_refl (rfl : F ⋙ T = F ⋙ T)] at hγ
  have result := CategoryTheory.assembly_transport F T H
    (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) adjH M L hFT hf γ hγ e
  simpa only [eqToHom_refl, Category.id_comp, cast_eq] using result

end AlgebraicGeometry
