/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenPinnedComposition
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenPinnedAdjunction
public import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenUnitSquareFactorization
import all WeilConjectures.AlgebraicGeometry.SingleComplexOpenRestrictedCounitCancellation
import all WeilConjectures.AlgebraicGeometry.OpenPinnedSourceCounitTriangle
import all WeilConjectures.AlgebraicGeometry.OpenPinnedTargetCounitTriangle
import all WeilConjectures.AlgebraicGeometry.OpenPinnedTensorComparisonCoherence
import all WeilConjectures.AlgebraicGeometry.OpenPinnedTensorCounitTransport
import all WeilConjectures.AlgebraicGeometry.OpenPinnedCounitHomotopyRestriction

/-! # The open pullback square evaluated on a direct-image representative

Source: Stacks Project, Tags 08FE, 08HY and 0D5S.
(blueprint: lem-pc-k3-open-counit-homotopy-factorization).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option linter.unusedVariables false

section

/-- Lift a commuting square of additive functors to their homotopy categories. -/
noncomputable def mapHomotopySquare
    {C D B E : Type*} [Category C] [Category D] [Category B] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive B] [Preadditive E]
    {F : C ⥤ D} {G : D ⥤ E} {R : C ⥤ B} {J : B ⥤ E}
    [F.Additive] [G.Additive] [R.Additive] [J.Additive]
    (e : F ⋙ G ≅ R ⋙ J) :
    F.mapHomotopyCategory (.up ℤ) ⋙ G.mapHomotopyCategory (.up ℤ) ≅
      R.mapHomotopyCategory (.up ℤ) ⋙ J.mapHomotopyCategory (.up ℤ) :=
  Functor.mapHomotopyCategoryCompIso e (.up ℤ) ≪≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ J)) (.up ℤ)).symm

private theorem targetHomotopyComparison
    {C D E : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D]
    [Category E] [Preadditive E]
    {F : C ⥤ D} {G R : D ⥤ E} {H : C ⥤ E}
    [F.Additive] [G.Additive] [R.Additive] [H.Additive]
    (e : G ≅ R) (a : F ⋙ G ≅ H) (P : HomotopyCategory C (.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso a (.up ℤ)).hom.app P ≫
        (Functor.mapHomotopyCategoryCompIso
          (Functor.isoWhiskerLeft F e.symm ≪≫ a) (.up ℤ)).inv.app P =
      (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app
        ((F.mapHomotopyCategory (.up ℤ)).obj P) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  change (HomotopyCategory.quotient E (.up ℤ)).map
      ((Functor.mapHomologicalComplexCompIso a (.up ℤ)).hom.app K) ≫
    (HomotopyCategory.quotient E (.up ℤ)).map
      ((Functor.mapHomologicalComplexCompIso
        (Functor.isoWhiskerLeft F e.symm ≪≫ a) (.up ℤ)).inv.app K) =
    (HomotopyCategory.quotient E (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app
        ((F.mapHomologicalComplex (.up ℤ)).obj K))
  rw [← Functor.map_comp]
  congr 1
  ext n
  simp [Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
    NatTrans.mapHomologicalComplex]

end

/-- Derived compatibility before the sectionwise mate identity.
Source: Stacks Project, Tags 08FE, 08HY and 0D5S.
(blueprint: lem-pc-k3-open-counit-homotopy-factorization).

Proof: The pinned Hom equivalence identifies pullback of the right-derived unit
followed by the derived counit with the left-derived counit followed by localization
of the homotopy counit. Move that unit across the five-factor pullback square by
naturality. Apply open_pinned_counit_homotopy_restriction to the direct-image
homotopy complex, and cancel the target restriction and tensor restriction
isomorphisms. Naturality of the source restriction factorization moves localization
of the homotopy counit through restriction. Functoriality of Qh then joins the
inverse tensor comparison and restricted homotopy counit into the displayed arrow.
This calculation does not identify that arrow with the restricted-morphism counit;
that is the separate sectionwise mate identity. It uses no inverse of the derived
unit, so applies also to unbounded complexes, empty opens and the zero complex. -/
theorem singleComplexOpen_pullback_counit_homotopy_factorization
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    (I : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    let _ : ∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z),
      (Scheme.Modules.tensorPullback k).Additive :=
      @Classical.choose _ _ exists_derivedPullbackComposition
    let F := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    let F₀ := RingedSpace.moduleDirectImage (f ∣_ V).toLRSHom.toShHom
    let rY := schemeOpenRestriction Y V
    let rX := schemeOpenRestriction X (f ⁻¹ᵁ V)
    let a := @singleComplexOpenPinnedAdjunction.{u, w} _
    let c := @singleComplexOpenPinnedComposition.{u, w} _
    let ε := @Classical.choose _ _
      (Classical.choose_spec exists_derivedPullbackComposition)
    (derivedPullback (f ∣_ V)).map
        (rY.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (.up ℤ)).obj I) ≫
          rY.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app I)) ≫
      ((derivedPullback (f ∣_ V)).mapIso
          ((singleComplexOpenPullbackIso Y V).symm.app
            ((schemeDerivedDirectImage f).obj (DerivedCategory.Qh.obj I))) ≪≫
        (c (f ∣_ V) V.ι).app ((schemeDerivedDirectImage f).obj (DerivedCategory.Qh.obj I)) ≪≫
        eqToIso (congrArg
          (fun k ↦ (derivedPullback k).obj
            ((schemeDerivedDirectImage f).obj (DerivedCategory.Qh.obj I)))
          (morphismRestrict_ι f V)) ≪≫
        (c (f ⁻¹ᵁ V).ι f).symm.app
          ((schemeDerivedDirectImage f).obj (DerivedCategory.Qh.obj I)) ≪≫
        (singleComplexOpenPullbackIso X (f ⁻¹ᵁ V)).app
          ((derivedPullback f).obj
            ((schemeDerivedDirectImage f).obj (DerivedCategory.Qh.obj I)))).hom ≫
      rX.mapDerivedCategory.map ((a f).counit.app (DerivedCategory.Qh.obj I)) ≫
      rX.mapDerivedCategoryFactorsh.hom.app I =
    (ε (f ∣_ V)).app ((rY.mapHomotopyCategory (.up ℤ)).obj
      ((F.mapHomotopyCategory (.up ℤ)).obj I)) ≫
      DerivedCategory.Qh.map
        ((openPinnedHomotopyTensorRestrictionIso f V (f ⁻¹ᵁ V) (f ∣_ V)
            (morphismRestrict_ι f V)).inv.app ((F.mapHomotopyCategory (.up ℤ)).obj I) ≫
          (rX.mapHomotopyCategory (.up ℤ)).map
            (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f))
              |>.mapHomotopyCategory (.up ℤ)).counit.app I)) := by
  have h₁ := singleComplexOpen_unit_square_factorization f V I
  have h₂ := singleComplexOpen_restricted_counit_cancellation f V I
  exact Eq.trans h₁ h₂

end AlgebraicGeometry
