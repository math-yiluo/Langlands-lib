/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorData
import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorTransportInternalCounit
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Derived total normalization of the quotient section tensor comparison

## References

* Stacks 06YS, 07A4 and 0G7D
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj ChangeOfRings

namespace AlgebraicGeometry.ProEtale.QuotientSectionTensor

open QuotientChange IntegralQuotient
open ModuleRingedComparison

attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory CategoryTheory.Mod.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor
  ModuleRingedComparison.tensor ModuleRingedComparison.qTensor
  CategoryTheory.Functor.mapDerivedCategory

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)]

universe uc vc w

private theorem resolving_of_iso
    {C : Type uc} [Category.{vc} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
    {A : Sheaf J CommRingCat.{w}}
    {P Q : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj A)) ℤ}
    (e : P ≅ Q) (hQ : CochainComplex.IsKFlatIndependentCoefficients (R := A) Q)
    (hfQ : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (R := A) (Q.X n)) :
    CochainComplex.IsKFlatIndependentCoefficients (R := A) P ∧
      (∀ n : ℤ, SheafOfModules.IsFlatOnSite (R := A) (P.X n)) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients A
  let := SheafOfModules.monoidalCategory A
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients A
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients A
  have (I : Type w) : HasColimitsOfShape (Discrete I) (PresheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj A).obj) :=
    PresheafOfModules.hasColimitsOfShape _ _
  constructor
  · intro V hV n
    exact (hQ V hV n).of_iso (((curriedTensor _).map₂CochainComplex.obj V).mapIso e.symm)
  · intro n
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso A (Q.X n) ≪≫
        (curriedTensor _).flip.mapIso ((HomologicalComplex.eval _ _ n).mapIso e.symm) ≪≫
        (SheafOfModules.siteSheafTensorRightIso A (P.X n)).symm) (hfQ n)

private theorem app_eq_of_iso
    {A B : Type*} [Category A] [Category B] {F G : A ⥤ B}
    (α β : F ⟶ G) {X Y : A} (e : X ≅ Y) (h : α.app X = β.app X) :
    α.app Y = β.app Y := by
  apply (cancel_epi (F.mapIso e).hom).mp
  change F.map e.hom ≫ α.app Y = F.map e.hom ≫ β.app Y
  rw [α.naturality, β.naturality, h]

private theorem total_comparison_naturality
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    {TA : A ⥤ A ⥤ A} [TA.PreservesZeroMorphisms]
    [∀ M, (TA.obj M).PreservesZeroMorphisms]
    {TB : B ⥤ B ⥤ B} [TB.PreservesZeroMorphisms]
    [∀ M, (TB.obj M).PreservesZeroMorphisms]
    [∀ P Q : CochainComplex A ℤ, P.HasMapBifunctor Q TA]
    [∀ P Q : CochainComplex B ℤ, P.HasMapBifunctor Q TB]
    {F : A ⥤ B} [F.Additive] [PreservesColimitsOfSize.{0, 0} F]
    (e : (Functor.postcompose₂.obj F).obj TA ⟶
      (((Functor.whiskeringLeft₂ _).obj F).obj F).obj TB)
    {M N : CochainComplex A ℤ × CochainComplex A ℤ} (f : M ⟶ N) :
    (F.mapHomologicalComplex (.up ℤ)).map ((cochainTotalFunctor TA).map f) ≫
        HomologicalComplex.mapBifunctorComparison e (.up ℤ) N.1 N.2 =
      HomologicalComplex.mapBifunctorComparison e (.up ℤ) M.1 M.2 ≫
        (cochainTotalFunctor TB).map
          (Prod.mkHom ((F.mapHomologicalComplex (.up ℤ)).map f.1)
            ((F.mapHomologicalComplex (.up ℤ)).map f.2)) := by
  let G := F.mapHomologicalComplex (.up ℤ)
  change G.map
      (HomologicalComplex.mapBifunctorMap f.1 (𝟙 M.2) TA (.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap (𝟙 N.1) f.2 TA (.up ℤ)) ≫
      HomologicalComplex.mapBifunctorComparison e (.up ℤ) N.1 N.2 =
    HomologicalComplex.mapBifunctorComparison e (.up ℤ) M.1 M.2 ≫
      (HomologicalComplex.mapBifunctorMap (G.map f.1) (𝟙 (G.obj M.2)) TB (.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap (𝟙 (G.obj N.1)) (G.map f.2) TB (.up ℤ))
  have h₁ := HomologicalComplex.mapBifunctorComparison_naturality e (.up ℤ) f.1 (𝟙 M.2)
  have h₂ := HomologicalComplex.mapBifunctorComparison_naturality e (.up ℤ) (𝟙 N.1) f.2
  rw [G.map_comp, Category.assoc, h₂, ← Category.assoc, h₁, Category.assoc]
  dsimp only [G]
  rw [(F.mapHomologicalComplex (.up ℤ)).map_id,
    (F.mapHomologicalComplex (.up ℤ)).map_id]

attribute [local irreducible] CochainComplex.IsKFlatIndependentCoefficients
  SheafOfModules.IsFlatOnSite

-- Elaborate the whiskered diagram without unfolding derived tensor structures.
-- STATEMENT-DISPUTED (old signature): an arbitrary barB need not satisfy the counit
-- equation. The repaired statement requires its tensor-section conjugation square.
/-- The pure section comparison extends to the normalized signed total on K-flat pairs
for the section conjugate of the given internal tensorator. -/
theorem section_tensor_transport_normalized_total (T : Scheme.{u})
    (c : ScalarSectionData a T) (hc : ScalarSectionNormalized a T c)
    (b : TensorIso a T) (hb : TensorNormalized a T b)
    (barB : tensor Λ T ⋙ c.model.T ≅
      (c.model.T.prod c.model.T) ⋙ tensor Λ' T)
    (hbarB : TensorSectionCondition a T c b barB)
    (e : (Functor.postcompose₂.obj c.model.E).obj (curriedTensor (modules Λ T)) ⟶
        (((Functor.whiskeringLeft₂ _).obj c.model.E).obj c.model.E).obj
          (curriedTensor (modules Λ' T)))
    (he : ∀ (M N : modules Λ T) (W : T.ProEtᵒᵖ) (m : M.val.obj W)
      (n : N.val.obj W) (s : (ring Λ' T).obj.obj W),
      (((e.app M).app N).val.app W)
          (sectionScalarElement a T c (M ⊗ N) W
            (sectionPureTensor Λ T M N W m n) s) =
        sectionPureTensor Λ' T (c.model.E.obj M) (c.model.E.obj N) W
          (sectionScalarElement a T c M W m 1)
          (sectionScalarElement a T c N W n s)) :
    ∀ P Q : CochainComplex (modules Λ T) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := ring Λ T) P →
      CochainComplex.IsKFlatIndependentCoefficients (R := ring Λ T) Q →
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology T)
        (R := ring Λ T) (P.X i)) →
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology T)
        (R := ring Λ T) (Q.X i)) →
      ∃ g : (c.model.E.mapHomologicalComplex (.up ℤ)).obj
            ((totalTensor Λ T).obj (P, Q)) ⟶
          (totalTensor Λ' T).obj
            ((c.model.E.mapHomologicalComplex (.up ℤ)).obj P,
              (c.model.E.mapHomologicalComplex (.up ℤ)).obj Q),
        (∀ (i j k : ℤ) (h : i + j = k),
          c.model.E.map
              (CochainComplex.ιMapBifunctor P Q (curriedTensor (modules Λ T))
                i j k h) ≫ g.f k =
            (e.app (P.X i)).app (Q.X j) ≫
              CochainComplex.ιMapBifunctor
                ((c.model.E.mapHomologicalComplex (.up ℤ)).obj P)
                ((c.model.E.mapHomologicalComplex (.up ℤ)).obj Q)
                (curriedTensor (modules Λ' T)) i j k h) ∧
        barB.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
            (tensor Λ' T).map (Prod.mkHom (c.model.ε.app P) (c.model.ε.app Q)) ≫
            (qTensor Λ' T).app
              ((c.model.E.mapHomologicalComplex (.up ℤ)).obj P,
                (c.model.E.mapHomologicalComplex (.up ℤ)).obj Q) =
          c.model.T.map ((qTensor Λ T).app (P, Q)) ≫
            c.model.ε.app ((totalTensor Λ T).obj (P, Q)) ≫ DerivedCategory.Q.map g := by
  let : PreservesColimitsOfSize.{0, 0}
      ((equivalence Λ T).functor ⋙ c.model.E) :=
    preservesColimits_of_natIso c.ordinary
  let : PreservesColimitsOfSize.{0, 0} c.model.E :=
    preservesColimits_of_natIso
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (equivalence Λ T).counitIso c.model.E ≪≫
        Functor.leftUnitor c.model.E)
  intro P Q hP hQ hfP hfQ
  refine ⟨HomologicalComplex.mapBifunctorComparison e (.up ℤ) P Q, ?_, ?_⟩
  · intro i j k h
    exact HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
      e (.up ℤ) P Q i j k h
  · let ec := (equivalence Λ T).mapHomologicalComplex (.up ℤ)
    let P₀ := ec.inverse.obj P
    let Q₀ := ec.inverse.obj Q
    let σ : ec.functor.obj P₀ ≅ P := ec.counitIso.app P
    let τ : ec.functor.obj Q₀ ≅ Q := ec.counitIso.app Q
    have hP₀ := resolving_of_iso (A := ring Λ T) σ hP hfP
    have hQ₀ := resolving_of_iso (A := ring Λ T) τ hQ hfQ
    have h := section_tensor_transport_internal_counit a T c hc b hb barB hbarB e he
      P₀ Q₀ hP₀.1 hQ₀.1 hP₀.2 hQ₀.2
    let E := c.model.E.mapHomologicalComplex (.up ℤ)
    let QR := DerivedCategory.Q (C := modules Λ T)
    let QS := DerivedCategory.Q (C := modules Λ' T)
    let TR := totalTensor Λ T
    let TS := totalTensor Λ' T
    let B := tensor Λ T
    let C := tensor Λ' T
    let δ : TR ⋙ E ⟶ E.prod E ⋙ TS :=
      { app := fun K ↦ HomologicalComplex.mapBifunctorComparison e (.up ℤ) K.1 K.2
        naturality := fun _ _ f ↦ total_comparison_naturality e f }
    let L : QR.prod QR ⋙ B ⋙ c.model.T ⟶ E.prod E ⋙ TS ⋙ QS :=
      Functor.whiskerRight (qTensor Λ T) c.model.T ≫
        Functor.whiskerLeft TR c.model.ε ≫ Functor.whiskerRight δ QS
    let U : QR.prod QR ⋙ B ⋙ c.model.T ⟶ E.prod E ⋙ TS ⋙ QS :=
      Functor.whiskerLeft (QR.prod QR) barB.hom ≫
        Functor.whiskerRight (NatTrans.prod c.model.ε c.model.ε) C ≫
        Functor.whiskerLeft (E.prod E) (qTensor Λ' T)
    have h₀ : U.app (ec.functor.obj P₀, ec.functor.obj Q₀) =
        L.app (ec.functor.obj P₀, ec.functor.obj Q₀) := by
      exact h
    exact app_eq_of_iso U L (Iso.prod σ τ) h₀

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
