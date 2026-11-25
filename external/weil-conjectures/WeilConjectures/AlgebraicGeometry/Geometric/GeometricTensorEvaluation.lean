/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Geometric.GeometricOrdinaryRealization
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.AlgebraicGeometry.Tensor.TensorComparisonModelPreservesFlat
import WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.AlgebraicGeometry.Tensor.TensorComparisonCochainSquare
import all WeilConjectures.AlgebraicGeometry.System.SystemTensorReductionFormula

/-! # Evaluation compatibility of representative-normalized tensor comparisons

Source: Zheng Construction 4.1; Stacks 06YU and 07A4.
(blueprint: lem-coef-semilinear-geometric-tensor-evaluation)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option genInjectivity false
set_option genSizeOfSpec false
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections
attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  HasDerivedCategory.standard DerivedCategory SheafOfModules.monoidalCategory
  CoefficientClosedStructure.tensor

section FlatPreservation
variable {C₀ C₁ : Type c} [Category.{v} C₀] [Category.{v} C₁]
  [EssentiallySmall.{max c v r} C₀] [EssentiallySmall.{max c v r} C₁]
  (J₀ : GrothendieckTopology C₀) (J₁ : GrothendieckTopology C₁)
  (R₀ : Sheaf J₀ CommRingCat.{max c v r}) (R₁ : Sheaf J₁ CommRingCat.{max c v r})

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem model_inverse
    (F : Mod.{c, v, max c v r} J₀ R₀ ⥤ Mod.{c, v, max c v r} J₁ R₁)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (S₀ : Closed.{c, v, r} J₀ R₀) (S₁ : Closed.{c, v, r} J₁ R₁)
    (T₀ : Models.{c, v, r} J₀ R₀ S₀) (T₁ : Models.{c, v, r} J₁ R₁ S₁)
    (μ : S₀.tensor ⋙ F.mapDerivedCategory ≅
      (F.mapDerivedCategory.prod F.mapDerivedCategory) ⋙ S₁.tensor)
    (t : TensorComparisonModel.{c, v, r} J₀ J₁ R₀ R₁ F S₀ S₁ T₀ T₁ μ)
    (P Q : CochainComplex (Mod.{c, v, max c v r} J₀ R₀) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients)
    (fP : flatTerms.{c, v, r} J₀ R₀ P) (fQ : flatTerms.{c, v, r} J₀ R₀ Q) :
    μ.inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      F.mapDerivedCategory.map ((tensorModelIso.{c, v, r} J₀ R₀ S₀ T₀ P Q hP hQ).inv) ≫
      F.mapDerivedCategoryFactors.hom.app ((totalTensor.{c, v, r} J₀ R₀).obj (P, Q)) =
    S₁.tensor.map (Prod.mkHom (F.mapDerivedCategoryFactors.hom.app P)
        (F.mapDerivedCategoryFactors.hom.app Q)) ≫
      (tensorModelIso.{c, v, r} J₁ R₁ S₁ T₁ _ _
        (t.kflat P hP fP) (t.kflat Q hQ fQ)).inv ≫ DerivedCategory.Q.map (t.chain P Q) := by
  have h := t.derived P Q hP hQ fP fQ
  let a := tensorModelIso.{c, v, r} J₁ R₁ S₁ T₁ _ _
    (t.kflat P hP fP) (t.kflat Q hQ fQ)
  let b := S₁.tensor.mapIso
    ((F.mapDerivedCategoryFactors.app P).prod (F.mapDerivedCategoryFactors.app Q))
  have he := congrArg (fun f ↦ b.hom ≫ a.inv ≫ f) h
  simpa only [a, b, Category.assoc, Iso.inv_hom_id_assoc, Iso.prod_hom,
    Functor.mapIso_hom, Iso.app_hom, ← Functor.map_comp_assoc, prod_comp,
    Iso.hom_inv_id_app, ← prod_id, Functor.map_id, S₁.tensor.map_id, Category.id_comp] using he

end FlatPreservation

section FourModels
variable {C₀ C₁ C₂ C₃ : Type c}
  [Category.{v} C₀] [Category.{v} C₁] [Category.{v} C₂] [Category.{v} C₃]
  [EssentiallySmall.{max c v r} C₀] [EssentiallySmall.{max c v r} C₁]
  [EssentiallySmall.{max c v r} C₂] [EssentiallySmall.{max c v r} C₃]
  (J₀ : GrothendieckTopology C₀) (J₁ : GrothendieckTopology C₁)
  (J₂ : GrothendieckTopology C₂) (J₃ : GrothendieckTopology C₃)
  (R₀ : Sheaf J₀ CommRingCat.{max c v r}) (R₁ : Sheaf J₁ CommRingCat.{max c v r})
  (R₂ : Sheaf J₂ CommRingCat.{max c v r}) (R₃ : Sheaf J₃ CommRingCat.{max c v r})
  (F : Mod.{c, v, max c v r} J₀ R₀ ⥤ Mod.{c, v, max c v r} J₁ R₁)
  (G : Mod.{c, v, max c v r} J₁ R₁ ⥤ Mod.{c, v, max c v r} J₃ R₃)
  (H : Mod.{c, v, max c v r} J₀ R₀ ⥤ Mod.{c, v, max c v r} J₂ R₂)
  (I : Mod.{c, v, max c v r} J₂ R₂ ⥤ Mod.{c, v, max c v r} J₃ R₃)
  [F.Additive] [G.Additive] [H.Additive] [I.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits I] [PreservesFiniteColimits I]
  (S₀ : Closed.{c, v, r} J₀ R₀) (S₁ : Closed.{c, v, r} J₁ R₁)
  (S₂ : Closed.{c, v, r} J₂ R₂) (S₃ : Closed.{c, v, r} J₃ R₃)
  (T₀ : Models.{c, v, r} J₀ R₀ S₀) (T₁ : Models.{c, v, r} J₁ R₁ S₁)
  (T₂ : Models.{c, v, r} J₂ R₂ S₂) (T₃ : Models.{c, v, r} J₃ R₃ S₃)
  (μF : S₀.tensor ⋙ F.mapDerivedCategory ≅
    (F.mapDerivedCategory.prod F.mapDerivedCategory) ⋙ S₁.tensor)
  (μG : S₁.tensor ⋙ G.mapDerivedCategory ≅
    (G.mapDerivedCategory.prod G.mapDerivedCategory) ⋙ S₃.tensor)
  (μH : S₀.tensor ⋙ H.mapDerivedCategory ≅
    (H.mapDerivedCategory.prod H.mapDerivedCategory) ⋙ S₂.tensor)
  (μI : S₂.tensor ⋙ I.mapDerivedCategory ≅
    (I.mapDerivedCategory.prod I.mapDerivedCategory) ⋙ S₃.tensor)
  (tF : TensorComparisonModel.{c, v, r} J₀ J₁ R₀ R₁ F S₀ S₁ T₀ T₁ μF)
  (tG : TensorComparisonModel.{c, v, r} J₁ J₃ R₁ R₃ G S₁ S₃ T₁ T₃ μG)
  (tH : TensorComparisonModel.{c, v, r} J₀ J₂ R₀ R₂ H S₀ S₂ T₀ T₂ μH)
  (tI : TensorComparisonModel.{c, v, r} J₂ J₃ R₂ R₃ I S₂ S₃ T₂ T₃ μI)
  (θ : F ⋙ G ≅ H ⋙ I)
  (ho : ∀ M N,
    G.map (tF.ordinary M N).hom ≫ (tG.ordinary (F.obj M) (F.obj N)).hom ≫
      ordinaryTensorHom.{c, v, r} J₃ R₃ (θ.hom.app M) (θ.hom.app N) =
    θ.hom.app (ordinaryTensor.{c, v, r} J₀ R₀ M N) ≫
      I.map (tH.ordinary M N).hom ≫ (tI.ordinary (H.obj M) (H.obj N)).hom)

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
-- Keep this composite isomorphism intact during reassociation.
@[irreducible] private def twoFactors (P : CochainComplex (Mod.{c, v, max c v r} J₀ R₀) ℤ) :
    G.mapDerivedCategory.obj (F.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≅
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P)) :=
  G.mapDerivedCategory.mapIso (F.mapDerivedCategoryFactors.app P) ≪≫
    G.mapDerivedCategoryFactors.app ((F.mapHomologicalComplex (.up ℤ)).obj P)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem fourModels_factors
    (P : CochainComplex (Mod.{c, v, max c v r} J₀ R₀) ℤ) :
    (Functor.mapDerivedCategoryCompIso F G ≪≫
      Functor.mapDerivedCategoryNatIso θ ≪≫ (Functor.mapDerivedCategoryCompIso H I).symm).hom.app
        (DerivedCategory.Q.obj P) ≫ (twoFactors.{c, v, r} J₀ J₂ J₃ R₀ R₂ R₃ H I P).hom =
    (twoFactors.{c, v, r} J₀ J₁ J₃ R₀ R₁ R₃ F G P).hom ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex θ.hom (.up ℤ)).app P) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, twoFactors,
    Functor.mapIso_hom, Iso.app_hom, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors]
  rw [Functor.mapDerivedCategoryNatIso_fac]
  erw [← Functor.mapDerivedCategoryCompIso_hom_app_factors F G P]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem fourModels_composite
    (P Q : CochainComplex (Mod.{c, v, max c v r} J₀ R₀) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients)
    (fP : flatTerms.{c, v, r} J₀ R₀ P) (fQ : flatTerms.{c, v, r} J₀ R₀ Q) :
    μG.inv.app (F.mapDerivedCategory.obj (DerivedCategory.Q.obj P),
        F.mapDerivedCategory.obj (DerivedCategory.Q.obj Q)) ≫
      G.mapDerivedCategory.map (μF.inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategory.map
        ((tensorModelIso.{c, v, r} J₀ R₀ S₀ T₀ P Q hP hQ).inv)) ≫
      (twoFactors.{c, v, r} J₀ J₁ J₃ R₀ R₁ R₃ F G
        ((totalTensor.{c, v, r} J₀ R₀).obj (P, Q))).hom =
    S₃.tensor.map (Prod.mkHom
        (twoFactors.{c, v, r} J₀ J₁ J₃ R₀ R₁ R₃ F G P).hom
        (twoFactors.{c, v, r} J₀ J₁ J₃ R₀ R₁ R₃ F G Q).hom) ≫
      (tensorModelIso.{c, v, r} J₃ R₃ S₃ T₃ _ _
        (tG.kflat _ (tF.kflat P hP fP) (fun i ↦
          tensorComparisonModel_preserves_flat.{c, v, r} J₀ J₁ R₀ R₁ F S₀ S₁ T₀ T₁ μF tF
            _ (fP i)))
        (tG.kflat _ (tF.kflat Q hQ fQ) (fun i ↦
          tensorComparisonModel_preserves_flat.{c, v, r} J₀ J₁ R₀ R₁ F S₀ S₁ T₀ T₁ μF tF
            _ (fQ i)))).inv ≫
      DerivedCategory.Q.map (tG.chain ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q) ≫
        (G.mapHomologicalComplex (.up ℤ)).map (tF.chain P Q)) := by
  dsimp only [flatTerms] at fP fQ
  let FP := (F.mapHomologicalComplex (.up ℤ)).obj P
  let FQ := (F.mapHomologicalComplex (.up ℤ)).obj Q
  have ffP : flatTerms.{c, v, r} J₁ R₁ FP := fun i ↦
    tensorComparisonModel_preserves_flat.{c, v, r} J₀ J₁ R₀ R₁ F S₀ S₁ T₀ T₁ μF tF _ (fP i)
  have ffQ : flatTerms.{c, v, r} J₁ R₁ FQ := fun i ↦
    tensorComparisonModel_preserves_flat.{c, v, r} J₀ J₁ R₀ R₁ F S₀ S₁ T₀ T₁ μF tF _ (fQ i)
  have hF := model_inverse.{c, v, r} J₀ J₁ R₀ R₁ F S₀ S₁ T₀ T₁ μF tF P Q hP hQ fP fQ
  have hG := model_inverse.{c, v, r} J₁ J₃ R₁ R₃ G S₁ S₃ T₁ T₃ μG tG FP FQ
    (tF.kflat P hP fP) (tF.kflat Q hQ fQ) ffP ffQ
  have hn := μG.inv.naturality (Prod.mkHom (F.mapDerivedCategoryFactors.hom.app P)
    (F.mapDerivedCategoryFactors.hom.app Q))
  change S₃.tensor.map (Prod.mkHom
      (G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P))
      (G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app Q))) ≫
      μG.inv.app (DerivedCategory.Q.obj FP, DerivedCategory.Q.obj FQ) =
    μG.inv.app (F.mapDerivedCategory.obj (DerivedCategory.Q.obj P),
      F.mapDerivedCategory.obj (DerivedCategory.Q.obj Q)) ≫
      G.mapDerivedCategory.map (S₁.tensor.map
        (Prod.mkHom (F.mapDerivedCategoryFactors.hom.app P)
          (F.mapDerivedCategoryFactors.hom.app Q))) at hn
  simp only [twoFactors, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  rw [← G.mapDerivedCategory.map_comp_assoc, ← G.mapDerivedCategory.map_comp_assoc]
  simp only [Category.assoc]
  rw [hF]
  simp only [G.mapDerivedCategory.map_comp, Category.assoc]
  rw [← reassoc_of% hn]
  have hg := G.mapDerivedCategoryFactors.hom.naturality (tF.chain P Q)
  dsimp only [Functor.comp_map] at hg
  erw [hg]
  rw [reassoc_of% hG]
  simp only [← S₃.tensor.map_comp_assoc, prod_comp, Functor.map_comp]
  rfl

-- The four representative model equations involve four independent module categories.
include ho in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem fourModels_inverse_on_representatives
    (P Q : CochainComplex (Mod.{c, v, max c v r} J₀ R₀) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients)
    (fP : flatTerms.{c, v, r} J₀ R₀ P) (fQ : flatTerms.{c, v, r} J₀ R₀ Q) :
    let δ := Functor.mapDerivedCategorySquareIso θ
    S₃.tensor.map (Prod.mkHom (δ.hom.app (DerivedCategory.Q.obj P))
        (δ.hom.app (DerivedCategory.Q.obj Q))) ≫
      μI.inv.app (H.mapDerivedCategory.obj (DerivedCategory.Q.obj P),
        H.mapDerivedCategory.obj (DerivedCategory.Q.obj Q)) ≫
      I.mapDerivedCategory.map (μH.inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) =
    μG.inv.app (F.mapDerivedCategory.obj (DerivedCategory.Q.obj P),
        F.mapDerivedCategory.obj (DerivedCategory.Q.obj Q)) ≫
      G.mapDerivedCategory.map (μF.inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      δ.hom.app (S₀.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) := by
  dsimp only
  dsimp only [flatTerms] at fP fQ
  let δ := Functor.mapDerivedCategorySquareIso θ
  let d := NatTrans.mapHomologicalComplex θ.hom (.up ℤ)
  let FP := (F.mapHomologicalComplex (.up ℤ)).obj P
  let FQ := (F.mapHomologicalComplex (.up ℤ)).obj Q
  let HP := (H.mapHomologicalComplex (.up ℤ)).obj P
  let HQ := (H.mapHomologicalComplex (.up ℤ)).obj Q
  let GFP := (G.mapHomologicalComplex (.up ℤ)).obj FP
  let GFQ := (G.mapHomologicalComplex (.up ℤ)).obj FQ
  let IHP := (I.mapHomologicalComplex (.up ℤ)).obj HP
  let IHQ := (I.mapHomologicalComplex (.up ℤ)).obj HQ
  let Tot := (totalTensor.{c, v, r} J₀ R₀).obj (P, Q)
  let bFG := twoFactors.{c, v, r} J₀ J₁ J₃ R₀ R₁ R₃ F G
  let bHI := twoFactors.{c, v, r} J₀ J₂ J₃ R₀ R₂ R₃ H I
  let r₀ := tensorModelIso.{c, v, r} J₀ R₀ S₀ T₀ P Q hP hQ
  have ffP : flatTerms.{c, v, r} J₁ R₁ FP := fun i ↦
    tensorComparisonModel_preserves_flat.{c, v, r} J₀ J₁ R₀ R₁ F S₀ S₁ T₀ T₁ μF tF _ (fP i)
  have ffQ : flatTerms.{c, v, r} J₁ R₁ FQ := fun i ↦
    tensorComparisonModel_preserves_flat.{c, v, r} J₀ J₁ R₀ R₁ F S₀ S₁ T₀ T₁ μF tF _ (fQ i)
  have fhP : flatTerms.{c, v, r} J₂ R₂ HP := fun i ↦
    tensorComparisonModel_preserves_flat.{c, v, r} J₀ J₂ R₀ R₂ H S₀ S₂ T₀ T₂ μH tH _ (fP i)
  have fhQ : flatTerms.{c, v, r} J₂ R₂ HQ := fun i ↦
    tensorComparisonModel_preserves_flat.{c, v, r} J₀ J₂ R₀ R₂ H S₀ S₂ T₀ T₂ μH tH _ (fQ i)
  have hkGFP := tG.kflat FP (tF.kflat P hP fP) ffP
  have hkGFQ := tG.kflat FQ (tF.kflat Q hQ fQ) ffQ
  have hkIHP := tI.kflat HP (tH.kflat P hP fP) fhP
  have hkIHQ := tI.kflat HQ (tH.kflat Q hQ fQ) fhQ
  let rFG := tensorModelIso.{c, v, r} J₃ R₃ S₃ T₃ GFP GFQ hkGFP hkGFQ
  let rHI := tensorModelIso.{c, v, r} J₃ R₃ S₃ T₃ IHP IHQ hkIHP hkIHQ
  let cFG := tG.chain FP FQ ≫ (G.mapHomologicalComplex (.up ℤ)).map (tF.chain P Q)
  let cHI := tI.chain HP HQ ≫ (I.mapHomologicalComplex (.up ℤ)).map (tH.chain P Q)
  have hFG := fourModels_composite.{c, v, r} J₀ J₁ J₃ R₀ R₁ R₃ F G
    S₀ S₁ S₃ T₀ T₁ T₃ μF μG tF tG P Q hP hQ fP fQ
  have hHI := fourModels_composite.{c, v, r} J₀ J₂ J₃ R₀ R₂ R₃ H I
    S₀ S₂ S₃ T₀ T₂ T₃ μH μI tH tI P Q hP hQ fP fQ
  change _ = S₃.tensor.map (Prod.mkHom (bFG P).hom (bFG Q).hom) ≫
    rFG.inv ≫ DerivedCategory.Q.map cFG at hFG
  change _ = S₃.tensor.map (Prod.mkHom (bHI P).hom (bHI Q).hom) ≫
    rHI.inv ≫ DerivedCategory.Q.map cHI at hHI
  have hp := fourModels_factors.{c, v, r} J₀ J₁ J₂ J₃ R₀ R₁ R₂ R₃ F G H I θ P
  have hq := fourModels_factors.{c, v, r} J₀ J₁ J₂ J₃ R₀ R₁ R₂ R₃ F G H I θ Q
  have ht := fourModels_factors.{c, v, r} J₀ J₁ J₂ J₃ R₀ R₁ R₂ R₃ F G H I θ Tot
  have hn := tensorModelIso_naturality.{c, v, r} J₃ R₃ S₃ T₃ GFP IHP GFQ IHQ
    hkGFP hkIHP hkGFQ hkIHQ (d.app P) (d.app Q)
  change DerivedCategory.Q.map ((totalTensor.{c, v, r} J₃ R₃).map
      (Prod.mkHom (d.app P) (d.app Q))) ≫ rHI.hom =
    rFG.hom ≫ S₃.tensor.map (Prod.mkHom (DerivedCategory.Q.map (d.app P))
      (DerivedCategory.Q.map (d.app Q))) at hn
  have hinv := congrArg (fun f ↦ rFG.inv ≫ f ≫ rHI.inv) hn
  simp only [Category.assoc, Iso.hom_inv_id, Iso.inv_hom_id_assoc,
    Category.comp_id] at hinv
  have hc := tensorComparisonCochainSquare.{c, v, r} J₀ J₁ J₂ J₃ R₀ R₁ R₂ R₃ F G H I
    S₀ S₁ S₂ S₃ T₀ T₁ T₂ T₃ μF μG μH μI tF tG tH tI θ ho P Q
  change cFG ≫ d.app Tot =
    (totalTensor.{c, v, r} J₃ R₃).map (Prod.mkHom (d.app P) (d.app Q)) ≫ cHI at hc
  let z := I.mapDerivedCategory.mapIso (H.mapDerivedCategory.mapIso r₀.symm) ≪≫ bHI Tot
  apply (cancel_mono z.hom).1
  simp only [z, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  have hδ := δ.hom.naturality r₀.inv
  change G.mapDerivedCategory.map (F.mapDerivedCategory.map r₀.inv) ≫
      δ.hom.app (DerivedCategory.Q.obj Tot) =
    δ.hom.app (S₀.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      I.mapDerivedCategory.map (H.mapDerivedCategory.map r₀.inv) at hδ
  erw [← reassoc_of% hδ]
  erw [ht]
  erw [reassoc_of% hFG]
  erw [hHI]
  rw [← S₃.tensor.map_comp_assoc]
  simp only [prod_comp]
  erw [hp, hq]
  erw [← prod_comp (Prod.mkHom (bFG P).hom (bFG Q).hom)
    (Prod.mkHom (DerivedCategory.Q.map (d.app P)) (DerivedCategory.Q.map (d.app Q))),
    S₃.tensor.map_comp]
  simp only [Category.assoc]
  erw [← reassoc_of% hinv]
  simp only [← DerivedCategory.Q.map_comp, ← Category.assoc]
  erw [← hc]

include ho in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem fourModels_square
    (M N : D.{c, v, max c v r} J₀ R₀) :
    let δ := Functor.mapDerivedCategorySquareIso θ
    G.mapDerivedCategory.map (μF.hom.app (M, N)) ≫
      μG.hom.app (F.mapDerivedCategory.obj M, F.mapDerivedCategory.obj N) ≫
      S₃.tensor.map (Prod.mkHom (δ.hom.app M) (δ.hom.app N)) =
    δ.hom.app (S₀.tensor.obj (M, N)) ≫
      I.mapDerivedCategory.map (μH.hom.app (M, N)) ≫
      μI.hom.app (H.mapDerivedCategory.obj M, H.mapDerivedCategory.obj N) := by
  let δ := Functor.mapDerivedCategorySquareIso θ
  change G.mapDerivedCategory.map (μF.hom.app (M, N)) ≫
      μG.hom.app (F.mapDerivedCategory.obj M, F.mapDerivedCategory.obj N) ≫
      S₃.tensor.map (Prod.mkHom (δ.hom.app M) (δ.hom.app N)) =
    δ.hom.app (S₀.tensor.obj (M, N)) ≫
      I.mapDerivedCategory.map (μH.hom.app (M, N)) ≫
      μI.hom.app (H.mapDerivedCategory.obj M, H.mapDerivedCategory.obj N)
  let U : (F.mapDerivedCategory.prod F.mapDerivedCategory) ⋙
      (G.mapDerivedCategory.prod G.mapDerivedCategory) ⋙ S₃.tensor ⟶
        S₀.tensor ⋙ H.mapDerivedCategory ⋙ I.mapDerivedCategory :=
    Functor.whiskerRight (δ.hom.prod δ.hom) S₃.tensor ≫
      Functor.whiskerLeft (H.mapDerivedCategory.prod H.mapDerivedCategory) μI.inv ≫
      Functor.whiskerRight μH.inv I.mapDerivedCategory
  let V : (F.mapDerivedCategory.prod F.mapDerivedCategory) ⋙
      (G.mapDerivedCategory.prod G.mapDerivedCategory) ⋙ S₃.tensor ⟶
        S₀.tensor ⋙ H.mapDerivedCategory ⋙ I.mapDerivedCategory :=
    Functor.whiskerLeft (F.mapDerivedCategory.prod F.mapDerivedCategory) μG.inv ≫
      Functor.whiskerRight μF.inv G.mapDerivedCategory ≫
      Functor.whiskerLeft S₀.tensor δ.hom
  have he : U = V := by
    obtain ⟨_, _, _, h⟩ := SheafOfModules.cochain_tensor_model_rigidity J₀ R₀
    apply (h (D.{c, v, max c v r} J₃ R₃) inferInstance _ _).1
    apply NatTrans.ext
    funext X
    rcases X with ⟨P, Q⟩
    exact fourModels_inverse_on_representatives.{c, v, r}
      J₀ J₁ J₂ J₃ R₀ R₁ R₂ R₃ F G H I S₀ S₁ S₂ S₃ T₀ T₁ T₂ T₃
      μF μG μH μI tF tG tH tI θ ho
      P.obj Q.obj P.property.1 Q.property.1 P.property.2 Q.property.2
  have hi := congrArg (fun t ↦ t.app (M, N)) he
  change S₃.tensor.map (Prod.mkHom (δ.hom.app M) (δ.hom.app N)) ≫
      μI.inv.app (H.mapDerivedCategory.obj M, H.mapDerivedCategory.obj N) ≫
      I.mapDerivedCategory.map (μH.inv.app (M, N)) =
    μG.inv.app (F.mapDerivedCategory.obj M, F.mapDerivedCategory.obj N) ≫
      G.mapDerivedCategory.map (μF.inv.app (M, N)) ≫
      δ.hom.app (S₀.tensor.obj (M, N)) at hi
  let u := G.mapDerivedCategory.mapIso (μF.app (M, N)) ≪≫
    μG.app (F.mapDerivedCategory.obj M, F.mapDerivedCategory.obj N)
  let w := I.mapDerivedCategory.mapIso (μH.app (M, N)) ≪≫
    μI.app (H.mapDerivedCategory.obj M, H.mapDerivedCategory.obj N)
  have hi' : S₃.tensor.map (Prod.mkHom (δ.hom.app M) (δ.hom.app N)) ≫ w.inv =
      u.inv ≫ δ.hom.app (S₀.tensor.obj (M, N)) := by
    simpa only [u, w, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc]
      using hi
  have hf : u.hom ≫ S₃.tensor.map (Prod.mkHom (δ.hom.app M) (δ.hom.app N)) =
      δ.hom.app (S₀.tensor.obj (M, N)) ≫ w.hom := by
    apply (Iso.comp_inv_eq w).1
    rw [Category.assoc, hi', Iso.hom_inv_id_assoc]
  exact (Category.assoc (G.mapDerivedCategory.map (μF.hom.app (M, N)))
    (μG.hom.app (F.mapDerivedCategory.obj M, F.mapDerivedCategory.obj N))
    (S₃.tensor.map (Prod.mkHom (δ.hom.app M) (δ.hom.app N)))).symm.trans hf

end FourModels

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)
  {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C')
  (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
  (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
  (adjSet : uInv ⊣ uPush)

variable (A : Data.{c, v, r} J B τ)
  (O : GeometryOrdinary.{c, v, r} J B τ J' uInv uPush adjSet)
  (target : Data.{c, v, r} J' O.coefficients O.coefficientTransition)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The ordinary evaluation square implies the derived evaluation square.
Source: Zheng Construction 4.1; Stacks 06YU and 07A4.
(blueprint: lem-coef-semilinear-geometric-tensor-evaluation).

Proof: each comparison model preserves flat modules, by applying its K-flat
preservation to a single flat module and using the converse single-complex criterion.
Restrict both natural transformations to pairs of flat-term K-flat system complexes.
The summand formulas for the four tensor models identify the two chain
maps: on the (p,q) summand this is precisely the given ordinary evaluation square,
with the inverse comparisons. Additivity preserves the sign on the second
differential. Apply localization and substitute the four representative equations.
Naturality of the exact-functor factorization isomorphisms identifies the remaining
factors with geometryPullEvaluation, which was defined by deriving the ordinary
comparison. Cancel the tensor-model and exact-factorization isomorphisms. Finally,
restriction to pairs of resolving representatives is faithful, by cochain tensor
model rigidity, so equality holds for arbitrary derived inputs. No derived evaluation
functor is assumed to be faithful. -/
theorem geometricTensorEvaluation [PreservesFiniteLimits uInv]
    (tensorPullback : A.closed.tensor ⋙ O.pull.mapDerivedCategory ≅
    (O.pull.mapDerivedCategory.prod O.pull.mapDerivedCategory) ⋙ target.closed.tensor)
    (levelTensorPullback : ∀ n : ℕ,
    (A.levelClosed n).tensor ⋙
        derivedExact.{c, v, max c v r, c, v} J J' (B n)
          (O.coefficients n) (O.inverseImage n).modules ≅
      ((derivedExact.{c, v, max c v r, c, v} J J' (B n)
          (O.coefficients n) (O.inverseImage n).modules).prod
        (derivedExact.{c, v, max c v r, c, v} J J' (B n)
          (O.coefficients n) (O.inverseImage n).modules)) ⋙ (target.levelClosed n).tensor)
    (levelTensorModel : ∀ n : ℕ,
    TensorComparisonModel.{c, v, r} J J' (B n) (O.coefficients n) (O.inverseImage n).modules
      (A.levelClosed n) (target.levelClosed n) (A.levelTensorModels n)
        (target.levelTensorModels n) (levelTensorPullback n))
    (tensorModel : TensorComparisonModel.{c, v, r} (coefficientSequenceTopology J)
    (coefficientSequenceTopology J') (systemRing.{c, v, max c v r} J B τ)
      (systemRing.{c, v, max c v r} J' O.coefficients O.coefficientTransition) O.pull A.closed
        target.closed
        A.tensorModels target.tensorModels tensorPullback)
    (tensor_ordinary_evaluation : ∀ (n : ℕ) (M N : Systems.{c, v, max c v r} J B τ),
    (evaluation.{c, v, max c v r} J' O.coefficients O.coefficientTransition n).map
      (tensorModel.ordinary M N).hom ≫
      (ordinaryEvaluationTensor.{c, v, r} J' O.coefficients O.coefficientTransition n (O.pull.obj M)
        (O.pull.obj N)).hom ≫
      ordinaryTensorHom.{c, v, r} J' (O.coefficients n)
        ((O.ordinaryPullEvaluation n).hom.app M) ((O.ordinaryPullEvaluation n).hom.app N) =
      (O.ordinaryPullEvaluation n).hom.app
        (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J
          B τ) M N) ≫
      (O.inverseImage n).modules.map (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).hom ≫
      ((levelTensorModel n).ordinary ((evaluation.{c, v, max c v r} J B τ n).obj M)
        ((evaluation.{c, v, max c v r} J B τ n).obj N)).hom)
    : ∀ (n : ℕ) (M P : DS.{c, v, max c v r} J B τ),
    (e.{c, v, max c v r} J' O.coefficients O.coefficientTransition n).map
        (tensorPullback.hom.app (M, P)) ≫
        (target.tensorEvaluation n).hom.app
          (O.pull.mapDerivedCategory.obj M, O.pull.mapDerivedCategory.obj P) ≫
        (target.levelClosed n).tensor.map
          (Prod.mkHom (((geometryPullEvaluation J B τ J' uInv uPush adjSet O) n).hom.app M)
            (((geometryPullEvaluation J B τ J' uInv uPush adjSet O) n).hom.app P)) =
      ((geometryPullEvaluation J B τ J' uInv uPush adjSet O) n).hom.app (A.closed.tensor.obj (M, P))
        ≫
        (derivedExact.{c, v, max c v r, c, v} J J' (B n)
          (O.coefficients n) (O.inverseImage n).modules).map
            ((A.tensorEvaluation n).hom.app (M, P)) ≫
        (levelTensorPullback n).hom.app
          ((e.{c, v, max c v r} J B τ n).obj M, (e.{c, v, max c v r} J B τ n).obj P) := by
  intro n M P
  apply fourModels_square.{c, v, r}
    (coefficientSequenceTopology J) (coefficientSequenceTopology J') J J'
    (systemRing.{c, v, max c v r} J B τ)
    (systemRing.{c, v, max c v r} J' O.coefficients O.coefficientTransition)
    (B n) (O.coefficients n) O.pull
    (evaluation.{c, v, max c v r} J' O.coefficients O.coefficientTransition n)
    (evaluation.{c, v, max c v r} J B τ n) (O.inverseImage n).modules
    A.closed target.closed (A.levelClosed n) (target.levelClosed n)
    A.tensorModels target.tensorModels (A.levelTensorModels n) (target.levelTensorModels n)
    tensorPullback (target.tensorEvaluation n) (A.tensorEvaluation n) (levelTensorPullback n)
    tensorModel (target.tensorEvaluationModel n) (A.tensorEvaluationModel n)
    (levelTensorModel n) (O.ordinaryPullEvaluation n) _ M P
  intro X Y
  simpa only [A.tensorEvaluationModel_ordinary, target.tensorEvaluationModel_ordinary] using
    tensor_ordinary_evaluation n X Y

end WeilConjectures.SemilinearSections
