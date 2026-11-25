/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.Homology.Localization
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Logic.Small.Defs
import all Mathlib.Algebra.Homology.Localization
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Logic.Small.Defs
import all WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility

/-!
# Bounded acyclic flat models for the proper coefficient map

Source: Stacks Project, `literature/stacks-project/more-etale.tex`, Tag 0GL6,
remark-Rf-lower-shriek-change-of-rings (blueprint:
lem-sp-acyclic-flat-proper-coefficient-model).

The scalar extension, its pullback comparison, and the coefficient mate are the
canonical constructions already provided by the étale six-functor interface.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/- The three names below expose the canonical objects named in the statement. -/

/-- The derived tensor `T_T = - ⊗ᴸ_{A_T} B_T` used in the coefficient comparison.
Source: Stacks Project, Tag 0GL6 (blueprint:
`lem-sp-acyclic-flat-proper-coefficient-model`). -/
abbrev properCoefficientTensor {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    DerivedCategoryModule A T ⥤ DerivedCategoryModule B T :=
  scalarExtension φ T

/-- The canonical tensor/pullback comparison `λ : T_W r_A^* ≅ r_B^* T_V` for the
coefficient extension; `scalarPullbackIso` is its inverse, used in the transpose below.
Source: Stacks Project, Tag 0GL6 (blueprint:
`lem-sp-acyclic-flat-proper-coefficient-model`). -/
abbrev properCoefficientPullbackComparison {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W V : Scheme.{u}} (r : W ⟶ V) :=
  (scalarPullbackIso φ r).symm

/-- The canonical coefficient map `q_r`, defined as the adjoint mate of the
scalar-extended counit through the comparison above.
Source: Stacks Project, Tag 0GL6 (blueprint:
`lem-sp-acyclic-flat-proper-coefficient-model`). -/
abbrev properCoefficientMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W V : Scheme.{u}} (r : W ⟶ V) :=
  scalarMate φ r

/-- The termwise scalar extension `C_B` of a cochain complex on `W`.
Source: Stacks 0GL6 (blueprint: lem-sp-acyclic-flat-proper-coefficient-model). -/
abbrev coefficientExtendedComplex {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (W : Scheme.{u})
    (C : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ :=
  ((ProEtale.etaleSheafExtendScalars φ W).mapHomologicalComplex (.up ℤ)).obj C

/-- The canonical acyclic-complex comparison, including the homotopy quotient factor.
Source: Stacks 015E (blueprint: lem-sp-acyclic-flat-proper-coefficient-model). -/
def properAcyclicComparison
    (A : Type (u + 1)) [CommRing A] {W V : Scheme.{u}} (r : W ⟶ V)
    (C : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    DerivedCategory.Q.obj
        (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C) ⟶
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) r).obj (DerivedCategory.Q.obj C) :=
  (DerivedCategory.quotientCompQhIso _).inv.app
      (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C) ≫
    DerivedCategory.Qh.map
      (((lowerStar (ModuleCat.{u + 1} A) r).mapHomotopyCategoryFactors (.up ℤ)).inv.app C) ≫
    (lowerStar (ModuleCat.{u + 1} A) r).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj C) ≫
    (rightDerivedLowerStar (ModuleCat.{u + 1} A) r).map
      ((DerivedCategory.quotientCompQhIso _).hom.app C)

/-- The ordinary B-linear projection map: the mate of scalar extension of the A-counit
through the ordinary scalar/pullback isomorphism. Its degreewise adjunct is precisely
pullback/tensor reassociation followed by counit tensor identity.
Source: Stacks 0GL6, 07A4 (blueprint: lem-sp-acyclic-flat-proper-coefficient-model). -/
def properSheafCoefficientMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W V : Scheme.{u}} (r : W ⟶ V) :
    lowerStar (ModuleCat.{u + 1} A) r ⋙ ProEtale.etaleSheafExtendScalars φ V ⟶
      ProEtale.etaleSheafExtendScalars φ W ⋙ lowerStar (ModuleCat.{u + 1} B) r :=
  (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r)
    (TwoSquare.mk _ _ _ _ (scalarSheafPullbackIso φ r).hom))

/-- The termwise projection chain map pi_C. Mapping the ordinary natural transformation
on complexes guarantees that its components commute with the differentials.
Source: Stacks 0GL6, 015E (blueprint: lem-sp-acyclic-flat-proper-coefficient-model). -/
def properCoefficientComplexMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W V : Scheme.{u}} (r : W ⟶ V)
    (C : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    coefficientExtendedComplex φ V
        (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C) ⟶
      ((lowerStar (ModuleCat.{u + 1} B) r).mapHomologicalComplex (.up ℤ)).obj
        (coefficientExtendedComplex φ W C) :=
  (Functor.mapHomologicalComplexCompIso
      (Iso.refl (lowerStar (ModuleCat.{u + 1} A) r ⋙
        ProEtale.etaleSheafExtendScalars φ V)) (.up ℤ)).hom.app C ≫
    (NatTrans.mapHomologicalComplex (properSheafCoefficientMap φ r) (.up ℤ)).app C ≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (ProEtale.etaleSheafExtendScalars φ W ⋙
        lowerStar (ModuleCat.{u + 1} B) r)) (.up ℤ)).inv.app C

section ProofCalculations

section CachedInstances
variable (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
private abbrev cachedPreadditive :
    MonoidalPreadditive (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) := inferInstance
private abbrev cachedCoproducts :
    HasCountableCoproducts (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) := inferInstance
private abbrev cachedColimits :
    HasColimitsOfShape ℤ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) := inferInstance
private abbrev cachedFlatResolution : Abelian.HasFunctorialFlatResolution
    (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) := inferInstance
private abbrev cachedInjectiveResolution : Abelian.HasKInjectiveResolutions
    (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) := inferInstance
private abbrev cachedExactColimits :
    HasExactColimitsOfShape ℤ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) := inferInstance
private abbrev cachedTensor4 : ∀ (X₁ X₂ X₃ X₄ :
    GradedObject ℤ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))),
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := inferInstance
private abbrev cachedTensor12 : ∀ (X₁ X₂ X₃ :
    GradedObject ℤ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))),
    GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := inferInstance
private abbrev cachedTensor23 : ∀ (X₁ X₂ X₃ :
    GradedObject ℤ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))),
    GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := inferInstance
private abbrev cachedTensorLeft : ∀ (X : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)),
    PreservesColimitsOfShape ℤ
      ((MonoidalCategory.curriedTensor (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).obj X) :=
  inferInstance
private abbrev cachedTensorRight : ∀ (X : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)),
    PreservesColimitsOfShape ℤ
      ((MonoidalCategory.curriedTensor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).flip.obj X) :=
  inferInstance
end CachedInstances
attribute [local instance] cachedPreadditive cachedCoproducts cachedColimits
  cachedFlatResolution cachedInjectiveResolution cachedExactColimits cachedTensor4
  cachedTensor12 cachedTensor23 cachedTensorLeft cachedTensorRight

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  derivedTensor upperStar lowerStar

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def acyclicComparisonTransformation
    {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
    [HasDerivedCategory D] [HasDerivedCategory E] [Abelian.HasKInjectiveResolutions D]
    (F : D ⥤ E) [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
  Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso E).inv ≫
    Functor.whiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).inv DerivedCategory.Qh ≫
    Functor.whiskerLeft (HomotopyCategory.quotient D (.up ℤ)) F.rightDerivedFunctorUnit ≫
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso D).hom F.rightDerivedFunctor

private def leftComparisonTransformation
    {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
    [HasDerivedCategory D] [HasDerivedCategory E]
    (F : D ⥤ E) [F.Additive] {L : DerivedCategory D ⥤ DerivedCategory E}
    (α : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :
    DerivedCategory.Q ⋙ L ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso D).inv L ≫
    Functor.whiskerLeft (HomotopyCategory.quotient _ (.up ℤ)) α ≫
    Functor.whiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).hom DerivedCategory.Qh ≫
    Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso E).hom

section DerivedComparison
variable {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
  [MonoidalCategory D] [MonoidalPreadditive D] [HasCountableCoproducts D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ D] [HasExactColimitsOfShape ℤ D]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor D).obj X)]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor D).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D] [HasDerivedCategory D] [HasDerivedCategory E]
  [Abelian.HasKInjectiveResolutions E]
  {F : D ⥤ E} {G : E ⥤ D} [F.Additive] [G.Additive] [F.PreservesKFlatQuasiIso]

private lemma derived_counit_normalization (adj : F ⊣ G) (C : CochainComplex E ℤ) :
    F.leftDerivedFunctor.map ((acyclicComparisonTransformation G).app C) ≫
        adj.derivedAdjunction.counit.app (DerivedCategory.Q.obj C) =
      (leftComparisonTransformation F F.leftDerivedFunctorCounit).app
          ((G.mapHomologicalComplex (.up ℤ)).obj C) ≫
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).counit.app C) := by
  have h := (adj.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso _ (.up ℤ)) F.leftDerivedFunctorCounit
    G.rightDerivedFunctorUnit ((HomotopyCategory.quotient _ (.up ℤ)).obj C)
  rw [Adjunction.mapHomotopyCategory_counit_app_quotient] at h
  dsimp only [acyclicComparisonTransformation, leftComparisonTransformation,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_hom, Quotient.lift.isLift_inv,
    DerivedCategory.quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso]
  repeat' first
    | erw [CategoryTheory.Functor.map_id]
    | erw [Category.id_comp]
    | erw [Category.comp_id]
  exact h

private lemma derived_unit_normalization (adj : F ⊣ G) (C : CochainComplex D ℤ) :
    adj.derivedAdjunction.unit.app (DerivedCategory.Q.obj C) ≫
        G.rightDerivedFunctor.map
          ((leftComparisonTransformation F F.leftDerivedFunctorCounit).app C) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app C) ≫
        (acyclicComparisonTransformation G).app
          ((F.mapHomologicalComplex (.up ℤ)).obj C) := by
  have h := (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso _ (.up ℤ)) F.leftDerivedFunctorCounit
    G.rightDerivedFunctorUnit ((HomotopyCategory.quotient _ (.up ℤ)).obj C)
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient] at h
  dsimp only [acyclicComparisonTransformation, leftComparisonTransformation,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_hom, Quotient.lift.isLift_inv,
    DerivedCategory.quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso]
  repeat' first
    | erw [CategoryTheory.Functor.map_id]
    | erw [Category.id_comp]
    | erw [Category.comp_id]
  exact h
end DerivedComparison

private def transposeTransformation
    {C D H : Type*} [Category C] [Category D] [Category H]
    {L : D ⥤ H} {R : H ⥤ D} (adj : L ⊣ R)
    {F : C ⥤ D} {G : C ⥤ H} (η : F ⟶ G ⋙ R) : F ⋙ L ⟶ G where
  app X := (adj.homEquiv _ _).symm (η.app X)
  naturality X Y h := adj.homEquiv_naturality_right_square
    (F.map h) (η.app Y) (η.app X) (G.map h) (η.naturality h)

private def ordinaryScalarRepresentative
    {D E H K : Type*} [Category D] [Category E] [Category H] [Category K]
    [Preadditive D] [Preadditive E] {F : D ⥤ E} {G : E ⥤ D}
    [F.Additive] [G.Additive] (adj : F ⊣ G)
    (Q : CochainComplex D ℤ ⥤ H) (Q' : CochainComplex E ℤ ⥤ K)
    {L : H ⥤ K} {R : K ⥤ H} (ad : L ⊣ R)
    (e : Q' ⋙ R ≅ G.mapHomologicalComplex (.up ℤ) ⋙ Q) :
    Q ⋙ L ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ Q' :=
  transposeTransformation ad
    (Functor.whiskerRight
      ((Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv ≫
        NatTrans.mapHomologicalComplex adj.unit (.up ℤ) ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv) Q ≫
      Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ)) e.inv)

private def complexLocalization
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ ⥤
      DerivedCategoryModule A T :=
  DerivedCategory.Q

private def scalarRepresentativeTransformation
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    complexLocalization A T ⋙ scalarExtension φ T ⟶
      (ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ) ⋙
        complexLocalization B T :=
  ordinaryScalarRepresentative (ProEtale.etaleSheafExtendScalarsAdjunction φ T)
    (complexLocalization A T) (complexLocalization B T)
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ))
    (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryFactors

private def complexTransformation
    {C₁ C₂ C₃ C₄ : Type*}
    [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    [Preadditive C₁] [Preadditive C₂] [Preadditive C₃] [Preadditive C₄]
    (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₄) (H : C₁ ⥤ C₃) (I : C₃ ⥤ C₄)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    (τ : F ⋙ G ⟶ H ⋙ I) :
    F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ) ⟶
      H.mapHomologicalComplex (.up ℤ) ⋙ I.mapHomologicalComplex (.up ℤ) :=
  (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom ≫
    NatTrans.mapHomologicalComplex τ (.up ℤ) ≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (H ⋙ I)) (.up ℤ)).inv

private lemma mate_component
    {D₁ D₂ D₃ D₄ : Type*}
    [Category D₁] [Category D₂] [Category D₃] [Category D₄]
    {G₁ : D₁ ⥤ D₂} {F₁ : D₂ ⥤ D₁} {G₂ : D₃ ⥤ D₄} {F₂ : D₄ ⥤ D₃}
    {H₁ : D₁ ⥤ D₃} {H₂ : D₂ ⥤ D₄}
    (ad₁ : G₁ ⊣ F₁) (ad₂ : G₂ ⊣ F₂)
    (θ : TwoSquare H₁ G₁ G₂ H₂) (X : D₂) :
    (mateEquiv ad₁ ad₂ θ).app X =
      ad₂.unit.app (H₁.obj (F₁.obj X)) ≫
        F₂.map (θ.app (F₁.obj X) ≫ H₂.map (ad₁.counit.app X)) := by
  simp only [CategoryTheory.Functor.map_comp]
  simp [mateEquiv_apply]

private theorem mate_comparison
    {D₁ D₂ D₃ D₄ : Type*}
    [Category D₁] [Category D₂] [Category D₃] [Category D₄]
    {G₁ : D₁ ⥤ D₂} {F₁ : D₂ ⥤ D₁} {G₂ : D₃ ⥤ D₄} {F₂ : D₄ ⥤ D₃}
    {H₁ : D₁ ⥤ D₃} {H₂ : D₂ ⥤ D₄}
    (ad₁ : G₁ ⊣ F₁) (ad₂ : G₂ ⊣ F₂)
    (θ : TwoSquare H₁ G₁ G₂ H₂)
    {X U : D₂} {P : D₁} {Y N T : D₃} {J U' Z : D₄}
    (p : P ⟶ F₁.obj X) (q : T ⟶ F₂.obj Z)
    (s : H₁.obj P ⟶ Y) (t : H₂.obj X ⟶ Z)
    (a₁ : G₁.obj P ⟶ U) (a₂ : G₂.obj Y ⟶ J)
    (v : H₂.obj U ⟶ U') (b₂ : N ⟶ F₂.obj J)
    (c : U ⟶ X) (i : Y ⟶ N) (z : J ⟶ U') (c' : U' ⟶ Z)
    (k : N ⟶ T) (n : Y ⟶ T)
    (hc : G₁.map p ≫ ad₁.counit.app X = a₁ ≫ c)
    (hu : ad₂.unit.app Y ≫ F₂.map a₂ = i ≫ b₂)
    (hθ : θ.app P ≫ H₂.map a₁ ≫ v = G₂.map s ≫ a₂ ≫ z)
    (h₄ : H₂.map c ≫ t = v ≫ c')
    (h₇ : k ≫ q = b₂ ≫ F₂.map (z ≫ c'))
    (hn : i ≫ k = n) :
    H₁.map p ≫ (mateEquiv ad₁ ad₂ θ).app X ≫ F₂.map t =
      s ≫ n ≫ q := by
  have hmate : (mateEquiv ad₁ ad₂ θ).app X =
      ad₂.unit.app (H₁.obj (F₁.obj X)) ≫
        F₂.map (θ.app (F₁.obj X)) ≫
        F₂.map (H₂.map (ad₁.counit.app X)) := by
    simp [mateEquiv_apply]
  have h₁ := ad₂.unit.naturality (H₁.map p)
  have h₂ := θ.naturality p
  have h₅ := ad₂.unit.naturality s
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map]
    at h₁ h₂ h₅
  rw [hmate]
  simp only [Category.assoc]
  rw [reassoc_of% h₁]
  simp only [← CategoryTheory.Functor.map_comp]
  rw [reassoc_of% h₂, ← CategoryTheory.Functor.map_comp_assoc H₂, hc,
    CategoryTheory.Functor.map_comp_assoc, h₄, reassoc_of% hθ]
  simp only [CategoryTheory.Functor.map_comp]
  rw [← reassoc_of% h₅, reassoc_of% hu]
  simp only [CategoryTheory.Functor.map_comp] at h₇ ⊢
  rw [← h₇]
  simpa only [Category.assoc] using congrArg (fun f ↦ s ≫ f ≫ q) hn

private theorem scalar_preservesKFlatQuasiIso
    {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (T : Scheme.{u}) :
    (ProEtale.etaleSheafExtendScalars φ T).PreservesKFlatQuasiIso := by
  exact ProEtale.scalarExtension_preservesKFlat T.smallEtaleTopology φ

section ScalarRepresentativeComparison
variable {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
  [MonoidalCategory D] [MonoidalPreadditive D] [HasCountableCoproducts D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ D] [HasExactColimitsOfShape ℤ D]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor D).obj X)]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor D).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D] [HasDerivedCategory D] [HasDerivedCategory E]
  [Abelian.HasKInjectiveResolutions E]
  {F : D ⥤ E} {G : E ⥤ D} [F.Additive] [G.Additive] [F.PreservesKFlatQuasiIso]

private lemma ordinaryScalarRepresentative_isIso
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : F ⊣ G) {L : DerivedCategory D ⥤ DerivedCategory E}
    (b : L ⊣ G.mapDerivedCategory) (P : CochainComplex D ℤ)
    (hP : (HomologicalComplex.quasiIso D (.up ℤ)).kFlat P) :
    IsIso ((b.homEquiv _ _).symm
      (DerivedCategory.Q.map ((Functor.mapHomologicalComplexIdIso D (.up ℤ)).inv.app P ≫
        (NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app P ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app P) ≫
        G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj P))) := by
  change IsIso ((ordinaryScalarRepresentative adj DerivedCategory.Q DerivedCategory.Q b
    G.mapDerivedCategoryFactors).app P)
  let c := adj.derivedAdjunction.ofNatIsoRight G.rightDerivedFunctorIsoMapDerivedCategory
  let e := Adjunction.leftAdjointUniq b c
  let ε : F.leftDerivedFunctor.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P) :=
    F.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  have hunit : c.unit.app (DerivedCategory.Q.obj P) ≫ G.mapDerivedCategory.map ε =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
    have h : c.unit.app (DerivedCategory.Q.obj P) ≫ G.mapDerivedCategory.map ε ≫
        G.mapDerivedCategoryFactorsh.hom.app
          ((F.mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient D (.up ℤ)).obj P)) =
        DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app
          ((HomotopyCategory.quotient D (.up ℤ)).obj P)) :=
      ProEtale.derived_adjunction_unit_normalization adj
        ((HomotopyCategory.quotient D (.up ℤ)).obj P)
    rw [Adjunction.mapHomotopyCategory_unit_app_quotient] at h
    change c.unit.app (DerivedCategory.Q.obj P) ≫ G.mapDerivedCategory.map ε ≫
        G.mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient E (.up ℤ)).obj
            ((F.mapHomologicalComplex (.up ℤ)).obj P)) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) at h
    have he := G.mapDerivedCategoryFactorsh_hom_app
      ((F.mapHomologicalComplex (.up ℤ)).obj P)
    simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
      DerivedCategory.quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso,
      Quotient.lift.isLift_hom] at he
    erw [CategoryTheory.Functor.map_id, Category.id_comp,
      CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id] at he
    have heq : G.mapDerivedCategoryFactorsh.app
        ((HomotopyCategory.quotient E (.up ℤ)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj P)) =
        G.mapDerivedCategoryFactors.app ((F.mapHomologicalComplex (.up ℤ)).obj P) :=
      Iso.ext he
    have hi : G.mapDerivedCategoryFactorsh.inv.app
        ((HomotopyCategory.quotient E (.up ℤ)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj P)) =
        G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj P) :=
      congrArg Iso.inv heq
    rw [← hi]
    apply (Iso.eq_comp_inv (G.mapDerivedCategoryFactorsh.app
      ((HomotopyCategory.quotient E (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P)))).2
    simpa only [Category.assoc, Iso.app_hom] using h
  have hrepr : (ordinaryScalarRepresentative adj DerivedCategory.Q DerivedCategory.Q b
      G.mapDerivedCategoryFactors).app P =
      e.hom.app (DerivedCategory.Q.obj P) ≫ ε := by
    apply (b.homEquiv _ _).injective
    rw [b.homEquiv_naturality_right,
      Adjunction.homEquiv_leftAdjointUniq_hom_app]
    rw [hunit]
    change (b.homEquiv _ _)
      ((b.homEquiv _ _).symm _) = _
    rw [Equiv.apply_symm_apply]
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    apply congrArg (fun t ↦ DerivedCategory.Q.map t ≫
      G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj P))
    ext n
    simp only [Functor.id_obj, Functor.comp_obj, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplexIdIso_inv_app_f, NatTrans.mapHomologicalComplex_app_f,
      Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.refl_inv, NatTrans.id_app,
      Category.id_comp, Adjunction.mapHomologicalComplex_unit_app_f]
    exact Category.comp_id _
  rw [hrepr]
  have : IsIso ε := F.isIso_leftDerivedFunctorCounit_app_of_kFlat P hP
  infer_instance

end ScalarRepresentativeComparison

attribute [local irreducible] Functor.mapHomotopyCategoryFactors
  Functor.mapDerivedCategoryFactors DerivedCategory.Qh
  Functor.rightDerivedFunctorUnit Functor.leftDerivedFunctorCounit
  Adjunction.ofIsRightAdjoint Adjunction.homEquiv
  ProEtale.etaleSheafExtendScalarsAdjunction upperStarLowerStarAdjunction
  Adjunction.derivedAdjunction

private lemma geometricRepresentative_app
    (A : Type (u + 1)) [CommRing A] {W V : Scheme.{u}} (r : W ⟶ V)
    (C : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (leftComparisonTransformation (upperStar (ModuleCat.{u + 1} A) r)
      (upperStar (ModuleCat.{u + 1} A) r).leftDerivedFunctorCounit).app C =
      scalarGeometricRepresentative A r C := by
  exact Eq.refl (scalarGeometricRepresentative A r C)

private lemma acyclicComparisonTransformation_app
    (A : Type (u + 1)) [CommRing A] {W V : Scheme.{u}} (r : W ⟶ V)
    (C : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (acyclicComparisonTransformation (lowerStar (ModuleCat.{u + 1} A) r)).app C =
      properAcyclicComparison A r C := by
  exact Eq.refl (properAcyclicComparison A r C)

private lemma scalarRepresentativeTransformation_app
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (C : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (scalarRepresentativeTransformation φ T).app C =
      scalarExtensionRepresentative φ T C := by
  exact Eq.refl (scalarExtensionRepresentative φ T C)

private lemma acyclicComparison_naturality
    (A : Type (u + 1)) [CommRing A] {W V : Scheme.{u}} (r : W ⟶ V)
    {C C' : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ}
    (h : C ⟶ C') :
    DerivedCategory.Q.map
        (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).map h) ≫
        properAcyclicComparison A r C' =
      properAcyclicComparison A r C ≫
        (rightDerivedLowerStar (ModuleCat.{u + 1} A) r).map (DerivedCategory.Q.map h) := by
  have hn := (acyclicComparisonTransformation (lowerStar (ModuleCat.{u + 1} A) r)).naturality h
  simpa only [acyclicComparisonTransformation_app, Functor.comp_obj, Functor.comp_map,
    rightDerivedLowerStar] using hn

private lemma scalarRepresentative_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) :
    IsIso (scalarExtensionRepresentative φ T P) := by
  have : (ProEtale.etaleSheafExtendScalars φ T).PreservesKFlatQuasiIso :=
    scalar_preservesKFlatQuasiIso φ T
  dsimp only [scalarExtensionRepresentative]
  exact ordinaryScalarRepresentative_isIso (ProEtale.etaleSheafExtendScalarsAdjunction φ T)
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)) P hP

private lemma complex_iso_transformation
    {C₁ C₂ C₃ C₄ : Type*}
    [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    [Preadditive C₁] [Preadditive C₂] [Preadditive C₃] [Preadditive C₄]
    (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₄) (H : C₁ ⥤ C₃) (I : C₃ ⥤ C₄)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    (e : F ⋙ G ≅ H ⋙ I) :
    (Functor.mapHomologicalComplexCompIso e (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (H ⋙ I)) (.up ℤ)).symm).hom =
      complexTransformation F G H I e.hom := by
  ext C n
  simp only [complexTransformation, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f, NatTrans.mapHomologicalComplex_app_f,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
  exact (Category.id_comp _).symm

private lemma complex_mate
    {C₁ C₂ C₃ C₄ : Type*}
    [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    [Preadditive C₁] [Preadditive C₂] [Preadditive C₃] [Preadditive C₄]
    {G₁ : C₁ ⥤ C₂} {F₁ : C₂ ⥤ C₁} (adj₁ : G₁ ⊣ F₁)
    {G₂ : C₃ ⥤ C₄} {F₂ : C₄ ⥤ C₃} (adj₂ : G₂ ⊣ F₂)
    (H₁ : C₁ ⥤ C₃) (H₂ : C₂ ⥤ C₄)
    [G₁.Additive] [F₁.Additive] [G₂.Additive] [F₂.Additive]
    [H₁.Additive] [H₂.Additive]
    (σ : TwoSquare H₁ G₁ G₂ H₂) (C : CochainComplex C₂ ℤ) :
    (mateEquiv (adj₁.mapHomologicalComplex (.up ℤ))
      (adj₂.mapHomologicalComplex (.up ℤ))
      (TwoSquare.mk _ _ _ _ (complexTransformation H₁ G₂ G₁ H₂ σ))).app C =
      (complexTransformation F₁ H₁ H₂ F₂ (mateEquiv adj₁ adj₂ σ)).app C := by
  ext n
  simp only [complexTransformation, mateEquiv_apply, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Adjunction.mapHomologicalComplex_unit_app_f,
    Adjunction.mapHomologicalComplex_counit_app_f,
    NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, Functor.comp_obj, Functor.comp_map,
    HomologicalComplex.id_f, Category.id_comp, Category.assoc]
  dsimp only [Functor.mapHomologicalComplex]
  simp only [Category.id_comp]
  erw [Category.comp_id, Category.comp_id, Category.comp_id, Category.comp_id]

private lemma geometric_counit_normalization
    (A : Type (u + 1)) [CommRing A] {W V : Scheme.{u}} (r : W ⟶ V)
    (C : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    L(upperStar (ModuleCat.{u + 1} A) r).map (properAcyclicComparison A r C) ≫
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r).counit.app
          (DerivedCategory.Q.obj C) =
      scalarGeometricRepresentative A r
          (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C) ≫
        DerivedCategory.Q.map
          (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r).mapHomologicalComplex
            (.up ℤ)).counit.app C) := by
  simpa only [acyclicComparisonTransformation_app, geometricRepresentative_app,
    derivedUpperStarLowerStarAdjunction] using derived_counit_normalization
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r) C

private lemma geometric_unit_normalization
    (A : Type (u + 1)) [CommRing A] {W V : Scheme.{u}} (r : W ⟶ V)
    (C : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r).unit.app
          (DerivedCategory.Q.obj C) ≫
        R(lowerStar (ModuleCat.{u + 1} A) r).map (scalarGeometricRepresentative A r C) =
      DerivedCategory.Q.map
          (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r).mapHomologicalComplex
            (.up ℤ)).unit.app C) ≫
        properAcyclicComparison A r
          (((upperStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C) := by
  simpa only [acyclicComparisonTransformation_app, geometricRepresentative_app,
    derivedUpperStarLowerStarAdjunction] using derived_unit_normalization
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r) C

private lemma scalar_pullback_normalization
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W V : Scheme.{u}} (r : W ⟶ V)
    (C : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hC : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat C) :
    (scalarPullbackIso φ r).hom.app (DerivedCategory.Q.obj C) ≫
        (scalarExtension φ W).map (scalarGeometricRepresentative A r C) ≫
        scalarExtensionRepresentative φ W
          (((upperStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C) =
      L(upperStar (ModuleCat.{u + 1} B) r).map
          (scalarExtensionRepresentative φ V C) ≫
        scalarGeometricRepresentative B r
          (((ProEtale.etaleSheafExtendScalars φ V).mapHomologicalComplex (.up ℤ)).obj C) ≫
        DerivedCategory.Q.map ((scalarSheafPullbackComplexIso φ r).hom.app C) := by
  exact (scalarPullbackIso_existsUnique φ r).choose_spec.1 C hC

end ProofCalculations

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  ProEtale.pbcFixedScalarExtension derivedTensor upperStar lowerStar
  scalarExtensionRepresentative scalarGeometricRepresentative properAcyclicComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] Functor.mapHomotopyCategoryFactors
  Functor.mapDerivedCategoryFactors Functor.rightDerivedFunctorUnit
  Functor.leftDerivedFunctorCounit Adjunction.ofIsRightAdjoint Adjunction.homEquiv
  ProEtale.etaleSheafExtendScalarsAdjunction upperStarLowerStarAdjunction
  Adjunction.derivedAdjunction

attribute [local irreducible] DerivedCategory DerivedCategory.Q DerivedCategory.Qh
  HasDerivedCategory.ofIsGrothendieckAbelian ProEtale.etaleSheafExtendScalars
  mateEquiv scalarPullbackIso derivedUpperStarLowerStarAdjunction
  Adjunction.mapHomologicalComplex
  MorphismProperty.kFlat HomologicalComplex.quasiIso
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

end AlgebraicGeometry.Etale
