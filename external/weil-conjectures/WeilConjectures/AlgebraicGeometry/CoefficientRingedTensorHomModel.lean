/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
/-! # Canonical closed tensor-Hom models on a ringed site

Source: Stacks Project, Tags 06YN, 07A4, 08J9 and 0A98
(auxiliary; not a blueprint node).

## Main definitions

- `CoefficientClosedStructure`: closed monoidal data for the recorded internal Hom.
- `coefficientTotalTensor`: the actual total-complex tensor bifunctor.
- `coefficientTensorGenerator`: the actual sheafified pure-tensor summand inclusion.
- `CoefficientTensorModels`: natural K-flat comparison with canonical uncurrying.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u c v w a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace WeilConjectures

/-- Closed tensor data with the recorded internal-Hom bifunctor as right adjoint.
The tensor objects are determined by this universal property, up to the compatible
unique isomorphism. Evaluation and transposition are the counit and Hom equivalence;
they are not extra maps supplied after taking components.
Source: Stacks 08J9 (auxiliary; not a blueprint node). -/
structure CoefficientClosedStructure {D : Type a} [Category.{b} D]
    (H : Dᵒᵖ × D ⥤ D) where
  /-- The derived tensor monoidal structure. -/
  monoidal : MonoidalCategory D
  /-- Tensor-Hom adjunction in the tensor parameter. -/
  adjunction : ∀ P : D,
    @MonoidalCategory.tensorRight D _ monoidal P ⊣
      Prod.sectR (op P) D ⋙ H
  /-- The evaluations are natural also in the internal-Hom source. -/
  evaluation_naturality : ∀ (P P' Q : D) (f : P' ⟶ P),
    (@MonoidalCategory.tensorRight D _ monoidal P').map
        (H.map
        (Prod.mkHom (f.op) (𝟙 Q))) ≫ (adjunction P').counit.app Q =
      (@MonoidalCategory.tensorLeft D _ monoidal
        (H.obj (op P, Q))).map f ≫ (adjunction P).counit.app Q

namespace CoefficientClosedStructure

variable {D : Type a} [Category.{b} D] {H : Dᵒᵖ × D ⥤ D}
  (S : CoefficientClosedStructure H)

/-- The actual tensor bifunctor specified by closed derived tensor data.
Source: Stacks 07A4, 08J9 (auxiliary; not a blueprint node). -/
def tensor : D × D ⥤ D :=
  @MonoidalCategory.tensor D _ S.monoidal

/-- Evaluation in the derived system category itself.
Source: Stacks 08J9 (auxiliary; not a blueprint node). -/
def evaluation (P Q : D) : S.tensor.obj (H.obj (op P, Q), P) ⟶ Q :=
  (S.adjunction P).counit.app Q

/-- The tensor-Hom transpose in the derived system category itself.
Source: Stacks 08J9 (auxiliary; not a blueprint node). -/
def transpose (T P Q : D) : (S.tensor.obj (T, P) ⟶ Q) ≃ (T ⟶ H.obj (op P, Q)) :=
  (S.adjunction P).homEquiv T Q

end CoefficientClosedStructure

/-- The actual total-tensor bifunctor on complexes, retaining independent site sizes.
Source: Stacks 06YN, 07A4 (auxiliary; not a blueprint node). -/
noncomputable def coefficientTotalTensor
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
    (A : Sheaf J CommRingCat.{max c v u}) :
    CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ ×
    CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ ⥤
    CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ :=
  letI := (SheafOfModules.isMonoidal_W_independentCoefficients A)
  letI := SheafOfModules.monoidalCategory A
  letI := (SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients A)
  letI := (SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients A)
  Functor.uncurry.obj
    (Functor.map₂HomologicalComplex (MonoidalCategory.curriedTensor (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)))
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ))

/-- The full subcategory of the recorded K-flat complexes.
Source: Stacks 06YN (auxiliary; not a blueprint node). -/
noncomputable def coefficientKFlatInclusion
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
    (A : Sheaf J CommRingCat.{max c v u}) :
    ObjectProperty.FullSubcategory
      (CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (J := J) (R := A)) ⥤
      CochainComplex (SheafOfModules.{max c v u}
        ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ :=
  ObjectProperty.ι
    (CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (J := J) (R := A) :
    ObjectProperty (CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ))

section TensorRepresentatives

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (A : Sheaf J CommRingCat.{max c v u})

/-- A tensor generator before sheafification, mapped to its total-degree summand.
Source: Stacks 03EK, 06YN (auxiliary; not a blueprint node). -/
noncomputable def coefficientTensorGenerator
    (P Q : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (p q k : ℤ) (h : p + q = k) (U : Cᵒᵖ)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    (((coefficientTotalTensor.{u, c, v} J A).obj (P, Q)).X k).val.obj U :=
  letI := (SheafOfModules.isMonoidal_W_independentCoefficients A)
  letI := SheafOfModules.monoidalCategory A
  letI := (SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients A)
  letI := (SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients A)
  ((HomologicalComplex.ιMapBifunctor P Q (MonoidalCategory.curriedTensor _)
    (ComplexShape.up ℤ) p q k h).val.app U)
    (((PresheafOfModules.sheafificationAdjunction.{max c v u}
      (𝟙 ((sheafCompose J
        (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A).obj)).unit.app
        ((P.X p).val ⊗ (Q.X q).val) ≫
      (SheafOfModules.tensorObjIsoSheafification (R := A) (P.X p) (Q.X q)).inv.val).app U
        (x ⊗ₜ[A.obj.obj U] y))

end TensorRepresentatives

/-- The exact representative uncurrying equation, packaged once as a proposition.
Source: Stacks 07A4, 08J9 (auxiliary; not a blueprint node). -/
def CoefficientTensorUncurryModel
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
    (A : Sheaf J CommRingCat.{max c v u})
    [HasDerivedCategory.{w} (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A))]
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J A))
    (comparison : (((coefficientKFlatInclusion.{u, c, v} J A).prod
      (coefficientKFlatInclusion.{u, c, v} J A)) ⋙ coefficientTotalTensor.{u, c, v} J A ⋙
        DerivedCategory.Q ≅
    ((coefficientKFlatInclusion.{u, c, v} J A ⋙ DerivedCategory.Q).prod
      (coefficientKFlatInclusion.{u, c, v} J A ⋙ DerivedCategory.Q)) ⋙ S.tensor)) : Prop :=
  ∀ (P L : ObjectProperty.FullSubcategory
      (CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u}
        (J := J) (R := A)))
    (M : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (φ : P.1 ⟶ homComplex.{c, v, max c v u, max c v u} (R := A) L.1
        ((coefficientHomResolution.{u, c, v} J A).obj M)),
    ∃ ψ : (coefficientTotalTensor.{u, c, v} J A).obj (P.1, L.1) ⟶
        (coefficientHomResolution.{u, c, v} J A).obj M,
      ((∀ (p q k : ℤ) (h : p + q = k) (h' : q + p = k) (U : Cᵒᵖ)
        (x : (P.1.X p).val.obj U) (y : (L.1.X q).val.obj U),
        (ψ.f k).val.app U (coefficientTensorGenerator.{u, c, v} J A P.1 L.1 p q k h U x y) =
          coefficientHomSectionEvaluation.{u, c, v} J A P.1 L.1 M φ p q k h' U x y) ∧
      comparison.hom.app (P, L) ≫
        (S.transpose (DerivedCategory.Q.obj P.1) (DerivedCategory.Q.obj L.1)
          (DerivedCategory.Q.obj M)).symm
            (DerivedCategory.Q.map φ ≫ (coefficientHomResolutionIso.{u, c, v, w} J A L.1 M).inv) =
        DerivedCategory.Q.map ψ ≫ coefficientHomResolutionInverse.{u, c, v, w} J A M)

-- Elaborate the representative tensor-Hom square with independent site universes.
/-- A derived tensor is specified by the natural total-tensor comparison on K-flats.
This is a universal representative characterization, not an extra assumption on inputs.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
structure CoefficientTensorModels
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
    (A : Sheaf J CommRingCat.{max c v u})
    [HasDerivedCategory.{w} (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A))]
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J A)) where
  /-- The simultaneous total-tensor comparison on the K-flat presentation. -/
  comparison : (((coefficientKFlatInclusion.{u, c, v} J A).prod
      (coefficientKFlatInclusion.{u, c, v} J A)) ⋙ coefficientTotalTensor.{u, c, v} J A ⋙
        DerivedCategory.Q ≅
    ((coefficientKFlatInclusion.{u, c, v} J A ⋙ DerivedCategory.Q).prod
      (coefficientKFlatInclusion.{u, c, v} J A ⋙ DerivedCategory.Q)) ⋙ S.tensor)

  /-- The closed adjunction is ordinary componentwise evaluation on representatives. -/
  uncurry_model : CoefficientTensorUncurryModel.{u, c, v, w} J A S comparison

/-- Computation of a chosen derived tensor on the displayed K-flat representatives.
Source: Stacks 06YU (auxiliary; not a blueprint node). -/
noncomputable def CoefficientTensorModels.iso
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
    (A : Sheaf J CommRingCat.{max c v u})
    [HasDerivedCategory.{w} (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A))]
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J A))
    (T : CoefficientTensorModels.{u, c, v, w} J A S)
    (P Q : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (J := J) (R := A) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (J := J) (R := A) Q) :
    DerivedCategory.Q.obj ((coefficientTotalTensor.{u, c, v} J A).obj (P, Q)) ≅
      S.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) :=
  T.comparison.app (⟨P, hP⟩, ⟨Q, hQ⟩)

end WeilConjectures
