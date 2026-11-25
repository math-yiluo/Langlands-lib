/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Derived.DerivedTensorRightExact
public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.CategoryTheory.SixFunctors.HomShiftEvaluationNormalization
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated

import WeilConjectures.CategoryTheory.Adjunction.Derived.DerivedAdjointCochainCounit
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import Mathlib.RingTheory.Flat.Stability
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
import WeilConjectures.CategoryTheory.Sites.ReductionFlat
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic

/-! # Models for the étale scalar internal-Hom comparison

Source: blueprint `lemma-change-coefficients-internal-hom--1`, proof paragraph 2; Stacks 06YY, 07A4,
08J9 and 08JC (blueprint: `lem-coef-etale-hom-thick-locus`).

The scalar extension functor and the derived internal Hom are the published étale
constructions.  The comparison is specified by its tensor--Hom transpose, so that
the statement retains the actual evaluation map and does not choose an unrelated
map between the two Hom objects.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v w w₁ w₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open CategoryTheory.Pretriangulated.Opposite Opposite

namespace AlgebraicGeometry.Etale

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] _root_.DerivedCategory.monoidalClosed
  Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit

variable {A B : Type (u + 1)} [CommRing A] [CommRing B]

/-- Scalar extension of Hom, contravariant in K.
Source: blueprint lemma-change-coefficients-internal-hom--1, proof paragraph 2
(blueprint: lem-coef-etale-hom-thick-locus). -/
abbrev EtaleHomLeft (X : Scheme.{u}) (φ : A →+* B)
    (M : DerivedCategoryModule A X) :
    (DerivedCategoryModule A X)ᵒᵖ ⥤ DerivedCategoryModule B X :=
  (derivedHom (ModuleCat.{u + 1} A) X).flip.obj M ⋙ scalarExtension φ X

/-- Hom of scalar extensions, contravariant in K.
Source: blueprint lemma-change-coefficients-internal-hom--1, proof paragraph 2
(blueprint: lem-coef-etale-hom-thick-locus). -/
abbrev EtaleHomRight (X : Scheme.{u}) (φ : A →+* B)
    (M : DerivedCategoryModule A X) :
    (DerivedCategoryModule A X)ᵒᵖ ⥤ DerivedCategoryModule B X :=
  (scalarExtension φ X).op ⋙
    (derivedHom (ModuleCat.{u + 1} B) X).flip.obj ((scalarExtension φ X).obj M)

/-- Type of binary tensor comparisons; canonicity is imposed below.
Source: Stacks 07A4, tensor compatibility
(blueprint: lem-coef-etale-hom-thick-locus). -/
abbrev EtaleHomTensorComparison (X : Scheme.{u}) (φ : A →+* B) : Type _ :=
  ∀ K L : DerivedCategoryModule A X,
    ((derivedTensor (ModuleCat.{u + 1} B) X).obj ((scalarExtension φ X).obj K)).obj
        ((scalarExtension φ X).obj L) ≅
      (scalarExtension φ X).obj
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj K).obj L)

section TensorNormalization

variable (C : Type w₁) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [MonoidalClosed C] [SymmetricCategory C] [Abelian.HasFunctorialFlatResolution C]
  (D : Type w₂) [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
  [MonoidalClosed D] [SymmetricCategory D] [Abelian.HasFunctorialFlatResolution D]
  (X : Scheme.{u})

/-- The binary derived comparison is normalized by the ordinary oplax tensorator.
The equation is imposed on K-flat complexes with flat terms. Its bottom arrow is
ordinary scalar balancing, inverse to (x tensor b) tensor (y tensor c) ↦
(x tensor y) tensor bc. The comparison maps r are the derived-extension counit.
Source: Stacks 06YY and 07A4, proof step 1 of the node
(blueprint: lem-coef-etale-hom-thick-locus). -/
def EtaleHomTensorModelNormalization
    (E : Sheaf X.smallEtaleTopology C ⥤ Sheaf X.smallEtaleTopology D) [E.Additive] [E.IsLeftAdjoint]
    [E.OplaxMonoidal]
    (F : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology D))
    (r : ∀ P : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ,
      F.obj (_root_.DerivedCategory.Q.obj P) ⟶
      _root_.DerivedCategory.Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj P))
    (μ : ∀ K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C),
      ((derivedTensor D X).obj (F.obj K)).obj (F.obj L) ≅
        F.obj (((derivedTensor C X).obj K).obj L)) : Prop :=
  Functor.rightExactTensorModelNormalization E F r μ

end TensorNormalization

/-- Naturality in both tensor variables and the flat-term K-flat normalization.
The ordinary oplax structure is the mate of the fixed lax restriction-of-scalars
structure, so it cannot be twisted by per-object automorphisms.
Source: Stacks 07A4, proof step 1 of the node
(blueprint: lem-coef-etale-hom-thick-locus). -/
def IsEtaleHomTensorCanonical (X : Scheme.{u}) (φ : A →+* B)
    (μ : EtaleHomTensorComparison X φ) : Prop :=
  (∀ {K K' : DerivedCategoryModule A X} (f : K ⟶ K') (L : DerivedCategoryModule A X),
    ((derivedTensor (ModuleCat.{u + 1} B) X).map ((scalarExtension φ X).map f)).app
        ((scalarExtension φ X).obj L) ≫ (μ K' L).hom =
      (μ K L).hom ≫ (scalarExtension φ X).map
        (((derivedTensor (ModuleCat.{u + 1} A) X).map f).app L)) ∧
  (∀ (K : DerivedCategoryModule A X) {L L' : DerivedCategoryModule A X} (g : L ⟶ L'),
    ((derivedTensor (ModuleCat.{u + 1} B) X).obj ((scalarExtension φ X).obj K)).map
        ((scalarExtension φ X).map g) ≫ (μ K L').hom =
      (μ K L).hom ≫ (scalarExtension φ X).map
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj K).map g)) ∧
  (letI := (ProEtale.etaleSheafExtendScalarsAdjunction φ X).isLeftAdjoint
   letI := (ProEtale.etaleSheafExtendScalarsAdjunction φ X).leftAdjointOplaxMonoidal
   EtaleHomTensorModelNormalization (ModuleCat.{u + 1} A) (ModuleCat.{u + 1} B) X
     (ProEtale.etaleSheafExtendScalars φ X)
     (scalarExtension φ X) (scalarExtensionRepresentative φ X) μ)

section SiteTensorProof

private theorem tensorComparison_onSite
    (C : Type w₁) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [SymmetricCategory C] [Abelian.HasFunctorialFlatResolution C]
    (D : Type w₂) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
    [MonoidalClosed D] [SymmetricCategory D] [Abelian.HasFunctorialFlatResolution D]
    (X : Scheme.{u})
    (E : Sheaf X.smallEtaleTopology C ⥤ Sheaf X.smallEtaleTopology D)
    [E.Additive] [E.IsLeftAdjoint] [E.PreservesFlat] [E.PreservesKFlatQuasiIso] [E.Monoidal]
    (F : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology D)) (e : F ≅ E.leftDerivedFunctor)
    (r : ∀ P : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ,
      F.obj (_root_.DerivedCategory.Q.obj P) ⟶
        _root_.DerivedCategory.Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj P))
    (hr : ∀ P, r P = e.hom.app (_root_.DerivedCategory.Q.obj P) ≫
      E.rightExact_cochainCounit P) :
    ∃! μ : ∀ K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C),
      ((derivedTensor D X).obj (F.obj K)).obj (F.obj L) ≅
        F.obj (((derivedTensor C X).obj K).obj L),
      (∀ {K K'} (f : K ⟶ K') L,
        ((derivedTensor D X).map (F.map f)).app (F.obj L) ≫ (μ K' L).hom =
          (μ K L).hom ≫ F.map (((derivedTensor C X).map f).app L)) ∧
      (∀ K {L L'} (f : L ⟶ L'),
        ((derivedTensor D X).obj (F.obj K)).map (F.map f) ≫ (μ K L').hom =
          (μ K L).hom ≫ F.map (((derivedTensor C X).obj K).map f)) ∧
      EtaleHomTensorModelNormalization C D X E F r μ := by
  have h := Functor.rightExact_tensorComparison_existsUnique E F e r hr
  dsimp only [derivedTensor, EtaleHomTensorModelNormalization]
  exact h

end SiteTensorProof

section ScalarTensorProof

private noncomputable abbrev scalarSheafMonoidal
    (R : Type (u + 1)) [CommRing R] (X : Scheme.{u}) :
    MonoidalCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) := inferInstance

attribute [local instance 2000] scalarSheafMonoidal

private theorem mapComplex_unit_formula
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    {E : C ⥤ D} {U : D ⥤ C} [E.Additive] [U.Additive] (adj : E ⊣ U)
    (P : CochainComplex C ℤ) :
    (adj.mapHomologicalComplex (.up ℤ)).unit.app P =
      (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
        (NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app P ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ U)) (.up ℤ)).inv.app P := by
  ext i
  simp only [Functor.id_obj, Functor.comp_obj, Adjunction.mapHomologicalComplex_unit_app_f,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplexIdIso_inv_app_f,
    NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplexCompIso_inv_app_f,
    Iso.refl_inv, NatTrans.id_app, Category.id_comp]
  exact (Category.comp_id _).symm

private theorem extension_flat {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (M : ModuleCat.{u + 1} A) (hM : ObjectProperty.flat M) :
    ObjectProperty.flat ((ModuleCat.extendScalars φ).obj M) := by
  apply (ModuleCat.flat_iff_flat _).2
  let := (ModuleCat.flat_iff_flat M).1 hM
  let := φ.toAlgebra
  exact Module.Flat.baseChange A B M

private theorem extension_preservesFlat {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) :
    (ProEtale.etaleSheafExtendScalars φ X).PreservesFlat := by
  constructor
  intro M hM
  apply (flat_iff_forall_flat_sheafFiber_obj _).2
  intro Ω _ _ s
  let p : X.smallEtaleTopology.Point.{u + 1} :=
    (Scheme.pointSmallEtale s).ulift.{u + 1}
  let E : ModuleCat.{u + 1} A ⥤ ModuleCat.{u + 1} B :=
    ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ
  let : E.IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ).isLeftAdjoint
  let W := (Functor.whiskeringRight X.Etaleᵒᵖ (ModuleCat.{u + 1} A)
    (ModuleCat.{u + 1} B)).obj E
  let q := sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)
  let a := presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)
  let e₀ := p.presheafToSheafCompSheafFiberIso (ModuleCat.{u + 1} B)
  let e₁ := p.presheafFiberCompIso E
  let e : ProEtale.etaleSheafExtendScalars φ X ⋙ p.sheafFiber ≅
      p.sheafFiber ⋙ E :=
    Functor.associator q (W ⋙ a) p.sheafFiber ≪≫
      Functor.isoWhiskerLeft q (Functor.associator W a p.sheafFiber) ≪≫
      Functor.isoWhiskerLeft q (Functor.isoWhiskerLeft W e₀) ≪≫
      Functor.isoWhiskerLeft q e₁ ≪≫
      (Functor.associator q p.presheafFiber E).symm
  exact ObjectProperty.prop_of_iso _ (e.app M).symm
    (extension_flat φ _ ((flat_iff_forall_flat_sheafFiber_obj M).1 hM s))

private theorem extension_preservesKFlatQuasiIso {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (φ : R →+* S) (X : Scheme.{u}) :
    (ProEtale.etaleSheafExtendScalars φ X).PreservesKFlatQuasiIso := by
  classical
  let E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) ⥤ Sheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} S) :=
    Sheaf.composeAndSheafify X.smallEtaleTopology (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)
  let U := Sheaf.restrictScalars X.smallEtaleTopology φ
  let adj : E ⊣ U :=
    Sheaf.adjunction X.smallEtaleTopology (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u +
      1} φ)
  have : E.Additive := adj.left_adjoint_additive
  let B := (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ).obj (ModuleCat.of S S)
  let coeff := (Functor.const X.Etaleᵒᵖ).obj B
  let a := presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)
  let a' := presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} S)
  let F := sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)
  let W := (Functor.whiskeringRight X.Etaleᵒᵖ _ _).obj
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)
  have : X.smallEtaleTopology.PreservesSheafification (ModuleCat.restrictScalars.{u + 1, u + 1, u
    + 1} φ) :=
    Sheaf.preservesSheafification_of_adjunction X.smallEtaleTopology
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ)
  let e : E ⋙ U ≅ MonoidalCategory.tensorRight (a.obj coeff) :=
    Functor.associator F (W ⋙ a') U ≪≫
      Functor.isoWhiskerLeft F (Functor.associator W a' U) ≪≫
      Functor.isoWhiskerLeft F (Functor.isoWhiskerLeft W
        (sheafComposeNatIso X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ)
          (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} S))
          (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} R))).symm) ≪≫
      Functor.isoWhiskerLeft F (Functor.associator W _ a).symm ≪≫
      Functor.isoWhiskerLeft F (Functor.isoWhiskerRight
        (Functor.whiskeringRightObjCompIso _ _ ≪≫
          (Functor.whiskeringRight _ _ _).mapIso
            (ModuleCat.extendScalarsCompRestrictScalarsIso.{u + 1} φ) ≪≫
          whiskeringRightTensorRightIso _) a) ≪≫
      Functor.isoWhiskerLeft F (Sheaf.presheafToSheafCompTensorRightIso coeff).symm ≪≫
      (Functor.associator F a (MonoidalCategory.tensorRight (a.obj coeff))).symm ≪≫
      Functor.isoWhiskerRight
        (asIso (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} R)).counit)
        (MonoidalCategory.tensorRight (a.obj coeff)) ≪≫ Functor.leftUnitor _
  have hU : U.Faithful := inferInstance
  have : HasColimitsOfSize.{u + 1, u + 1} (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
    IsGrothendieckAbelian.hasColimits _
  have : HasColimitsOfSize.{0, 0} (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
    hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} _
  have : HasCountableCoproducts (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
    ⟨fun K _ ↦ HasColimitsOfSize.has_colimits_of_shape (Discrete K)⟩
  have hE : E.PreservesKFlatQuasiIso := by
    apply CategoryTheory.Functor.PreservesKFlatQuasiIso.mk'
    intro K hK hKa
    have ht := CochainComplex.acyclic_tensorRight_of_kFlat K hK hKa (a.obj coeff)
    have hEU := ht.of_iso
      ((NatIso.mapHomologicalComplex e (.up ℤ)).app K).symm
    have hUK : ((U.mapHomologicalComplex (.up ℤ)).obj
        ((E.mapHomologicalComplex (.up ℤ)).obj K)).Acyclic :=
      hEU.of_iso ((CategoryTheory.Functor.mapHomologicalComplexCompIso
        (Iso.refl (E ⋙ U)) (.up ℤ)).app K)
    intro n
    exact (ShortComplex.exact_map_iff_of_faithful _ U).1 (hUK n)
  exact hE

/-- The canonical binary tensor comparison exists uniquely.
Source: Stacks 06YY and 07A4, proof step 1 of the node
(blueprint: lem-coef-etale-tensor-model-comparison).
Proof: on two flat-term K-flat resolutions, termwise scalar balancing is the
isomorphism (x tensor b) tensor (y tensor c) ↦ (x tensor y) tensor bc.
The total differential is preserved because the coefficients have degree zero.
The displayed counit equation expresses this map after localization. Naturality
of balancing permits descent along quasi-isomorphisms between K-flat models.
Every object has such a model, and naturality along its resolution determines
every component, proving uniqueness. No flatness of B over A is needed. -/
theorem etaleHomTensorComparison_existsUnique (X : Scheme.{u}) (φ : A →+* B) :
    ∃! μ : EtaleHomTensorComparison X φ, IsEtaleHomTensorCanonical X φ μ := by
  let E := ProEtale.etaleSheafExtendScalars φ X
  let U := Sheaf.restrictScalars X.smallEtaleTopology φ
  let adj : E ⊣ U := ProEtale.etaleSheafExtendScalarsAdjunction φ X
  let : E.IsLeftAdjoint := adj.isLeftAdjoint
  let : E.PreservesFlat := extension_preservesFlat φ X
  let : E.PreservesKFlatQuasiIso := extension_preservesKFlatQuasiIso φ X
  let : E.OplaxMonoidal := adj.leftAdjointOplaxMonoidal
  let : E.Monoidal := CategoryTheory.composeAndSheafifyMonoidal X.smallEtaleTopology
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)
  let ad : scalarExtension φ X ⊣ U.mapDerivedCategory := Adjunction.ofIsRightAdjoint _
  let b : E.leftDerivedFunctor ⊣ U.mapDerivedCategory :=
    adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory
  let e : scalarExtension φ X ≅ E.leftDerivedFunctor := ad.leftAdjointUniq b
  have hr : ∀ P, scalarExtensionRepresentative φ X P =
      e.hom.app (_root_.DerivedCategory.Q.obj P) ≫ E.rightExact_cochainCounit P := by
    intro P
    unfold scalarExtensionRepresentative
    rw [← mapComplex_unit_formula]
    dsimp only [Functor.rightExact_cochainCounit]
    have h := (Adjunction.leftDerivedCochainCounit E U adj ad P).symm
    simp only [E, U, adj, ad, e, b, Functor.id_obj,
      Iso.app_inv, Iso.app_hom] at h ⊢
    exact h
  have h := tensorComparison_onSite (ModuleCat.{u + 1} A) (ModuleCat.{u + 1} B) X E
    (scalarExtension φ X) e (scalarExtensionRepresentative φ X) hr
  simpa only [IsEtaleHomTensorCanonical, E, U, adj] using h

end ScalarTensorProof

/-- The uniquely normalized binary comparison, used in the evaluation transpose.
Source: Stacks 07A4, proof step 1 of the node
(blueprint: lem-coef-etale-hom-thick-locus). -/
def etaleHomTensorComparison (X : Scheme.{u}) (φ : A →+* B) :
    EtaleHomTensorComparison X φ :=
  (etaleHomTensorComparison_existsUnique X φ).choose

/-- The defining evaluation-transpose equation for the canonical comparison.
Source: blueprint lemma-change-coefficients-internal-hom--1, proof paragraph 2
(blueprint: lem-coef-etale-hom-thick-locus). -/
def IsEtaleHomTranspose (X : Scheme.{u}) (φ : A →+* B)
    (M : DerivedCategoryModule A X)
    (v : EtaleHomLeft X φ M ⟶ EtaleHomRight X φ M) : Prop :=
  ∀ K : DerivedCategoryModule A X,
    (etaleHomTensorComparison X φ K
        (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj M)).hom ≫
        (scalarExtension φ X).map
          ((derivedTensorHomAdjunction (ModuleCat.{u + 1} A) (X := X) K).counit.app M) =
      ((derivedTensorHomAdjunction (ModuleCat.{u + 1} B) (X := X)
          ((scalarExtension φ X).obj K)).homEquiv _ _).symm (v.app (op K))

/-- Naturality of the family of evaluation transposes in the second variable.
Source: blueprint lemma-change-coefficients-internal-hom--1, proof paragraph 2
(blueprint: lem-coef-etale-hom-thick-locus). -/
def IsEtaleHomNaturalInM (X : Scheme.{u}) (φ : A →+* B)
    (v : ∀ M : DerivedCategoryModule A X,
      EtaleHomLeft X φ M ⟶ EtaleHomRight X φ M) : Prop :=
  ∀ {M N : DerivedCategoryModule A X} (g : M ⟶ N)
    (K : DerivedCategoryModule A X),
    (scalarExtension φ X).map
        (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).map g) ≫
        (v N).app (op K) =
      (v M).app (op K) ≫
        ((derivedHom (ModuleCat.{u + 1} B) X).obj (op ((scalarExtension φ X).obj K))).map
          ((scalarExtension φ X).map g)

section HomShiftNormalization

variable (C : Type w) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [MonoidalClosed C] [SymmetricCategory C] [Abelian.HasFunctorialFlatResolution C]
  (X : Scheme.{u})

/-- Canonical cancellation of the two opposite tensor shifts, with the tensor signs.
Source: Stacks 08JC and the tensor-shift calculation in proof step 4
(blueprint: lem-coef-etale-hom-thick-locus). -/
def etaleHomTensorShiftCancellation
    (K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)) (n : ℤ) :
    ((derivedTensor C X).obj (K⟦-n⟧)).obj (L⟦n⟧) ⟶ ((derivedTensor C X).obj K).obj L :=
  (((curriedTensor _).flip.obj (L⟦n⟧)).commShiftIso (-n)).hom.app K ≫
    ((((curriedTensor _).obj K).commShiftIso n).hom.app L)⟦-n⟧' ≫
    (shiftFunctorCompIsoId _ n (-n) (add_neg_cancel n)).hom.app _

/-- The canonical contravariant Hom shift is fixed by evaluation and tensor shifts.
This equation determines the shift, since its transpose is fixed and shifting is
an equivalence. In complex notation it is the signed reindexing of Hom. With the
tensor shifts composed as in `etaleHomTensorShiftCancellation`, the Hom shift carries
the explicit factor `((n * (n + 1)) / 2).negOnePow`; on Hom complexes it is then
f ↦ (-1)^(n*j + n*(n+1)/2) f in degree j, the sign of Mathlib's `Cochain.leftShift`
by -n. The factor is -1 for n = 1, as the cone triangle's connecting morphism in
the opposite triangulated convention requires. It satisfies
ε(a+b) = (-1)^(a*b) ε(a) ε(b), which compensates c(a+b) = (-1)^(a*b) c(a) c(b) for the
cancellations, so the normalized family obeys the `CommShift` addition axiom
(a multiplicative factor such as `n.negOnePow` would not). It applies to both
coefficient Hom functors.
Source: Stacks 08JC, proof steps 4 and 5
(blueprint: lem-coef-etale-hom-thick-locus). -/
def EtaleHomShiftNormalization
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C))
    (s : ((derivedHom C X).flip.obj M).CommShift ℤ) : Prop :=
  homShiftEvaluationNormalization M s

end HomShiftNormalization

/-- The scalar shift is the canonical adjoint mate of exact restriction's shift.
This is the counit-compatible shift, hence on K-flat models the termwise shift.
Source: Stacks 05SU and 06YY, proof step 1
(blueprint: lem-coef-etale-hom-thick-locus). -/
@[instance_reducible]
def etaleHomScalarCommShift (X : Scheme.{u}) (φ : A →+* B) :
    (scalarExtension φ X).CommShift ℤ :=
  (Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)).leftAdjointCommShift ℤ

/-- Exactness with the evaluation-normalized Hom shifts and the fixed scalar shift.
The two component equations are chi_Phi = F(s_A) followed by sigma and
chi_Psi = H_B(sigma inverse,1) followed by s_B. The very same structures make
both functors triangulated and v a shift-compatible natural transformation;
therefore its third triangle square includes the connecting map and its sign.
Source: Stacks 08JC, proof steps 4--6
(blueprint: lem-coef-etale-hom-thick-locus). -/
def IsEtaleHomReversedExact (X : Scheme.{u}) (φ : A →+* B)
    (M : DerivedCategoryModule A X)
    (v : EtaleHomLeft X φ M ⟶ EtaleHomRight X φ M) : Prop :=
  letI := etaleHomScalarCommShift X φ
  ∃ (sA : ((derivedHom (ModuleCat.{u + 1} A) X).flip.obj M).CommShift ℤ)
    (sB : ((derivedHom (ModuleCat.{u + 1} B) X).flip.obj
      ((scalarExtension φ X).obj M)).CommShift ℤ)
    (_chiPhi : (EtaleHomLeft X φ M).CommShift ℤ)
    (_chiPsi : (EtaleHomRight X φ M).CommShift ℤ),
    EtaleHomShiftNormalization (ModuleCat.{u + 1} A) X M sA ∧
    EtaleHomShiftNormalization (ModuleCat.{u + 1} B) X ((scalarExtension φ X).obj M) sB ∧
    (∀ (K : DerivedCategoryModule A X) (n : ℤ),
      ((EtaleHomLeft X φ M).commShiftIso n).hom.app (op K) =
        (scalarExtension φ X).map ((sA.commShiftIso n).hom.app (op K)) ≫
          ((scalarExtension φ X).commShiftIso n).hom.app
            (((derivedHom (ModuleCat.{u + 1} A) X).flip.obj M).obj (op K))) ∧
    (∀ (K : DerivedCategoryModule A X) (n : ℤ),
      ((EtaleHomRight X φ M).commShiftIso n).hom.app (op K) =
        ((derivedHom (ModuleCat.{u + 1} B) X).flip.obj
            ((scalarExtension φ X).obj M)).map
          ((((scalarExtension φ X).commShiftIso (-n)).inv.app K).op) ≫
        (sB.commShiftIso n).hom.app (op ((scalarExtension φ X).obj K))) ∧
    (EtaleHomLeft X φ M).IsTriangulated ∧
    (EtaleHomRight X φ M).IsTriangulated ∧ NatTrans.CommShift v ℤ

/-- The isomorphism locus and its thick-subcategory closure properties.
Source: blueprint lemma-change-coefficients-internal-hom--1, proof paragraph 2
(blueprint: lem-coef-etale-hom-thick-locus). -/
def IsEtaleHomThickIsoLocus (X : Scheme.{u}) (φ : A →+* B)
    (M : DerivedCategoryModule A X)
    (v : EtaleHomLeft X φ M ⟶ EtaleHomRight X φ M) : Prop :=
  (∀ (K : (DerivedCategoryModule A X)ᵒᵖ), IsZero K → IsIso (v.app K)) ∧
  (∀ {K L : (DerivedCategoryModule A X)ᵒᵖ} (_e : K ≅ L),
    IsIso (v.app K) ↔ IsIso (v.app L)) ∧
  (∀ (K : (DerivedCategoryModule A X)ᵒᵖ) (n : ℤ), IsIso (v.app K) →
    IsIso (v.app (K⟦n⟧))) ∧
  (∀ (T : Triangle ((DerivedCategoryModule A X)ᵒᵖ)), T ∈ distTriang _ →
    IsIso (v.app T.obj₁) → IsIso (v.app T.obj₂) → IsIso (v.app T.obj₃)) ∧
  (∀ {K L : (DerivedCategoryModule A X)ᵒᵖ} (i : K ⟶ L) (r : L ⟶ K),
    i ≫ r = 𝟙 K → IsIso (v.app L) → IsIso (v.app K))

end AlgebraicGeometry.Etale
