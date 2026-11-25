/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorTranspositionData
import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorAssociatorRepresentatives
import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorUnitRepresentatives
import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorSymmetryRepresentatives
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Structural coherence of a normalized ringed tensor comparison

Source: Stacks Project, Tags 0FPT, 06YU and 0G7D
(blueprint: lem-sf-ringed-forget-tensor-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false

universe b vb a va c v r d vd s wb wa
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
-- Keep the chosen internal-Hom and localization constructions behind their APIs.
attribute [local irreducible] homComplexFunctor homComplexπ derivedInternalHomOfUniverses
  coefficientHomResolutionIso Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  DerivedCategory instCategoryDerivedCategory DerivedCategory.Q
  SheafOfModules.IsFlatOnSite
  CochainComplex.IsKFlatIndependentCoefficients

namespace CategoryTheory.RingedForgetTensorTransposition

section Transport

variable {B : Type b} [Category.{vb} B] {A : Type a} [Category.{va} A]
  {H : Bᵒᵖ × B ⥤ B} {H' : Aᵒᵖ × A ⥤ A}
  (S : CoefficientClosedStructure H) (T : CoefficientClosedStructure H')
  (F : B ⥤ A) (μ : S.tensor ⋙ F ≅ (F.prod F) ⋙ T.tensor)

private def rho (X Y : B) :
    F.obj (S.tensor.obj (X, Y)) ≅ T.tensor.obj (F.obj X, F.obj Y) :=
  μ.app (X, Y)

private theorem rho_naturality (X Y X' Y' : B) (f : X ⟶ X') (g : Y ⟶ Y') :
    F.map (S.tensor.map (f, g)) ≫ (rho S T F μ X' Y').hom =
      (rho S T F μ X Y).hom ≫ T.tensor.map (F.map f, F.map g) :=
  μ.hom.naturality (X := (X, Y)) (Y := (X', Y')) (f, g)

private theorem associator_of_iso
    {P Q N L M V : B} (e : P ≅ L) (e' : Q ≅ M) (e'' : N ≅ V)
    (h : F.map (S.monoidal.associator P Q N).hom ≫
      (rho S T F μ P (S.tensor.obj (Q, N))).hom ≫
      T.tensor.map (X := (F.obj P, F.obj (S.tensor.obj (Q, N))))
        (Y := (F.obj P, T.tensor.obj (F.obj Q, F.obj N)))
        (𝟙 (F.obj P), (rho S T F μ Q N).hom) =
      (rho S T F μ (S.tensor.obj (P, Q)) N).hom ≫
      T.tensor.map (X := (F.obj (S.tensor.obj (P, Q)), F.obj N))
        (Y := (T.tensor.obj (F.obj P, F.obj Q), F.obj N))
        ((rho S T F μ P Q).hom, 𝟙 (F.obj N)) ≫
      (T.monoidal.associator (F.obj P) (F.obj Q) (F.obj N)).hom) :
    F.map (S.monoidal.associator L M V).hom ≫
      (rho S T F μ L (S.tensor.obj (M, V))).hom ≫
      T.tensor.map (X := (F.obj L, F.obj (S.tensor.obj (M, V))))
        (Y := (F.obj L, T.tensor.obj (F.obj M, F.obj V)))
        (𝟙 (F.obj L), (rho S T F μ M V).hom) =
      (rho S T F μ (S.tensor.obj (L, M)) V).hom ≫
      T.tensor.map (X := (F.obj (S.tensor.obj (L, M)), F.obj V))
        (Y := (T.tensor.obj (F.obj L, F.obj M), F.obj V))
        ((rho S T F μ L M).hom, 𝟙 (F.obj V)) ≫
      (T.monoidal.associator (F.obj L) (F.obj M) (F.obj V)).hom := by
  let := S.monoidal
  let := T.monoidal
  let F₁ := (leftAssocTensor B) ⋙ F
  let F₂ := (rightAssocTensor B) ⋙ F
  let G₁ := (F.prod (F.prod F)) ⋙ leftAssocTensor A
  let G₂ := (F.prod (F.prod F)) ⋙ rightAssocTensor A
  let α : F₁ ⟶ F₂ := Functor.whiskerRight (associatorNatIso B).hom F
  let β : G₁ ⟶ G₂ := Functor.whiskerLeft (F.prod (F.prod F)) (associatorNatIso A).hom
  let c₁ : F₁ ⟶ G₁ :=
    { app := fun X ↦ (rho S T F μ (X.1 ⊗ X.2.1) X.2.2).hom ≫
        (rho S T F μ X.1 X.2.1).hom ▷ F.obj X.2.2
      naturality := by
        intro X Y f
        have h₁ := rho_naturality S T F μ (X.1 ⊗ X.2.1) X.2.2
          (Y.1 ⊗ Y.2.1) Y.2.2 (f.1 ⊗ₘ f.2.1) f.2.2
        have h₂ := rho_naturality S T F μ X.1 X.2.1 Y.1 Y.2.1 f.1 f.2.1
        simp only [CoefficientClosedStructure.tensor, tensor_map] at h₁ h₂
        change F.map ((f.1 ⊗ₘ f.2.1) ⊗ₘ f.2.2) ≫ _ = _
        rw [reassoc_of% h₁]
        change (rho S T F μ (X.1 ⊗ X.2.1) X.2.2).hom ≫
            (F.map (f.1 ⊗ₘ f.2.1) ⊗ₘ F.map f.2.2) ≫
              (rho S T F μ Y.1 Y.2.1).hom ▷ F.obj Y.2.2 = _
        simp only [← tensorHom_id, Category.assoc,
          tensorHom_comp_tensorHom,
          Category.comp_id]
        erw [h₂]
        simp only [G₁, Functor.comp_map, Functor.prod_map,
          leftAssocTensor_map,
          tensorHom_comp_tensorHom,
          Category.id_comp] }
  let c₂ : F₂ ⟶ G₂ :=
    { app := fun X ↦ (rho S T F μ X.1 (X.2.1 ⊗ X.2.2)).hom ≫
        F.obj X.1 ◁ (rho S T F μ X.2.1 X.2.2).hom
      naturality := by
        intro X Y f
        have h₁ := rho_naturality S T F μ X.1 (X.2.1 ⊗ X.2.2)
          Y.1 (Y.2.1 ⊗ Y.2.2) f.1 (f.2.1 ⊗ₘ f.2.2)
        have h₂ := rho_naturality S T F μ X.2.1 X.2.2 Y.2.1 Y.2.2 f.2.1 f.2.2
        simp only [CoefficientClosedStructure.tensor, tensor_map] at h₁ h₂
        change F.map (f.1 ⊗ₘ (f.2.1 ⊗ₘ f.2.2)) ≫ _ = _
        rw [reassoc_of% h₁]
        change (rho S T F μ X.1 (X.2.1 ⊗ X.2.2)).hom ≫
            (F.map f.1 ⊗ₘ F.map (f.2.1 ⊗ₘ f.2.2)) ≫
              F.obj Y.1 ◁ (rho S T F μ Y.2.1 Y.2.2).hom = _
        simp only [← id_tensorHom, Category.assoc,
          tensorHom_comp_tensorHom,
          Category.comp_id]
        erw [h₂]
        simp only [G₂, Functor.comp_map, Functor.prod_map,
          rightAssocTensor_map,
          tensorHom_comp_tensorHom,
          Category.id_comp] }
  let z : (P, Q, N) ≅ (L, M, V) := e.prod (e'.prod e'')
  have hz : IsIso (F₁.map z.hom) := inferInstance
  apply (cancel_epi (F₁.map z.hom)).mp
  have hh : (α ≫ c₂).app (P, Q, N) = (c₁ ≫ β).app (P, Q, N) := by
    simpa only [α, β, c₁, c₂, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, associatorNatIso_hom_app, Functor.prod_obj,
      F₁, G₂, Functor.comp_obj, leftAssocTensor_obj, rightAssocTensor_obj, tensor_obj,
      CoefficientClosedStructure.tensor, tensor_map,
      id_tensorHom, tensorHom_id, Category.assoc] using h
  have hh' := congrArg (fun f ↦ f ≫ G₂.map z.hom) hh
  rw [← (α ≫ c₂).naturality, ← (c₁ ≫ β).naturality] at hh'
  simpa only [α, β, c₁, c₂, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, associatorNatIso_hom_app, Functor.prod_obj,
      F₁, G₂, Functor.comp_obj, leftAssocTensor_obj, rightAssocTensor_obj, tensor_obj,
      CoefficientClosedStructure.tensor, tensor_map,
    id_tensorHom, tensorHom_id, Category.assoc] using hh'

private theorem left_unit_of_iso
    (η : F.obj S.monoidal.tensorUnit ≅ T.monoidal.tensorUnit)
    {X Y : B} (e : X ≅ Y)
    (h : μ.hom.app (S.monoidal.tensorUnit, X) ≫
      T.tensor.map (X := (F.obj S.monoidal.tensorUnit, F.obj X))
        (Y := (T.monoidal.tensorUnit, F.obj X)) (η.hom, 𝟙 _) ≫
          (T.monoidal.leftUnitor (F.obj X)).hom =
        F.map (S.monoidal.leftUnitor X).hom) :
    μ.hom.app (S.monoidal.tensorUnit, Y) ≫
      T.tensor.map (X := (F.obj S.monoidal.tensorUnit, F.obj Y))
        (Y := (T.monoidal.tensorUnit, F.obj Y)) (η.hom, 𝟙 _) ≫
          (T.monoidal.leftUnitor (F.obj Y)).hom =
        F.map (S.monoidal.leftUnitor Y).hom := by
  let := S.monoidal
  let := T.monoidal
  apply (cancel_epi (F.map (𝟙_ B ◁ e.hom))).mp
  have hn := rho_naturality S T F μ (𝟙_ B) X (𝟙_ B) Y (𝟙 _) e.hom
  simp only [rho, CoefficientClosedStructure.tensor, tensor_map, Functor.map_id,
    id_tensorHom] at hn
  simp only [CoefficientClosedStructure.tensor, tensor_map, tensorHom_id]
  change F.map (𝟙_ B ◁ e.hom) ≫ μ.hom.app (𝟙_ B, Y) ≫
    η.hom ▷ F.obj Y ≫ (λ_ (F.obj Y)).hom =
      F.map (𝟙_ B ◁ e.hom) ≫ F.map (λ_ Y).hom
  erw [reassoc_of% hn]
  have ht : F.obj (𝟙_ B) ◁ F.map e.hom ≫ η.hom ▷ F.obj Y =
      η.hom ▷ F.obj X ≫ 𝟙_ A ◁ F.map e.hom := by
    simp only [← tensorHom_id, ← id_tensorHom, tensorHom_comp_tensorHom,
      Category.id_comp, Category.comp_id]
  rw [reassoc_of% ht, MonoidalCategory.leftUnitor_naturality]
  have hh : μ.hom.app (𝟙_ B, X) ≫ η.hom ▷ F.obj X ≫ (λ_ (F.obj X)).hom =
      F.map (λ_ X).hom := by
    simpa only [CoefficientClosedStructure.tensor, tensor_map, tensorHom_id] using h
  rw [← F.map_comp, MonoidalCategory.leftUnitor_naturality, F.map_comp]
  simpa only [Category.assoc, Iso.app_hom, Functor.comp_obj,
    CoefficientClosedStructure.tensor, tensor_obj] using
      congrArg (fun f ↦ f ≫ F.map e.hom) hh

private theorem right_unit_of_iso
    (η : F.obj S.monoidal.tensorUnit ≅ T.monoidal.tensorUnit)
    {X Y : B} (e : X ≅ Y)
    (h : μ.hom.app (X, S.monoidal.tensorUnit) ≫
      T.tensor.map (X := (F.obj X, F.obj S.monoidal.tensorUnit))
        (Y := (F.obj X, T.monoidal.tensorUnit)) (𝟙 _, η.hom) ≫
          (T.monoidal.rightUnitor (F.obj X)).hom =
        F.map (S.monoidal.rightUnitor X).hom) :
    μ.hom.app (Y, S.monoidal.tensorUnit) ≫
      T.tensor.map (X := (F.obj Y, F.obj S.monoidal.tensorUnit))
        (Y := (F.obj Y, T.monoidal.tensorUnit)) (𝟙 _, η.hom) ≫
          (T.monoidal.rightUnitor (F.obj Y)).hom =
        F.map (S.monoidal.rightUnitor Y).hom := by
  let := S.monoidal
  let := T.monoidal
  apply (cancel_epi (F.map (e.hom ▷ 𝟙_ B))).mp
  have hn := rho_naturality S T F μ X (𝟙_ B) Y (𝟙_ B) e.hom (𝟙 _)
  simp only [rho, CoefficientClosedStructure.tensor, tensor_map, Functor.map_id,
    tensorHom_id] at hn
  simp only [CoefficientClosedStructure.tensor, tensor_map, id_tensorHom]
  change F.map (e.hom ▷ 𝟙_ B) ≫ μ.hom.app (Y, 𝟙_ B) ≫
    F.obj Y ◁ η.hom ≫ (ρ_ (F.obj Y)).hom =
      F.map (e.hom ▷ 𝟙_ B) ≫ F.map (ρ_ Y).hom
  erw [reassoc_of% hn]
  have ht : F.map e.hom ▷ F.obj (𝟙_ B) ≫ F.obj Y ◁ η.hom =
      F.obj X ◁ η.hom ≫ F.map e.hom ▷ 𝟙_ A := by
    simp only [← tensorHom_id, ← id_tensorHom, tensorHom_comp_tensorHom,
      Category.id_comp, Category.comp_id]
  rw [reassoc_of% ht, MonoidalCategory.rightUnitor_naturality]
  have hh : μ.hom.app (X, 𝟙_ B) ≫ F.obj X ◁ η.hom ≫ (ρ_ (F.obj X)).hom =
      F.map (ρ_ X).hom := by
    simpa only [CoefficientClosedStructure.tensor, tensor_map, id_tensorHom] using h
  rw [← F.map_comp, MonoidalCategory.rightUnitor_naturality, F.map_comp]
  simpa only [Category.assoc, Iso.app_hom, Functor.comp_obj,
    CoefficientClosedStructure.tensor, tensor_obj] using
      congrArg (fun f ↦ f ≫ F.map e.hom) hh

private theorem symmetry_of_iso
    (β : @SymmetricCategory B _ S.monoidal)
    (β' : @SymmetricCategory A _ T.monoidal)
    {X Y X' Y' : B} (e : X ≅ X') (e' : Y ≅ Y')
    (h : F.map (β.toBraidedCategory.braiding X Y).hom ≫ μ.hom.app (Y, X) =
      μ.hom.app (X, Y) ≫ (β'.toBraidedCategory.braiding (F.obj X) (F.obj Y)).hom) :
    F.map (β.toBraidedCategory.braiding X' Y').hom ≫ μ.hom.app (Y', X') =
      μ.hom.app (X', Y') ≫
        (β'.toBraidedCategory.braiding (F.obj X') (F.obj Y')).hom := by
  let := S.monoidal
  let := T.monoidal
  let : SymmetricCategory B := β
  let : SymmetricCategory A := β'
  apply (cancel_epi (F.map (e.hom ⊗ₘ e'.hom))).mp
  change F.map (e.hom ⊗ₘ e'.hom) ≫ F.map (β_ X' Y').hom ≫ _ =
    F.map (e.hom ⊗ₘ e'.hom) ≫ μ.hom.app (X', Y') ≫ (β_ _ _).hom
  rw [← Functor.map_comp_assoc, BraidedCategory.braiding_naturality,
    Functor.map_comp, Category.assoc]
  have hn := rho_naturality S T F μ Y X Y' X' e'.hom e.hom
  have hn' := rho_naturality S T F μ X Y X' Y' e.hom e'.hom
  simp only [rho, CoefficientClosedStructure.tensor, tensor_map] at hn hn'
  simp only [Functor.prod_obj]
  erw [hn, reassoc_of% hn', ← Category.assoc, h, Category.assoc,
    BraidedCategory.braiding_naturality]
  rfl

end Transport

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

variable {D : Type d} [Category.{vd} D] (J' : GrothendieckTopology D)
  [HasSheafify J' AddCommGrpCat.{max d vd s}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{max d vd s}]
  (R' : Sheaf J' CommRingCat.{max d vd s})
  (U : RingedTensorModules.{c, v, r} J R ⥤ RingedTensorModules.{d, vd, s} J' R')
  [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]

variable [HasDerivedCategory.{wb} (RingedTensorModules.{c, v, r} J R)]
  [HasDerivedCategory.{wa} (RingedTensorModules.{d, vd, s} J' R')]
  [∀ I : Type (max c v r), PreservesLimitsOfShape (Discrete I) U]
  [U.PreservesKInjectiveComplexes]
  (u : Underived.{c, v, r, d, vd, s} J R J' R' U)
  (SB : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, wb} J R))
  (TB : CoefficientTensorModels.{r, c, v, wb} J R SB)
  (βB : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, r} J R))
    _ SB.monoidal)
  (cB : RingedDerivedTensorCoherence.{c, v, r, wb} J R SB TB βB)
  (SA : CoefficientClosedStructure (derivedInternalHomOfUniverses.{d, vd, s, wa} J' R'))
  (TA : CoefficientTensorModels.{s, d, vd, wa} J' R' SA)
  (βA : @SymmetricCategory (DerivedCategory (RingedTensorModules.{d, vd, s} J' R'))
    _ SA.monoidal)
  (cA : RingedDerivedTensorCoherence.{d, vd, s, wa} J' R' SA TA βA)

private theorem flat_representative (X : DerivedCategory (RingedTensorModules.{c, v, r} J R)) :
    ∃ (P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
      (_hP : P.IsKFlatIndependentCoefficients)
      (_fP : ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
        (R := R) (P.X p)), Nonempty (DerivedCategory.Q.obj P ≅ X) := by
  obtain ⟨P, f, hP, fP, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R)
      (DerivedCategory.Q.objPreimage X)
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hf
  refine ⟨P, hP, ?_, ⟨asIso (DerivedCategory.Q.map f) ≪≫
    DerivedCategory.Q.objObjPreimageIso X⟩⟩
  intro n
  unfold SheafOfModules.IsFlatOnSite
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R (P.X n)).symm (fP n)

attribute [local irreducible] coefficientTotalTensor tensorSummand ringedForgetTensorUnitIso

-- Assemble the four transported constraints without unfolding their model constructions.
/-- A tensor comparison already constructed and normalized on flat-term K-flat models
preserves the structural constraints of the two fixed derived tensor presentations.
This statement constructs neither the chain comparison nor its derived extension and
makes no uniqueness assertion.

Source: Stacks Project, sites-cohomology.tex, Tag 0FPT
(`lemma-symmetric-monoidal-derived`), with Tags 06YS, 06YU and 0G7D;
step 4 of lem-sf-ringed-forget-tensor-descent
(blueprint: lem-sf-ringed-forget-tensor-coherence).

Proof: define the unit comparison by composing the image of cB.unitIso, the
termwise exact-functor factor, the single-complex comparison, the degree-zero
image of u.coherence.unit, and cA.unitIso inverse. Its normalization follows by
cancelling cA.unitIso. For flat-term K-flat P,Q,N, their total tensor complexes
are flat-term K-flat (lem-pur-kflat-total-tensor-model); their termwise U-images
have the same properties by hypothesis. Apply the representative square to the
inner and outer tensor pairs. Apply the associator-model equations of cB and cA
and naturality of the representative comparisons. Cancel these isomorphisms to
reduce the derived associativity square to an equality of localized chain maps.
Before localization it suffices to restrict to each triple coproduct summand:
the summand law for chain changes the two paths into the underived associativity
square u.coherence.associativity. These equalities are equalities of sheaf maps;
the universal property of the sheafified tensor and its locally generating pure
tensors justifies the structural-model identifications without a global-pure-tensor
assumption. For the unit squares use the left- and right-unitor models of cB and
cA; on each summand in degree n they are u.coherence.left_unit and right_unit.
For symmetry use cB.symmetry_model and cA.symmetry_model: on (p,q) both paths
are the underived symmetry square multiplied by (-1)^(pq), and U preserves this
integer multiple by additivity. Finally every derived object is isomorphic to a
flat-term K-flat representative by lem-pc-kflat-resolution. Naturality of the
tensor comparison, associators, unitors and braidings transports each checked
square along these objectwise isomorphisms, proving the four constraints for all
derived objects. -/
theorem ringed_forget_tensor_coherence
    (hU : ∀ P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ,
      P.IsKFlatIndependentCoefficients →
      (∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
        (R := R) (P.X p)) →
      CochainComplex.IsKFlatIndependentCoefficients (R := R')
        ((U.mapHomologicalComplex (.up ℤ)).obj P) ∧
      ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{d, vd, max d vd s, max d vd s}
        (R := R') (U.obj (P.X p)))
    (chain : coefficientTotalTensor.{r, c, v} J R ⋙ U.mapHomologicalComplex (.up ℤ) ≅
      ((U.mapHomologicalComplex (.up ℤ)).prod (U.mapHomologicalComplex (.up ℤ))) ⋙
        coefficientTotalTensor.{s, d, vd} J' R')
    (summand : ∀ (P Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
      (p q n : ℤ) (hpq : p + q = n),
      U.map (tensorSummand.{c, v, r} J R P Q p q n hpq) ≫ (chain.hom.app (P, Q)).f n =
        u.tensor.hom.app (P.X p, Q.X q) ≫
          tensorSummand.{d, vd, s} J' R' ((U.mapHomologicalComplex (.up ℤ)).obj P)
            ((U.mapHomologicalComplex (.up ℤ)).obj Q) p q n hpq)
    (μ : SB.tensor ⋙ U.mapDerivedCategory ≅
      (U.mapDerivedCategory.prod U.mapDerivedCategory) ⋙ SA.tensor)
    (hμ : RepresentativeModel.{c, v, r, d, vd, s, wb, wa}
      J R J' R' U SB TB SA TA chain μ.hom) :
    ∃ c : TensorCoherence SB.monoidal SA.monoidal βB βA U.mapDerivedCategory μ,
      c.unit.hom ≫ cA.unitIso.hom =
        U.mapDerivedCategory.map cB.unitIso.hom ≫
          U.mapDerivedCategoryFactors.hom.app (ringedTensorUnitComplex.{c, v, r} J R) ≫
          DerivedCategory.Q.map
            ((HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).hom.app
              (SheafOfModules.unit ((sheafCompose J
                (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))) ≫
          DerivedCategory.Q.map
            ((HomologicalComplex.single _ (.up ℤ) (0 : ℤ)).map (u.coherence.unit).hom) := by
  let η := ringedForgetTensorUnitIso J R J' R' U u SB TB βB cB SA TA βA cA
  refine ⟨⟨η, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro X Y Z
    obtain ⟨P, hP, fP, ⟨e⟩⟩ := flat_representative.{c, v, r, wb} J R X
    obtain ⟨Q, hQ, fQ, ⟨e'⟩⟩ := flat_representative.{c, v, r, wb} J R Y
    obtain ⟨N, hN, fN, ⟨e''⟩⟩ := flat_representative.{c, v, r, wb} J R Z
    apply associator_of_iso SB SA U.mapDerivedCategory μ e e' e''
    exact ringed_forget_tensor_associator_representatives.{c, v, r, d, vd, s, wb, wa}
      J R J' R' U u SB TB βB cB SA TA βA cA hU chain summand μ hμ
      P Q N hP fP hQ fQ hN fN
  · intro X
    obtain ⟨P, hP, fP, ⟨e⟩⟩ := flat_representative.{c, v, r, wb} J R X
    apply left_unit_of_iso SB SA U.mapDerivedCategory μ η e
    exact (ringed_forget_tensor_unit_representatives.{c, v, r, d, vd, s, wb, wa}
      J R J' R' U u SB TB βB cB SA TA βA cA hU chain summand μ hμ P hP fP).1
  · intro X
    obtain ⟨P, hP, fP, ⟨e⟩⟩ := flat_representative.{c, v, r, wb} J R X
    apply right_unit_of_iso SB SA U.mapDerivedCategory μ η e
    exact (ringed_forget_tensor_unit_representatives.{c, v, r, d, vd, s, wb, wa}
      J R J' R' U u SB TB βB cB SA TA βA cA hU chain summand μ hμ P hP fP).2
  · intro X Y
    obtain ⟨P, hP, fP, ⟨e⟩⟩ := flat_representative.{c, v, r, wb} J R X
    obtain ⟨Q, hQ, fQ, ⟨e'⟩⟩ := flat_representative.{c, v, r, wb} J R Y
    apply symmetry_of_iso SB SA U.mapDerivedCategory μ βB βA e e'
    exact ringed_forget_tensor_symmetry_representatives.{c, v, r, d, vd, s, wb, wa}
      J R J' R' U u SB TB βB cB SA TA βA cA hU chain summand μ hμ P Q hP fP hQ fQ
  · dsimp only [η]
    unfold ringedForgetTensorUnitIso
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom,
      ringedTensorUnitComplex, Functor.comp_obj, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]

end CategoryTheory.RingedForgetTensorTransposition
