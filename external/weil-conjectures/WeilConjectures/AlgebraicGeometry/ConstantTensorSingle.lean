/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.BifunctorSingleComparison
public import WeilConjectures.AlgebraicGeometry.ConstantKoszulQuotientAugmentation
import WeilConjectures.CategoryTheory.FlatConstantTensorProZeroCones

/-! # Single-complex tensor comparisons for ordinary reduction towers

Source: Stacks Project, Modules on Sites, Tag 03EK; Cohomology on Sites, total tensor.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace CategoryTheory.ConstantCompletion.TensorComparison
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
attribute [local instance] flatConstantCochainMonoidal flatConstantCochainMonoidalStruct
  SheafOfModules.monoidalCategory
  Functor.preservesZeroMorphisms_of_additive

/-- The termwise tensor of the unit complex is the single quotient complex.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
@[irreducible] def quotientUnitIso
    (O : Sheaf J CommRingCat.{u})
    (Q : Mod O) :
    ((tensorRight Q).mapHomologicalComplex (.up ℤ)).obj (𝟙_ _) ≅
      (HomologicalComplex.single _ (.up ℤ) 0).obj Q :=
  (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) Q (𝟙_ _)).symm ≪≫
    λ_ ((HomologicalComplex.single _ (.up ℤ) 0).obj Q)

/-- Total tensor with a termwise tensor of the unit is ordinary termwise tensor.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
@[irreducible] def quotientTensorIso
    (O : Sheaf J CommRingCat.{u})
    (Q : Mod O) (P : CochainComplex (Mod O) ℤ) :
    P ⊗ ((tensorRight Q).mapHomologicalComplex (.up ℤ)).obj (𝟙_ _) ≅
      ((tensorRight Q).mapHomologicalComplex (.up ℤ)).obj P :=
  (tensorLeft P).mapIso (quotientUnitIso J O Q) ≪≫
    CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) Q P

private lemma singleTensor_naturality
    (O : Sheaf J CommRingCat.{u})
    (P : CochainComplex (Mod O) ℤ)
    {Q Q' : Mod O} (f : Q ⟶ Q') :
    P ◁ (HomologicalComplex.single _ (.up ℤ) 0).map f ≫
        (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) Q' P).hom =
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) Q P).hom ≫
        (NatTrans.mapHomologicalComplex ((curriedTensor _).flip.map f) (.up ℤ)).app P := by
  apply (cancel_epi
    (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) Q P).inv).1
  apply (cancel_mono
    (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) Q' P).inv).1
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id]
  exact (CochainComplex.mapBifunctorSingle₂Iso_inv_naturality₂
    (curriedTensor _) f P).symm

private lemma quotientUnitIso_naturality
    (O : Sheaf J CommRingCat.{u})
    {Q Q' : Mod O} (f : Q ⟶ Q') :
    (NatTrans.mapHomologicalComplex ((curriedTensor _).flip.map f) (.up ℤ)).app (𝟙_ _) ≫
        (quotientUnitIso J O Q').hom =
      (quotientUnitIso J O Q).hom ≫ (HomologicalComplex.single _ (.up ℤ) 0).map f := by
  apply (cancel_epi
    (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) Q (𝟙_ _)).hom).1
  unfold quotientUnitIso
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  erw [← Category.assoc, ← singleTensor_naturality J O, Category.assoc,
    Iso.hom_inv_id_assoc]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact leftUnitor_naturality _

private lemma quotientTensorIso_naturality
    (O : Sheaf J CommRingCat.{u})
    (P : CochainComplex (Mod O) ℤ)
    {Q Q' : Mod O} (f : Q ⟶ Q') :
    P ◁ (NatTrans.mapHomologicalComplex
        ((curriedTensor _).flip.map f) (.up ℤ)).app (𝟙_ _) ≫
          (quotientTensorIso J O Q' P).hom =
      (quotientTensorIso J O Q P).hom ≫
        (NatTrans.mapHomologicalComplex ((curriedTensor _).flip.map f) (.up ℤ)).app P := by
  unfold quotientTensorIso
  dsimp only [Iso.trans_hom, Functor.mapIso_hom]
  have hq := congrArg ((tensorLeft P).map) (quotientUnitIso_naturality J O f)
  simp only [Functor.map_comp] at hq
  calc
    _ = ((tensorLeft P).map
          ((NatTrans.mapHomologicalComplex ((curriedTensor _).flip.map f)
            (.up ℤ)).app (𝟙_ _)) ≫
          (tensorLeft P).map (quotientUnitIso J O Q').hom) ≫ _ :=
      (Category.assoc _ _ _).symm
    _ = ((tensorLeft P).map (quotientUnitIso J O Q).hom ≫
          (tensorLeft P).map ((HomologicalComplex.single _ (.up ℤ) 0).map f)) ≫ _ :=
      congrArg (fun z ↦ z ≫ _) hq
    _ = _ := by
      rw [Category.assoc, Category.assoc]
      exact congrArg (fun z ↦ (tensorLeft P).map (quotientUnitIso J O Q).hom ≫ z)
        (singleTensor_naturality J O P f)

/-- The tower of right tensor functors attached to a coefficient tower.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
def tensorTower (O : Sheaf J CommRingCat.{u}) (Q : ℕᵒᵖ ⥤ Mod O) :
    Mod O ⥤ ℕᵒᵖ ⥤ Mod O := (Q ⋙ (curriedTensor (Mod O)).flip).flip

/-- Tensor towers are additive by evaluation at every level.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
theorem tensorTower_additive (O : Sheaf J CommRingCat.{u})
    (Q : ℕᵒᵖ ⥤ Mod O) : (tensorTower J O Q).Additive := by
  constructor
  intro M N f g
  apply NatTrans.ext
  funext n
  exact (tensorRight (Q.obj n)).map_add

attribute [local instance] tensorTower_additive

/-- Tensoring the termwise coefficient tower at the cochain unit gives its value at P.

Source: Stacks 03EK and the total tensor convention of Cohomology on Sites.
(auxiliary; not a blueprint node).

Proof: identify termwise tensor of the unit with the quotient in degree zero by
single-factor total tensor and the left unitor. Tensor this identification with P,
then use single-factor total tensor again. Naturality in each quotient transition
is the naturality of the single-factor comparison and the left unitor. -/
def tensorTowerComparison (O : Sheaf J CommRingCat.{u})
    (Q : ℕᵒᵖ ⥤ Mod O) (P : Cx O) :
    (((tensorTower J O Q).mapHomologicalComplex (.up ℤ)).obj (𝟙_ (Cx O))).asFunctor ⋙
      tensorLeft P ≅
        (((tensorTower J O Q).mapHomologicalComplex (.up ℤ)).obj P).asFunctor :=
  NatIso.ofComponents (fun n ↦ quotientTensorIso J O (Q.obj n) P) (by
    intro m n f
    exact quotientTensorIso_naturality J O P (Q.map f))

end CategoryTheory.ConstantCompletion.TensorComparison
