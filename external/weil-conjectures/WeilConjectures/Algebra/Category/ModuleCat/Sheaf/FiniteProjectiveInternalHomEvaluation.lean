/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree

/-! # Evaluation for a finite projective sheaf of modules

Source: Stacks Project, Cohomology of Sheaves, Tag 08DQ, proof of
`lemma-dual-perfect-complex`, finite-free and direct-summand calculation.
(blueprint: lem-pc-finite-projective-internal-hom-evaluation).
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SheafOfModules

attribute [local instance] monoidalCategory symmetricCategory

private theorem homObjMap_sum {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (R : Sheaf J CommRingCat.{u})
    {I : Type*} (s : Finset I)
    {E F N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : I → (E ⟶ F)) :
    homObjMap (∑ j ∈ s, f j) (𝟙 N) = ∑ j ∈ s, homObjMap (f j) (𝟙 N) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := (((homFunctor R).flip.obj N).map_zero (Opposite.op F) (Opposite.op E))
    simpa using h
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj, homObjMap_add_left, ih]

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

/-- The canonical map sending `b tensor phi` to `e ↦ b * phi(e)`.
Source: Stacks Project, Tag 08DQ, proof of `lemma-dual-perfect-complex`.
(blueprint: lem-pc-finite-projective-internal-hom-evaluation). -/
def moduleDualEvaluation (R : Sheaf J CommRingCat.{u})
    (E B : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    B ⊗ homObj E (𝟙_ _) ⟶ homObj E B :=
  tensorHomEquiv E _ B
    ((β_ E (B ⊗ homObj E (𝟙_ _))).hom ≫
      (α_ B (homObj E (𝟙_ _)) E).hom ≫
      B ◁ ((β_ (homObj E (𝟙_ _)) E).hom ≫
        (tensorHomEquiv E (homObj E (𝟙_ _)) (𝟙_ _)).symm (𝟙 _)) ≫
      (ρ_ B).hom)

private theorem evaluation_precomposition (R : Sheaf J CommRingCat.{u})
    {E F : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : E ⟶ F) :
    E ◁ homObjMap f (𝟙 (𝟙_ _)) ≫
        (tensorHomEquiv E (homObj E (𝟙_ _)) (𝟙_ _)).symm (𝟙 _) =
      f ▷ homObj F (𝟙_ _) ≫
        (tensorHomEquiv F (homObj F (𝟙_ _)) (𝟙_ _)).symm (𝟙 _) := by
  apply (tensorHomEquiv E _ _).injective
  rw [tensorHomEquiv_whiskerLeft_comp, tensorHomEquiv_whiskerRight_comp]
  simp

private theorem moduleDualEvaluation_naturality (R : Sheaf J CommRingCat.{u})
    {E F : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (B : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (f : E ⟶ F) :
    B ◁ homObjMap f (𝟙 (𝟙_ _)) ≫ moduleDualEvaluation R E B =
      moduleDualEvaluation R F B ≫ homObjMap f (𝟙 B) := by
  unfold moduleDualEvaluation
  rw [← tensorHomEquiv_whiskerLeft_comp, ← tensorHomEquiv_whiskerRight_comp]
  apply (tensorHomEquiv E _ B).congr_arg
  rw [BraidedCategory.braiding_naturality_right_assoc,
    associator_naturality_middle_assoc, ← whiskerLeft_comp_assoc,
    BraidedCategory.braiding_naturality_left_assoc,
    evaluation_precomposition]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [BraidedCategory.braiding_naturality_left_assoc,
    associator_naturality_right_assoc]
  simp only [← whiskerLeft_comp_assoc, BraidedCategory.braiding_naturality_right_assoc]

private theorem evaluation_shuffle {A : Type*} [Category* A] [MonoidalCategory A]
    [SymmetricCategory A] (E B D : A) (ev : E ⊗ D ⟶ 𝟙_ A) :
    (β_ E (B ⊗ D)).hom ≫ (α_ B D E).hom ≫
        B ◁ ((β_ D E).hom ≫ ev) ≫ (ρ_ B).hom =
      E ◁ (β_ B D).hom ≫ (α_ E D B).inv ≫ ev ▷ B ≫ (λ_ B).hom := by
  rw [← braiding_rightUnitor B, BraidedCategory.braiding_naturality_left_assoc]
  simp only [BraidedCategory.braiding_tensor_left_hom,
    BraidedCategory.braiding_tensor_right_hom, Category.assoc, whiskerLeft_comp,
    Iso.inv_hom_id_assoc]
  simp only [← whiskerLeft_comp_assoc, SymmetricCategory.symmetry_assoc]
  simp only [SymmetricCategory.symmetry, whiskerLeft_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem moduleDualEvaluation_comparison (R : Sheaf J CommRingCat.{u})
    (E B : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    letI := monoidalClosed (R := R)
    moduleDualEvaluation R E B = (β_ B (homObj E (𝟙_ _))).hom ≫
      MonoidalClosed.ihomUnitTensorToIhom E B := by
  let := monoidalClosed (R := R)
  apply MonoidalClosed.uncurry_injective
  rw [uncurry_eq_tensorHomEquiv_symm]
  simp only [moduleDualEvaluation, Equiv.symm_apply_apply]
  rw [← uncurry_eq_tensorHomEquiv_symm,
    MonoidalClosed.uncurry_natural_left, MonoidalClosed.ihomUnitTensorToIhom,
    MonoidalClosed.uncurry_curry, ihom_ev_app]
  rw [uncurry_eq_tensorHomEquiv_symm]
  exact evaluation_shuffle E B (homObj E (𝟙_ _))
    ((tensorHomEquiv E (homObj E (𝟙_ _)) (𝟙_ _)).symm (𝟙 _))

private theorem unit_evaluation (R : Sheaf J CommRingCat.{u})
    (B : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    IsIso (moduleDualEvaluation R (𝟙_ _) B) := by
  let := monoidalClosed (R := R)
  rw [moduleDualEvaluation_comparison]
  have := MonoidalClosed.isIso_ihomUnitTensorToIhom (𝟙_ _) (𝟙_ _) B
  infer_instance

private theorem whiskerLeft_sum (R : Sheaf J CommRingCat.{u})
    {I : Type*} (s : Finset I)
    (B : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    {E F : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : I → (E ⟶ F)) :
    B ◁ (∑ j ∈ s, f j) = ∑ j ∈ s, B ◁ f j := by
  exact (tensorLeft B).map_sum f s

private theorem free_evaluation (R : Sheaf J CommRingCat.{u})
    (m : ℕ) (B : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    IsIso (moduleDualEvaluation R
      (free (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
        (ULift.{u} (Fin m))) B) := by
  classical
  let I := ULift.{u} (Fin m)
  let U : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) := 𝟙_ _
  let e : (Limits.biproduct (fun _ : I ↦ U)) ≅ free (R :=
      (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) I :=
    Limits.biproduct.isoCoproduct _
  let i (j : I) := Limits.biproduct.ι (fun _ : I ↦ U) j ≫ e.hom
  let p (j : I) := e.inv ≫ Limits.biproduct.π (fun _ : I ↦ U) j
  have ht : ∑ j, p j ≫ i j = 𝟙 _ := by
    simp only [p, i, Category.assoc, ← Preadditive.comp_sum]
    simp only [← Category.assoc]
    rw [← Preadditive.sum_comp,
      Limits.IsBilimit.total (Limits.biproduct.isBilimit (fun _ : I ↦ U))]
    simp
  have := unit_evaluation R B
  let q := ∑ j, homObjMap (i j) (𝟙 B) ≫ inv (moduleDualEvaluation R U B) ≫
    B ◁ homObjMap (p j) (𝟙 (𝟙_ _))
  have h₁ : moduleDualEvaluation R (free I) B ≫ q = 𝟙 _ := by
    dsimp only [q]
    rw [Preadditive.comp_sum]
    have hj (j : I) : moduleDualEvaluation R (free I) B ≫
        (homObjMap (i j) (𝟙 B) ≫ inv (moduleDualEvaluation R U B) ≫
          B ◁ homObjMap (p j) (𝟙 (𝟙_ _))) =
        B ◁ homObjMap (p j ≫ i j) (𝟙 (𝟙_ _)) := by
      rw [← Category.assoc, ← moduleDualEvaluation_naturality R B (i j)]
      simp only [Category.assoc, IsIso.hom_inv_id_assoc]
      rw [← whiskerLeft_comp, homObjMap_comp_homObjMap, Category.comp_id]
    simp only [hj]
    rw [← whiskerLeft_sum R, ← homObjMap_sum R, ht]
    simp
  have h₂ : q ≫ moduleDualEvaluation R (free I) B = 𝟙 _ := by
    dsimp only [q]
    rw [Preadditive.sum_comp]
    simp only [Category.assoc, moduleDualEvaluation_naturality R B,
      IsIso.inv_hom_id_assoc, homObjMap_comp_homObjMap, Category.comp_id]
    rw [← homObjMap_sum R, ht]
    simp
  exact ⟨⟨q, h₁, h₂⟩⟩

/-- Canonical tensor-dual evaluation is invertible for a retract of a finite free sheaf.
Source: Stacks Project, Tag 08DQ, proof of `lemma-dual-perfect-complex`.
(blueprint: lem-pc-finite-projective-internal-hom-evaluation).

Proof: for the free sheaf on `Fin m`, internal Hom is the finite product of `m`
copies of the target, and the dual is the free sheaf on the same basis. Tensoring
with that free sheaf is the finite coproduct of `m` copies of B. The finite
product/coproduct identification sends the evaluation map to the identity on
these copies: its j-th coordinate evaluates the j-th basis vector. For the
retraction `i ≫ p = id`, precomposition induces retractions on both the dual
and Hom. Naturality of evaluation gives a morphism of the resulting split
idempotents. Its inverse for the free sheaf commutes with these idempotents,
so restrict it by the inclusion and projection to obtain the inverse for E.
The two inverse equations reduce to the free inverse equations and `i ≫ p = id`.
For `m = 0` both free objects are zero; the same retraction argument applies.
-/
theorem isIso_moduleDualEvaluation_of_retract (R : Sheaf J CommRingCat.{u})
    (E B : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (hE : ∃ m : ℕ,
      ∃ (i : E ⟶ free (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
          (ULift.{u} (Fin m)))
        (p : free (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
          (ULift.{u} (Fin m)) ⟶ E), i ≫ p = 𝟙 E) :
    IsIso (moduleDualEvaluation R E B) := by
  obtain ⟨m, i, p, hip⟩ := hE
  have := free_evaluation R m B
  let F := free (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
    (ULift.{u} (Fin m))
  let q := homObjMap p (𝟙 B) ≫ inv (moduleDualEvaluation R F B) ≫
    B ◁ homObjMap i (𝟙 (𝟙_ _))
  have h₁ : moduleDualEvaluation R E B ≫ q = 𝟙 _ := by
    dsimp only [q, F]
    rw [← Category.assoc, ← moduleDualEvaluation_naturality R B p]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    rw [← whiskerLeft_comp, homObjMap_comp_homObjMap, hip]
    simp
  have h₂ : q ≫ moduleDualEvaluation R E B = 𝟙 _ := by
    dsimp only [q, F]
    simp only [Category.assoc]
    rw [moduleDualEvaluation_naturality R B i]
    simp [hip]
  exact ⟨⟨q, h₁, h₂⟩⟩


end SheafOfModules
