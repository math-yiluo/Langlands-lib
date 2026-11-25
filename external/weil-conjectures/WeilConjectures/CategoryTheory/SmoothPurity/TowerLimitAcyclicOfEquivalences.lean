/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # Transporting tower-limit acyclicity through equivalences

Source: Stacks Project, Cohomology on Sites, Tags 0A07 and 0D6E.
(blueprint: lem-pur-tower-limit-acyclic-of-equivalences).
-/

@[expose] public section
set_option autoImplicit false
universe a av b bv c cv d dv
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

private theorem quasiIsoOfIso
    {A D : Type*} [Category A] [Category D] [Abelian A] [Abelian D]
    (F G : A ⥤ D) [F.Additive] [G.Additive] (e : F ≅ G)
    {I K : CochainComplex A ℤ} (j : I ⟶ K)
    [QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map j)] :
    QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map j) := by
  let ec := NatIso.mapHomologicalComplex e (.up ℤ)
  have heq : (G.mapHomologicalComplex (.up ℤ)).map j =
      ec.inv.app I ≫ (F.mapHomologicalComplex (.up ℤ)).map j ≫ ec.hom.app K := by
    apply (cancel_epi (ec.hom.app I)).mp
    simp only [Iso.hom_inv_id_app_assoc]
    exact (ec.hom.naturality j).symm
  rw [heq]
  infer_instance

/-- Inverse-limit acyclicity for a functor on strict towers is invariant under
compatible equivalences of its source and target abelian categories.
Source: Stacks Project, Tags 0A07 and 0D6E, transport of the resolution criterion.
(blueprint: lem-pur-tower-limit-acyclic-of-equivalences).

Proof: whisker the two equivalences by the tower index. They remain additive exact
equivalences and preserve K-injectivity and quasi-isomorphisms. The supplied
comparison, lifted to towers and complexes using composition isomorphisms,
transports the resolution map to the model categories. Apply the model acyclicity
criterion and cancel the inverse-limit image of the comparison isomorphism.
The target equivalence preserves limits; its canonical limit comparison transfers
this result to its image of the original inverse-limit map. Exact equivalences
reflect quasi-isomorphisms, giving the result. This includes zero categories and
zero complexes and uses no exactness of countable products. -/
theorem towerLimitAcyclicOfEquivalences
    {A : Type a} [Category.{av} A] [Abelian A]
    {B : Type b} [Category.{bv} B] [Abelian B]
    {C : Type c} [Category.{cv} C] [Abelian C]
    {D : Type d} [Category.{dv} D] [Abelian D]
    [HasLimitsOfShape ℕᵒᵖ B] [HasLimitsOfShape ℕᵒᵖ D]
    [(lim : (ℕᵒᵖ ⥤ B) ⥤ B).Additive] [(lim : (ℕᵒᵖ ⥤ D) ⥤ D).Additive]
    (EX : A ≌ C) (EY : B ≌ D) (P : A ⥤ B) [P.Additive]
    (Q : C ⥤ D) [Q.Additive] (em : P ⋙ EY.functor ≅ EX.functor ⋙ Q)
    (hq : ∀ (I : CochainComplex (ℕᵒᵖ ⥤ C) ℤ), I.IsKInjective →
      ∀ (T : CochainComplex (ℕᵒᵖ ⥤ D) ℤ), T.IsKInjective →
      ∀ (q : ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj Q).mapHomologicalComplex
        (.up ℤ)).obj I) ⟶ T), QuasiIso q →
      QuasiIso (((lim : (ℕᵒᵖ ⥤ D) ⥤ D).mapHomologicalComplex (.up ℤ)).map q))
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (hI : I.IsKInjective)
    (T : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (hT : T.IsKInjective)
    (j : ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj P).mapHomologicalComplex
      (.up ℤ)).obj I) ⟶ T) [QuasiIso j] :
    QuasiIso (((lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ)).map j) := by
  have : EX.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : EY.functor.Additive := Functor.additive_of_preserves_binary_products _
  let VX := (Functor.whiskeringRight ℕᵒᵖ _ _).obj EX.functor
  let VY := (Functor.whiskeringRight ℕᵒᵖ _ _).obj EY.functor
  let I' := (VX.mapHomologicalComplex (.up ℤ)).obj I
  let T' := (VY.mapHomologicalComplex (.up ℤ)).obj T
  have := hI
  have := hT
  have hI' : CochainComplex.IsKInjective I' := inferInstance
  have hT' : CochainComplex.IsKInjective T' := inferInstance
  let ep := Functor.whiskeringRightObjCompIso (E := ℕᵒᵖ) P EY.functor ≪≫
    (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso em ≪≫
      (Functor.whiskeringRightObjCompIso (E := ℕᵒᵖ) EX.functor Q).symm
  let ec := Functor.mapHomologicalComplexCompIso ep (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (VX ⋙ (Functor.whiskeringRight ℕᵒᵖ _ _).obj Q)) (.up ℤ)).symm
  let j' : ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj Q).mapHomologicalComplex
      (.up ℤ)).obj I') ⟶ T' := ec.inv.app I ≫ (VY.mapHomologicalComplex (.up ℤ)).map j
  have : QuasiIso j' := by dsimp only [j']; infer_instance
  have hq₀ := hq I' hI' T' hT' j' inferInstance
  have hq₁ : QuasiIso (((VY ⋙ lim).mapHomologicalComplex (.up ℤ)).map j) := by
    dsimp only [j'] at hq₀
    rw [Functor.map_comp] at hq₀
    exact (quasiIso_iff_comp_left _ _).mp hq₀
  have hq₂ : QuasiIso (((lim ⋙ EY.functor).mapHomologicalComplex (.up ℤ)).map j) :=
    quasiIsoOfIso _ _ (preservesLimitNatIso EY.functor (J := ℕᵒᵖ)).symm j
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ EY.functor).mp hq₂

end CategoryTheory
