/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import WeilConjectures.Algebra.Homology.RingTensorCohomology

/-! # Scalar compatibility of the canonical localization cohomology map

Source: Stacks Project, Tags 06Y6 and 0DJ8.
(blueprint: lem-pc-first-localization-cohomology-semilinear).
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory
open scoped TensorProduct ChangeOfRings

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace RingTensorCohomology

variable (R A Aq B D : Type u)
  [CommRing R] [CommRing A] [CommRing Aq] [CommRing B] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra A Aq] [Algebra R Aq]
  [IsScalarTower R A Aq]
  [Algebra (A ⊗[R] B) D] [Algebra (Aq ⊗[R] B) D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]

/-- Canonical cohomology map induced by the localization unit and universal counits.
Source: Stacks Project, Tag 06Y6.
(blueprint: lem-pc-first-localization-cohomology-semilinear). -/
noncomputable def localizationModelMap (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R Aq B ((extend A Aq).obj Q) D)
    (uQ : (restrict R A).obj Q ⟶ (restrict R Aq).obj ((extend A Aq).obj Q)) :
    (ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom).obj
        (L.cohomology i) ⟶
      (ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom).obj
        (K.cohomology i) :=
  let := L.universal
  let := K.universal
  let ζ := Functor.leftDerivedNatIso L.derived K.derived L.counit K.counit
    (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)) (Iso.refl _)
  (L.cohomologyIso i).hom ≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
      (L.derived.map (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map uQ)) ≫
        ζ.hom.app (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
            ((restrict R Aq).obj ((extend A Aq).obj Q))))) ≫
    (K.cohomologyIso i).inv

omit [IsScalarTower R A Aq] in
private theorem localizationModelMap_left (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R Aq B ((extend A Aq).obj Q) D)
    (uQ : (restrict R A).obj Q ⟶ (restrict R Aq).obj ((extend A Aq).obj Q))
    (huQ : ∀ (j : ℤ) (x : Q.X j), uQ.f j x = (1 : Aq) ⊗ₜ[A,algebraMap A Aq] x)
    (a : A) (x : L.cohomology i) :
    localizationModelMap R A Aq B D i Q L K uQ
        ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • x) =
      (Algebra.TensorProduct.includeLeft (S := R) (algebraMap A Aq a) : Aq ⊗[R] B) •
        localizationModelMap R A Aq B D i Q L K uQ x := by
  let := L.universal
  let := K.universal
  let ζ := Functor.leftDerivedNatIso L.derived K.derived L.counit K.counit
    (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)) (Iso.refl _)
  let V := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ) ⋙ DerivedCategory.Qh
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
  let v := V.map uQ
  let α := (restrict R A).map (a • 𝟙 Q)
  let β := (restrict R Aq).map ((algebraMap A Aq a) • 𝟙 ((extend A Aq).obj Q))
  have hab : α ≫ uQ = uQ ≫ β := by
    apply HomologicalComplex.Hom.ext
    funext j
    apply ModuleCat.hom_ext
    ext y
    change Q.X j at y
    change uQ.f j (show Q.X j from a • y) =
      (show ((extend A Aq).obj Q).X j from
        algebraMap A Aq a • (show ((extend A Aq).obj Q).X j from uQ.f j y))
    rw [huQ, huQ]
    let : Module A Aq := Module.compHom Aq (algebraMap A Aq)
    rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
    rfl
  have hd : L.derived.map (V.map α) ≫ L.derived.map v ≫ ζ.hom.app _ =
      L.derived.map v ≫ ζ.hom.app _ ≫ K.derived.map (V.map β) := by
    rw [← ζ.hom.naturality]
    simp only [← Category.assoc, ← Functor.map_comp]
    simpa only [v, Functor.map_comp] using
      congrArg (fun z ↦ L.derived.map (V.map z) ≫ ζ.hom.app _) hab
  have hc :
      (ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom).map
          ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) •
            𝟙 (L.cohomology i)) ≫ localizationModelMap R A Aq B D i Q L K uQ =
        localizationModelMap R A Aq B D i Q L K uQ ≫
          (ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom).map
            ((Algebra.TensorProduct.includeLeft (S := R) (algebraMap A Aq a) :
              Aq ⊗[R] B) • 𝟙 (K.cohomology i)) := by
    apply (cancel_mono (K.cohomologyIso i).hom).1
    dsimp only [localizationModelMap]
    simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [K.cohomologyIso_smul]
    simp only [← Category.assoc]
    rw [L.cohomologyIso_smul]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    change (L.cohomologyIso i).hom ≫ H.map (L.derived.map (V.map α)) ≫
        H.map (L.derived.map v) ≫ H.map (ζ.hom.app _) =
      (L.cohomologyIso i).hom ≫ H.map (L.derived.map v) ≫ H.map (ζ.hom.app _) ≫
        H.map (K.derived.map (V.map β))
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun z ↦ (L.cohomologyIso i).hom ≫ H.map z) hd
  exact congrArg (fun f ↦ f x) hc

/-- The unit-induced map respects the tensor coefficient actions.
Source: Stacks Project, Tag 06Y6, naturality of derived tensor and scalar multiplication.
(blueprint: lem-pc-first-localization-cohomology-semilinear).

Proof: the termwise unit intertwines multiplication by a on Q with multiplication
by its image on Aq tensor_A Q, by tensor balancing. Apply the homotopy quotient,
the derived functor and homology. Naturality of the universal counit comparison
intertwines these endomorphisms. The cohomologyIso_smul fields identify them with
includeLeft a on the source and includeLeft (algebraMap A Aq a) on the target.
The map is B-linear by construction, hence also intertwines includeRight b.
Tensor induction, using additivity and the product of the two actions on pure
tensors, proves the assertion for every tensor coefficient. -/
theorem localizationModelMap_smul (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R Aq B ((extend A Aq).obj Q) D)
    (uQ : (restrict R A).obj Q ⟶ (restrict R Aq).obj ((extend A Aq).obj Q))
    (huQ : ∀ (j : ℤ) (x : Q.X j), uQ.f j x = (1 : Aq) ⊗ₜ[A,algebraMap A Aq] x)
    (a : A ⊗[R] B) (x : L.cohomology i) :
    localizationModelMap R A Aq B D i Q L K uQ (a • x) =
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A Aq) (AlgHom.id R B) a •
        localizationModelMap R A Aq B D i Q L K uQ x := by
  let c := localizationModelMap R A Aq B D i Q L K uQ
  change c (a • x) =
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A Aq) (AlgHom.id R B) a • c x
  induction a using TensorProduct.inductionOn with
  | tmul a b =>
    rw [Algebra.TensorProduct.map_tmul]
    change c ((a ⊗ₜ[R] b) • x) = (algebraMap A Aq a ⊗ₜ[R] b) • c x
    have hab : (a ⊗ₜ[R] b : A ⊗[R] B) =
        (Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) *
          Algebra.TensorProduct.includeRight b := by
      simp [Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.includeRight]
    have hab' : (algebraMap A Aq a ⊗ₜ[R] b : Aq ⊗[R] B) =
        (Algebra.TensorProduct.includeLeft (S := R) (algebraMap A Aq a) : Aq ⊗[R] B) *
          Algebra.TensorProduct.includeRight b := by
      simp [Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.includeRight]
    rw [hab, hab', mul_smul, mul_smul, localizationModelMap_left R A Aq B D i Q L K uQ huQ]
    congr 1
    exact c.hom.map_smul b x
  | add a b ha hb => simp only [add_smul, map_add, ha, hb]


end RingTensorCohomology
