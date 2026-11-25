/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.GroupWithZero.Units.Basic

import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-! # Finite character projectors on a split coefficient module

Source: latest blueprint, lem-wft-as-unit-trivialization.proof.md, first paragraph,
the character eigenfunctions and their root evaluations
(blueprint: lem-wft-as-split-character-projector).

Reindexing the finite sum gives eπ_d = χ(d)eπ_0. Construct the character vector j
with components χ(d)id. The character identity and invertibility of the group
order imply je = j, while jπ_0 = id. Product extensionality gives e = (eπ_0)j,
so e is idempotent and eπ_0, j form a strong epi-mono factorization of e.
The unique image comparison identifies the image with the coefficient object,
and its compatibility with the actual image inclusion identifies it as evaluation.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ArtinSchreierUnit

variable {R : Type u} [CommRing R]
variable {G : Type v} [AddCommGroup G] [Fintype G]
variable {C : Type w} [Category C] [Preadditive C] [Linear R C]
variable (U : C) [HasProduct (fun _ : G ↦ U)]
variable (χ : AddChar G R)

/-- Translation of functions on the trivial G-torsor. -/
def splitTranslation (c : G) : End (∏ᶜ fun _ : G ↦ U) :=
  .of (Pi.lift (fun d ↦ Pi.π (fun _ : G ↦ U) (d + c)))

/-- The actual finite averaging endomorphism in a linear category. -/
def splitProjector : End (∏ᶜ fun _ : G ↦ U) :=
  ∑ c : G, (Ring.inverse (Fintype.card G : R) * χ (-c)) • splitTranslation U c

/-- The χ-eigenfunction with prescribed value at zero. -/
def splitCharacterVector : U ⟶ ∏ᶜ fun _ : G ↦ U :=
  Pi.lift (fun d ↦ χ d • 𝟙 U)

omit [Fintype G] in
@[simp] theorem splitCharacterVector_π (d : G) :
    splitCharacterVector U χ ≫ Pi.π (fun _ : G ↦ U) d = χ d • 𝟙 U := by
  simp [splitCharacterVector]

omit [Fintype G] in
@[simp] theorem splitCharacterVector_zero :
    splitCharacterVector U χ ≫ Pi.π (fun _ : G ↦ U) 0 = 𝟙 U := by
  simp

theorem splitProjector_π (d : G) :
    (splitProjector U χ).asHom ≫ Pi.π (fun _ : G ↦ U) d =
      ∑ c : G, (Ring.inverse (Fintype.card G : R) * χ (-c)) •
        Pi.π (fun _ : G ↦ U) (d + c) := by
  unfold splitProjector
  rw [End.sum_asHom, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro c hc
  change ((Ring.inverse (Fintype.card G : R) * χ (-c)) •
    (splitTranslation U c).asHom) ≫ Pi.π (fun _ : G ↦ U) d = _
  rw [CategoryTheory.Linear.smul_comp]
  exact congrArg (fun t ↦ (Ring.inverse (Fintype.card G : R) * χ (-c)) • t)
    (Pi.lift_comp_π (fun d ↦ Pi.π (fun _ : G ↦ U) (d + c)) d)

theorem splitProjector_eigen (d : G) :
    (splitProjector U χ).asHom ≫ Pi.π (fun _ : G ↦ U) d =
      χ d • ((splitProjector U χ).asHom ≫ Pi.π (fun _ : G ↦ U) 0) := by
  rw [splitProjector_π, splitProjector_π, Finset.smul_sum]
  apply Fintype.sum_equiv (Equiv.addLeft d)
  intro c
  simp only [Equiv.coe_addLeft, zero_add, smul_smul]
  congr 1
  have he : χ d * (Ring.inverse (Fintype.card G : R) * χ (-(d + c))) =
      Ring.inverse (Fintype.card G : R) * χ (-c) := by
    rw [mul_left_comm, ← AddChar.map_add_eq_mul]
    congr 1
    abel_nf
  exact he.symm

theorem splitCharacterVector_projector
    (hq : IsUnit (Fintype.card G : R)) :
    splitCharacterVector U χ ≫ (splitProjector U χ).asHom = splitCharacterVector U χ := by
  apply Pi.hom_ext
  intro d
  simp only [Category.assoc, splitProjector_π, Preadditive.comp_sum,
    Linear.comp_smul, splitCharacterVector_π, smul_smul, AddChar.map_add_eq_mul]
  have he (c : G) :
      (Ring.inverse (Fintype.card G : R) * χ (-c)) * (χ d * χ c) =
        Ring.inverse (Fintype.card G : R) * χ d := by
    calc
      _ = Ring.inverse (Fintype.card G : R) * χ d * (χ (-c) * χ c) := by ring
      _ = Ring.inverse (Fintype.card G : R) * χ d := by
        rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, mul_one]
  simp only [he, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul R, smul_smul]
  rw [← mul_assoc, Ring.mul_inverse_cancel _ hq, one_mul]

/-- The averaging endomorphism factors through its value at zero. -/
theorem splitProjector_factor :
    ((splitProjector U χ).asHom ≫ Pi.π (fun _ : G ↦ U) 0) ≫ splitCharacterVector U χ =
      (splitProjector U χ).asHom := by
  apply Pi.hom_ext
  intro d
  rw [Category.assoc, splitCharacterVector_π, Linear.comp_smul, Category.comp_id]
  exact (splitProjector_eigen U χ d).symm

/-- The finite average is idempotent when the group order is invertible. -/
theorem splitProjector_idempotent (hq : IsUnit (Fintype.card G : R)) :
    (splitProjector U χ).asHom ≫ (splitProjector U χ).asHom = (splitProjector U χ).asHom := by
  calc
    _ = ((splitProjector U χ).asHom ≫ Pi.π (fun _ : G ↦ U) 0) ≫
        splitCharacterVector U χ ≫ (splitProjector U χ).asHom := by
      rw [← Category.assoc, splitProjector_factor]
    _ = ((splitProjector U χ).asHom ≫ Pi.π (fun _ : G ↦ U) 0) ≫
        splitCharacterVector U χ := by
      rw [splitCharacterVector_projector U χ hq]
    _ = (splitProjector U χ).asHom := splitProjector_factor U χ

/-- Averaging an actual finite group action, without choosing a splitting chart. -/
def actionProjector (M : C) (σ : G → End M) (χ : AddChar G R) : End M :=
  ∑ c : G, (Ring.inverse (Fintype.card G : R) * χ (-c)) • σ c

/-- Reindexing the finite average gives its character eigenrelation. -/
theorem actionProjector_eigen (M : C) (σ : G → End M) (χ : AddChar G R)
    (hσ : ∀ a b, σ (a + b) = .of ((σ a).asHom ≫ (σ b).asHom)) (b : G) :
    (actionProjector M σ χ).asHom ≫ (σ b).asHom = (χ b • actionProjector M σ χ).asHom := by
  unfold actionProjector
  simp only [End.sum_asHom, End.smul_asHom]
  rw [Preadditive.sum_comp, Finset.smul_sum]
  apply Fintype.sum_equiv (Equiv.addRight b)
  intro a
  change ((Ring.inverse (Fintype.card G : R) * χ (-a)) • (σ a).asHom) ≫ (σ b).asHom =
    χ b • ((Ring.inverse (Fintype.card G : R) * χ (-(a + b))) • (σ (a + b)).asHom)
  have hs : χ b * (Ring.inverse (Fintype.card G : R) * χ (-(a + b))) =
      Ring.inverse (Fintype.card G : R) * χ (-a) := by
    rw [mul_left_comm, ← AddChar.map_add_eq_mul]
    congr 1
    abel_nf
  calc
    _ = (Ring.inverse (Fintype.card G : R) * χ (-a)) • ((σ a).asHom ≫ (σ b).asHom) :=
      Linear.smul_comp _ _ _ _ _ _
    _ = (Ring.inverse (Fintype.card G : R) * χ (-a)) • (σ (a + b)).asHom :=
      congrArg (fun t ↦ (Ring.inverse (Fintype.card G : R) * χ (-a)) • t)
        (congrArg End.asHom (hσ a b)).symm
    _ = (χ b * (Ring.inverse (Fintype.card G : R) * χ (-(a + b)))) • (σ (a + b)).asHom :=
      congrArg (fun r ↦ r • (σ (a + b)).asHom) hs.symm
    _ = _ := (smul_smul _ _ _).symm

/-- Averaging is idempotent whenever the group order is invertible. -/
theorem actionProjector_idempotent (M : C) (σ : G → End M) (χ : AddChar G R)
    (hσ : ∀ a b, σ (a + b) = .of ((σ a).asHom ≫ (σ b).asHom))
    (hq : IsUnit (Fintype.card G : R)) :
    (actionProjector M σ χ).asHom ≫ (actionProjector M σ χ).asHom =
      (actionProjector M σ χ).asHom := by
  conv_lhs => arg 2; simp only [actionProjector, End.sum_asHom, End.smul_asHom]
  rw [Preadditive.comp_sum]
  have ht (c : G) : (actionProjector M σ χ).asHom ≫
        ((Ring.inverse (Fintype.card G : R) * χ (-c)) • (σ c).asHom) =
      Ring.inverse (Fintype.card G : R) • (actionProjector M σ χ).asHom := by
    calc
      _ = (Ring.inverse (Fintype.card G : R) * χ (-c)) •
          ((actionProjector M σ χ).asHom ≫ (σ c).asHom) := Linear.comp_smul _ _ _ _ _ _
      _ = (Ring.inverse (Fintype.card G : R) * χ (-c)) •
          (χ c • (actionProjector M σ χ).asHom) :=
        congrArg (fun t ↦ (Ring.inverse (Fintype.card G : R) * χ (-c)) • t)
          (actionProjector_eigen M σ χ hσ c)
      _ = _ := by
        rw [smul_smul, mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel,
          AddChar.map_zero_eq_one, mul_one]
  simp only [ht, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul R, smul_smul, Ring.mul_inverse_cancel _ hq, one_smul]

variable [HasStrongEpiMonoFactorisations C]

/-- The image of the split character average is the coefficient object.
The section is the actual character vector, rather than a chosen existence witness.
Source: latest blueprint, lem-wft-as-unit-trivialization.proof.md, first paragraph,
root evaluation (blueprint: lem-wft-as-split-character-projector). -/
def splitProjectorImageIso (hq : IsUnit (Fintype.card G : R)) :
    image ((splitProjector U χ)).asHom ≅ U := by
  let r := (splitProjector U χ).asHom ≫ Pi.π (fun _ : G ↦ U) 0
  let j := splitCharacterVector U χ
  have hjr : j ≫ r = 𝟙 U := by
    dsimp only [j, r]
    rw [← Category.assoc, splitCharacterVector_projector U χ hq,
      splitCharacterVector_zero]
  have : StrongEpi (j ≫ r) := by rw [hjr]; infer_instance
  let : StrongEpi r := strongEpi_of_strongEpi j r
  let : IsSplitMono j := IsSplitMono.mk' ⟨Pi.π (fun _ : G ↦ U) 0,
    splitCharacterVector_zero U χ⟩
  exact (image.isoStrongEpiMono r j (splitProjector_factor U χ)).symm

/-- This image isomorphism is evaluation at zero, with the specified image inclusion. -/
theorem splitProjectorImageIso_hom (hq : IsUnit (Fintype.card G : R)) :
    (splitProjectorImageIso U χ hq).hom =
      image.ι ((splitProjector U χ)).asHom ≫ Pi.π (fun _ : G ↦ U) 0 := by
  let r := (splitProjector U χ).asHom ≫ Pi.π (fun _ : G ↦ U) 0
  let j := splitCharacterVector U χ
  have hjr : j ≫ r = 𝟙 U := by
    dsimp only [j, r]
    rw [← Category.assoc, splitCharacterVector_projector U χ hq,
      splitCharacterVector_zero]
  have : StrongEpi (j ≫ r) := by rw [hjr]; infer_instance
  let : StrongEpi r := strongEpi_of_strongEpi j r
  let : IsSplitMono j := IsSplitMono.mk' ⟨Pi.π (fun _ : G ↦ U) 0,
    splitCharacterVector_zero U χ⟩
  have h := congrArg (fun t ↦ t ≫ Pi.π (fun _ : G ↦ U) 0)
    (image.isoStrongEpiMono_inv_comp_mono r j (splitProjector_factor U χ))
  simpa only [splitProjectorImageIso, Iso.symm_hom, Category.assoc, j,
    splitCharacterVector_zero, Category.comp_id] using h

/-- The inverse image comparison is the explicit character vector. -/
theorem splitProjectorImageIso_inv (hq : IsUnit (Fintype.card G : R)) :
    (splitProjectorImageIso U χ hq).inv ≫ image.ι ((splitProjector U χ)).asHom =
      splitCharacterVector U χ := by
  simp only [splitProjectorImageIso, Iso.symm_inv,
    image.isoStrongEpiMono_hom_comp_ι]

/-- Evaluation at zero on the actual image is an isomorphism. -/
theorem splitProjectorImageEvaluation_isIso (hq : IsUnit (Fintype.card G : R)) :
    IsIso (image.ι ((splitProjector U χ)).asHom ≫ Pi.π (fun _ : G ↦ U) 0) := by
  rw [← splitProjectorImageIso_hom U χ hq]
  infer_instance

end AlgebraicGeometry.ArtinSchreierUnit
