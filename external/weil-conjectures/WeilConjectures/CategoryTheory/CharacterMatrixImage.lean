/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Tactic.Ring

/-! # Rank-one images of character matrices -/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

private theorem scalar_comp {C : Type*} [Category C] [Preadditive C]
    {S : Type*} [CommRing S] {R : C} (r : S →+* End R) (a b : S) :
    (r a).asHom ≫ (r b).asHom = (r (a * b)).asHom := by
  rw [← End.mul_asHom, ← map_mul, mul_comm]

private theorem character_column_row
    {C : Type*} [Category C] [Preadditive C]
    {S : Type*} [CommRing S] {R : C} (r : S →+* End R)
    (G : Type*) [AddCommGroup G] [Fintype G] [HasProduct (fun _ : G ↦ R)]
    (χ : AddChar G S) (hn : IsUnit (Fintype.card G : S)) :
    Pi.lift (fun a : G ↦ (r (χ a)).asHom) ≫
        (∑ a : G, Pi.π (fun _ : G ↦ R) a ≫
          (r (Ring.inverse (Fintype.card G : S) * χ (-a))).asHom) = 𝟙 R := by
  classical
  rw [Preadditive.comp_sum]
  simp only [← Category.assoc, Pi.lift_comp_π]
  have he (a : G) : χ a * (Ring.inverse (Fintype.card G : S) * χ (-a)) =
      Ring.inverse (Fintype.card G : S) := by
    rw [mul_left_comm, ← χ.map_add_eq_mul, add_neg_cancel,
      χ.map_zero_eq_one, mul_one]
  simp only [scalar_comp r, he, Finset.sum_const, Finset.card_univ]
  rw [← End.nsmul_asHom, ← End.one_asHom]
  congr 1
  rw [← map_nsmul r, nsmul_eq_mul, Ring.mul_inverse_cancel _ hn, map_one]

private theorem character_matrix_factorization
    {C : Type*} [Category C] [Preadditive C]
    {S : Type*} [CommRing S] {R M : C} (r : S →+* End R)
    (G : Type*) [AddCommGroup G] [Fintype G] [HasProduct (fun _ : G ↦ R)]
    (χ : AddChar G S) (q : M ≅ ∏ᶜ (fun _ : G ↦ R)) (e : End M)
    (he : ∀ a : G, (e).asHom ≫ q.hom ≫ Pi.π (fun _ : G ↦ R) a =
      ∑ b : G, (q.hom ≫ Pi.π (fun _ : G ↦ R) b) ≫
        (r (Ring.inverse (Fintype.card G : S) * χ (a - b))).asHom) :
    (q.hom ≫ ∑ b : G, Pi.π (fun _ : G ↦ R) b ≫
        (r (Ring.inverse (Fintype.card G : S) * χ (-b))).asHom) ≫
      (Pi.lift (fun a : G ↦ (r (χ a)).asHom) ≫ q.inv) = (e).asHom := by
  classical
  apply (cancel_mono q.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply Pi.hom_ext
  intro a
  simp only [Category.assoc, Pi.lift_comp_π, Preadditive.comp_sum,
    Preadditive.sum_comp]
  rw [he a]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [Category.assoc, scalar_comp r]
  apply congrArg (fun z ↦ q.hom ≫ Pi.π (fun _ : G ↦ R) b ≫ (r z).asHom)
  rw [sub_eq_add_neg, χ.map_add_eq_mul]
  ring

/-- A normalized character matrix on a finite product has rank-one image;
evaluation at the zero index is the specified isomorphism.
Source: blueprint lemma-artin-schreier-character-sheaf, Step 4, eigenfunction calculation
(blueprint: lem-fd-as-character-matrix-image).

Proof: form the column a mapped to multiplication by χ(a), and the weighted row
sum_b π_b times n⁻¹χ(-b). Their composite on the coefficient object is the identity:
each summand is n⁻¹ because χ(b)χ(-b)=1, and there are n summands. The reverse
composite is the specified character matrix, since χ(a-b)=χ(a)χ(-b).
This is a split epi-mono factorization, so its middle object is the categorical
image. The column has identity zero component, which identifies the inverse
image comparison with evaluation at zero. -/
theorem characterMatrix_image_evaluation_isIso
    {C : Type*} [Category C] [Abelian C]
    {S : Type*} [CommRing S] {R M : C} (r : S →+* End R)
    (G : Type*) [AddCommGroup G] [Fintype G] [HasProduct (fun _ : G ↦ R)]
    (χ : AddChar G S) (hn : IsUnit (Fintype.card G : S))
    (q : M ≅ ∏ᶜ (fun _ : G ↦ R)) (e : End M)
    (he : ∀ a : G, (e).asHom ≫ q.hom ≫ Pi.π (fun _ : G ↦ R) a =
      ∑ b : G, (q.hom ≫ Pi.π (fun _ : G ↦ R) b) ≫
        (r (Ring.inverse (Fintype.card G : S) * χ (a - b))).asHom) :
    IsIso (image.ι (e).asHom ≫ q.hom ≫ Pi.π (fun _ : G ↦ R) 0) := by
  classical
  let row : M ⟶ R := q.hom ≫ ∑ b : G, Pi.π (fun _ : G ↦ R) b ≫
    (r (Ring.inverse (Fintype.card G : S) * χ (-b))).asHom
  let col : R ⟶ M := Pi.lift (fun a : G ↦ (r (χ a)).asHom) ≫ q.inv
  have hs : col ≫ row = 𝟙 R := by
    dsimp only [col, row]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact character_column_row r G χ hn
  have hp : row ≫ col = e.asHom := character_matrix_factorization r G χ q e he
  let : IsSplitEpi row := IsSplitEpi.mk' ⟨col, hs⟩
  let : IsSplitMono col := IsSplitMono.mk' ⟨row, hs⟩
  let i : R ≅ image e.asHom := image.isoStrongEpiMono row col hp
  have hi : i.hom ≫ (image.ι e.asHom ≫ q.hom ≫ Pi.π (fun _ : G ↦ R) 0) = 𝟙 R := by
    rw [← Category.assoc, image.isoStrongEpiMono_hom_comp_ι]
    simp only [col, Category.assoc, Iso.inv_hom_id_assoc, Pi.lift_comp_π,
      χ.map_zero_eq_one, map_one]
    rfl
  have : IsIso (i.hom ≫ (image.ι e.asHom ≫ q.hom ≫ Pi.π (fun _ : G ↦ R) 0)) := by
    rw [hi]
    infer_instance
  exact IsIso.of_isIso_comp_left i.hom _

end CategoryTheory
