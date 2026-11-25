/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Preadditive.CokernelBiproduct
public import WeilConjectures.CategoryTheory.Preadditive.FinitePowerCokernel
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber

/-!
# Pivots and ranks of morphisms between finite powers of an object

Let `C` be a preadditive category with finite biproducts and cokernels, and `U` an object of `C`.

- `CategoryTheory.Limits.exists_cokernel_iso_of_isIso_entry`: **Gaussian elimination at a
  pivot**. If an entry of a morphism `f : Uᵐ⁺¹ ⟶ Uⁿ⁺¹` is invertible, the cokernel of `f` is the
  cokernel of a morphism `Uᵐ ⟶ Uⁿ`.
- `CategoryTheory.Limits.eq_of_iso_biproduct_fin`: if `End U` admits a ring homomorphism to a
  nontrivial commutative ring, then `Uᵃ ≅ Uᵇ` implies `a = b`.
- `CategoryTheory.Limits.exists_le_iso_cokernel_biproduct_fin`: if the nonzero endomorphisms of
  `U` are invertible, the cokernel of `f : Uᵐ ⟶ Uⁿ` is `Uᵈ` with `d ≤ n`, and `d < n` if `f ≠ 0`.
- `CategoryTheory.Limits.eq_zero_of_cokernel_iso_biproduct_fin`: under both assumptions, a
  morphism `f : Uᵐ ⟶ Uⁿ` with cokernel isomorphic to `Uⁿ` is zero.
-/

@[expose] public section

namespace CategoryTheory.Limits

universe v u

open Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C] {U : C}

/-- Morphisms between finite powers of `U` are determined by their entries. -/
lemma biproduct_fin_hom_ext {m n : ℕ} {f g : (⨁ fun _ : Fin m ↦ U) ⟶ ⨁ fun _ : Fin n ↦ U}
    (h : ∀ a b, biproduct.ι _ b ≫ f ≫ biproduct.π _ a = biproduct.ι _ b ≫ g ≫ biproduct.π _ a) :
    f = g :=
  biproduct.hom_ext' _ _ fun b ↦ biproduct.hom_ext _ _ fun a ↦ by
    simpa only [Category.assoc] using h a b

/-! ### Gaussian elimination at a pivot -/

/-- **Gaussian elimination at a pivot**: if the entry `(a, b)` of `f : Uᵐ⁺¹ ⟶ Uⁿ⁺¹` is
invertible, the cokernel of `f` is isomorphic to the cokernel of a morphism `Uᵐ ⟶ Uⁿ`. -/
theorem exists_cokernel_iso_of_isIso_entry [HasCokernels C] {m n : ℕ}
    (f : (⨁ fun _ : Fin (m + 1) ↦ U) ⟶ ⨁ fun _ : Fin (n + 1) ↦ U) (a : Fin (n + 1))
    (b : Fin (m + 1))
    [IsIso (biproduct.ι (fun _ : Fin (m + 1) ↦ U) b ≫ f ≫
      biproduct.π (fun _ : Fin (n + 1) ↦ U) a)] :
    ∃ f' : (⨁ fun _ : Fin m ↦ U) ⟶ ⨁ fun _ : Fin n ↦ U, Nonempty (cokernel f ≅ cokernel f') := by
  have : IsIso ((biproduct.ι (fun _ : Fin (m + 1) ↦ U) b ≫ f) ≫
      biproduct.π (fun _ : Fin (n + 1) ↦ U) a) := by
    rw [Category.assoc]
    infer_instance
  let eS : (⨁ fun _ : Fin m ↦ U) ≅ ⨁ fun _ : { j // j ≠ b } ↦ U :=
    biproduct.whiskerEquiv (finSuccAboveEquiv b) fun _ ↦ Iso.refl U
  let eT : (⨁ fun _ : { i // i ≠ a } ↦ U) ≅ ⨁ fun _ : Fin n ↦ U :=
    (biproduct.whiskerEquiv (finSuccAboveEquiv a) fun _ ↦ Iso.refl U).symm
  let e₁ := cokernelIsoOfIsIsoCompπ _ (biproduct.ι (fun _ : Fin (m + 1) ↦ U) b ≫ f) a
  refine ⟨eS.hom ≫ fromSubtypeCokernel _ f b ≫ e₁.hom ≫ eT.hom, ⟨?_⟩⟩
  exact cokernelIsoCokernelFromSubtype _ f b ≪≫ (cokernelCompIsIso _ (e₁.hom ≫ eT.hom)).symm ≪≫
    (cokernelEpiComp eS.hom _).symm

/-! ### Invariance of the exponent of a finite power -/

/-- The matrix of a morphism `Uᵖ ⟶ Uᵠ`, with entries in `End U`. -/
noncomputable def biproductFinMatrix {p q : ℕ}
    (g : (⨁ fun _ : Fin p ↦ U) ⟶ ⨁ fun _ : Fin q ↦ U) :
    Matrix (Fin q) (Fin p) (End U) :=
  fun i j ↦ .of (biproduct.ι (fun _ : Fin p ↦ U) j ≫ g ≫ biproduct.π (fun _ : Fin q ↦ U) i)

/-- The matrix of a composition is the product of the matrices (in the opposite order, since
multiplication in `End U` is composition in the opposite order). -/
lemma biproductFinMatrix_comp {p q r : ℕ} (g : (⨁ fun _ : Fin p ↦ U) ⟶ ⨁ fun _ : Fin q ↦ U)
    (h : (⨁ fun _ : Fin q ↦ U) ⟶ ⨁ fun _ : Fin r ↦ U) :
    biproductFinMatrix (g ≫ h) = biproductFinMatrix h * biproductFinMatrix g := by
  funext i k
  apply End.ext
  simp only [biproductFinMatrix, Matrix.mul_apply, End.sum_asHom, End.mul_asHom]
  conv_lhs => rw [← Category.id_comp h, ← biproduct.total]
  simp only [comp_sum, sum_comp, Category.assoc]

/-- The matrix of the identity is the identity matrix. -/
lemma biproductFinMatrix_id (p : ℕ) :
    biproductFinMatrix (𝟙 (⨁ fun _ : Fin p ↦ U)) = 1 := by
  funext i j
  apply End.ext
  simp only [biproductFinMatrix, Category.id_comp, Matrix.one_apply]
  by_cases h : j = i
  · subst h
    simp [End.one_asHom]
  · simp [biproduct.ι_π_ne _ h, Ne.symm h]

/-- If `End U` admits a ring homomorphism to a nontrivial commutative ring, finite powers of `U`
determine their exponent. -/
theorem eq_of_iso_biproduct_fin {K : Type*} [CommRing K] [Nontrivial K] (ψ : End U →+* K)
    {a b : ℕ} (e : (⨁ fun _ : Fin a ↦ U) ≅ ⨁ fun _ : Fin b ↦ U) : a = b := by
  have h₁ := congrArg (Matrix.map · ψ) (biproductFinMatrix_comp e.inv e.hom)
  have h₂ := congrArg (Matrix.map · ψ) (biproductFinMatrix_comp e.hom e.inv)
  simp only [e.inv_hom_id, e.hom_inv_id, biproductFinMatrix_id, Matrix.map_mul] at h₁ h₂
  rw [Matrix.map_one _ (map_zero ψ) (map_one ψ)] at h₁ h₂
  simpa using (Matrix.square_of_invertible _ _ h₁.symm h₂.symm).symm

/-! ### Cokernels over an object with invertible nonzero endomorphisms -/

/-- If the nonzero endomorphisms of `U` are invertible, the cokernel of `f : Uᵐ ⟶ Uⁿ` is
isomorphic to `Uᵈ` for some `d ≤ n`, with `d < n` if `f ≠ 0`. -/
theorem exists_le_iso_cokernel_biproduct_fin [HasCokernels C]
    (hU : ∀ t : End U, t ≠ 0 → IsIso (t).asHom) {m n : ℕ}
    (f : (⨁ fun _ : Fin m ↦ U) ⟶ ⨁ fun _ : Fin n ↦ U) :
    ∃ d ≤ n, (f ≠ 0 → d < n) ∧ Nonempty (cokernel f ≅ ⨁ fun _ : Fin d ↦ U) := by
  induction n generalizing m with
  | zero =>
    refine ⟨0, le_rfl, fun hf ↦ (hf ?_).elim, ⟨cokernelIsoOfEq ?_ ≪≫ cokernelZeroIsoTarget⟩⟩ <;>
      exact (isZero_biproduct_fin_zero _).eq_of_tgt _ _
  | succ n ih =>
    by_cases hf : f = 0
    · subst hf
      exact ⟨n + 1, le_rfl, fun h ↦ (h rfl).elim, ⟨cokernelZeroIsoTarget⟩⟩
    obtain ⟨a, b, hab⟩ : ∃ a b, biproduct.ι _ b ≫ f ≫ biproduct.π _ a ≠ 0 := by
      by_contra! h
      exact hf (biproduct_fin_hom_ext fun a b ↦ by simp [h a b])
    obtain _ | m := m
    · exact b.elim0
    have : IsIso (biproduct.ι (fun _ : Fin (m + 1) ↦ U) b ≫ f ≫
        biproduct.π (fun _ : Fin (n + 1) ↦ U) a) :=
      hU (biproductFinMatrix f a b) (by
        intro h
        exact hab (congr($(h).asHom)))
    obtain ⟨f', ⟨e⟩⟩ := exists_cokernel_iso_of_isIso_entry f a b
    obtain ⟨d, hd, -, ⟨e'⟩⟩ := ih f'
    exact ⟨d, by omega, fun _ ↦ by omega, ⟨e ≪≫ e'⟩⟩

/-- If the nonzero endomorphisms of `U` are invertible and `End U` admits a ring homomorphism to
a nontrivial commutative ring, a morphism `f : Uᵐ ⟶ Uⁿ` whose cokernel is isomorphic to `Uⁿ` is
zero. -/
theorem eq_zero_of_cokernel_iso_biproduct_fin [HasCokernels C]
    (hU : ∀ t : End U, t ≠ 0 → IsIso (t).asHom) {K : Type*} [CommRing K] [Nontrivial K]
    (ψ : End U →+* K) {m n : ℕ} (f : (⨁ fun _ : Fin m ↦ U) ⟶ ⨁ fun _ : Fin n ↦ U)
    (e : cokernel f ≅ ⨁ fun _ : Fin n ↦ U) : f = 0 := by
  by_contra hf
  obtain ⟨d, -, hd, ⟨e'⟩⟩ := exists_le_iso_cokernel_biproduct_fin hU f
  exact (hd hf).ne (eq_of_iso_biproduct_fin ψ (e'.symm ≪≫ e))

end CategoryTheory.Limits
