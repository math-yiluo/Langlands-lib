import Langlands.Shimura.Unitary.DiagonalWeightConjugacy
import Langlands.Shimura.Unitary.ComplexCocharacterPoints

noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Algebra Module Matrix
open scoped CategoryTheory.MonObj Classical
attribute [local instance 1100] Algebra.toModule

namespace Langlands.Shimura.ComplexMatrix

variable (S : Type*) [CommRing S] {n : ℕ}

/-- The diagonal matrix unit with inverse weight on a specified coordinate support. -/
def inverseDiagonalUnit (p : Fin n → Prop) [DecidablePred p] (u : Sˣ) :
    (Matrix (Fin n) (Fin n) S)ˣ where
  val := Matrix.diagonal (fun j => if p j then (↑(u⁻¹) : S) else 1)
  inv := Matrix.diagonal (fun j => if p j then (u : S) else 1)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    trans Matrix.diagonal (fun _ : Fin n => (1 : S))
    · congr 1
      funext j
      by_cases hj : p j <;> simp [hj]
    · exact Matrix.diagonal_one
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    trans Matrix.diagonal (fun _ : Fin n => (1 : S))
    · congr 1
      funext j
      by_cases hj : p j <;> simp [hj]
    · exact Matrix.diagonal_one

end Langlands.Shimura.ComplexMatrix

namespace Langlands.Shimura.CentralSimpleUnitaryData

variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
  {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
  (T : Over (Spec (CommRingCat.of ℂ)))

/-- Actual Harris group points with specified inverse-weight supports and inverse multiplier. -/
def diagonalWeightPointFamily (p : (E →+* ℝ) → Fin n → Prop)
    (u : (AlgebraInvolution.complexTestAlgebra T)ˣ) :
    T ⟶ D.complexRationalGroupScheme.X :=
  (D.complexGroupPointsEquiv C T).symm
    (fun τ => ComplexMatrix.inverseDiagonalUnit (AlgebraInvolution.complexTestAlgebra T) (p τ) u,
      u⁻¹)

@[simp] theorem diagonalWeightPointFamily_split (p : (E →+* ℝ) → Fin n → Prop)
    (u : (AlgebraInvolution.complexTestAlgebra T)ˣ) :
    D.complexGroupPointsEquiv C T (D.diagonalWeightPointFamily C T p u) =
      (fun τ => ComplexMatrix.inverseDiagonalUnit (AlgebraInvolution.complexTestAlgebra T) (p τ) u,
        u⁻¹) :=
  (D.complexGroupPointsEquiv C T).apply_symm_apply _

/-- The actual point lifting the factorwise support-permutation matrices, with multiplier one. -/
def diagonalWeightPointConjugator (p q : (E →+* ℝ) → Fin n → Prop)
    (h : ∀ τ, (Finset.univ.filter (p τ)).card = (Finset.univ.filter (q τ)).card) :
    T ⟶ D.complexRationalGroupScheme.X :=
  (D.complexGroupPointsEquiv C T).symm
    (fun τ => ComplexMatrix.diagonalWeightConjugator (p τ) (q τ)
      (AlgebraInvolution.complexTestAlgebra T) (h τ), 1)

set_option backward.isDefEq.respectTransparency false in
/-- One actual Harris group point conjugates the complete diagonal point families. -/
theorem diagonalWeightPointConjugator_spec (p q : (E →+* ℝ) → Fin n → Prop)
    (h : ∀ τ, (Finset.univ.filter (p τ)).card = (Finset.univ.filter (q τ)).card)
    (u : (AlgebraInvolution.complexTestAlgebra T)ˣ) :
    D.diagonalWeightPointConjugator C T p q h * D.diagonalWeightPointFamily C T p u *
      (D.diagonalWeightPointConjugator C T p q h)⁻¹ = D.diagonalWeightPointFamily C T q u := by
  apply (D.complexGroupPointsEquiv C T).injective
  simp only [map_mul, map_inv, diagonalWeightPointConjugator,
    MulEquiv.apply_symm_apply, diagonalWeightPointFamily_split]
  apply Prod.ext
  · funext τ
    apply Units.ext
    exact ComplexMatrix.diagonalWeightConjugator_spec (p τ) (q τ)
      (AlgebraInvolution.complexTestAlgebra T) (h τ) u
  · simp

/-- Simultaneous conjugacy of the specified families in the actual group of Harris points. -/
def DiagonalWeightPointConjugate (p q : (E →+* ℝ) → Fin n → Prop) : Prop :=
  ∃ g : T ⟶ D.complexRationalGroupScheme.X,
    ∀ u : (AlgebraInvolution.complexTestAlgebra T)ˣ,
      g * D.diagonalWeightPointFamily C T p u * g⁻¹ = D.diagonalWeightPointFamily C T q u

set_option backward.isDefEq.respectTransparency false in
/-- Factorwise support cardinalities classify these actual point families. -/
theorem diagonalWeightPointConjugate_iff_card_eq [Nontrivial Γ(T.left, ⊤)]
    (p q : (E →+* ℝ) → Fin n → Prop) :
    D.DiagonalWeightPointConjugate C T p q ↔
      ∀ τ, (Finset.univ.filter (p τ)).card = (Finset.univ.filter (q τ)).card := by
  let : Nontrivial (AlgebraInvolution.complexTestAlgebra T) := ‹Nontrivial Γ(T.left, ⊤)›
  constructor
  · rintro ⟨g, hg⟩ τ
    apply (ComplexMatrix.diagonalWeightConjugate_iff_card_eq (p τ) (q τ)
      (AlgebraInvolution.complexTestAlgebra T)).mp
    refine ⟨(D.complexGroupPointsEquiv C T g).1 τ, ?_⟩
    intro u
    have he := congrArg (D.complexGroupPointsEquiv C T) (hg u)
    simp only [map_mul, map_inv, diagonalWeightPointFamily_split] at he
    exact congrArg (fun z => (z.1 τ :
      Matrix (Fin n) (Fin n) (AlgebraInvolution.complexTestAlgebra T))) he
  · intro h
    exact ⟨D.diagonalWeightPointConjugator C T p q h,
      D.diagonalWeightPointConjugator_spec C T p q h⟩

set_option backward.isDefEq.respectTransparency false in
/-- The first-source-factor Kottwitz cocharacter is the prescribed diagonal point family. -/
theorem diagonalWeightPointFamily_kottwitz
    (u : (AlgebraInvolution.complexTestAlgebra T)ˣ) :
    D.diagonalWeightPointFamily C T
      (fun τ j => j.val < if τ = C.distinguished then n - 1 else n) u =
      (GroupScheme.Gm.pointsEquiv _ T).symm u ≫
        (D.kottwitzCocharacter C true).hom.hom := by
  apply (D.complexGroupPointsEquiv C T).injective
  rw [D.diagonalWeightPointFamily_split, D.kottwitzCocharacter_split_points,
    MulEquiv.apply_symm_apply]
  apply Prod.ext
  · funext τ
    apply Units.ext
    rw [ComplexMatrix.kottwitzSplitPoint_matrix]
    simp only [ComplexMatrix.inverseDiagonalUnit, ComplexMatrix.splitDiagonal, ite_true]
    congr 1
    funext j
    split_ifs <;> rfl
  · rfl

set_option backward.isDefEq.respectTransparency false in
/-- Conjugacy to the actual first-factor Kottwitz family is exactly the signature count condition. -/
theorem diagonalWeightPointConjugate_kottwitz_iff [Nontrivial Γ(T.left, ⊤)]
    (q : (E →+* ℝ) → Fin n → Prop) :
    (∃ g : T ⟶ D.complexRationalGroupScheme.X,
      ∀ u : (AlgebraInvolution.complexTestAlgebra T)ˣ,
        g * ((GroupScheme.Gm.pointsEquiv _ T).symm u ≫
          (D.kottwitzCocharacter C true).hom.hom) * g⁻¹ =
            D.diagonalWeightPointFamily C T q u) ↔
      ∀ τ, (Finset.univ.filter (q τ)).card =
        if τ = C.distinguished then n - 1 else n := by
  let p : (E →+* ℝ) → Fin n → Prop :=
    fun τ j => j.val < if τ = C.distinguished then n - 1 else n
  have hc : (∃ g : T ⟶ D.complexRationalGroupScheme.X,
      ∀ u : (AlgebraInvolution.complexTestAlgebra T)ˣ,
        g * ((GroupScheme.Gm.pointsEquiv _ T).symm u ≫
          (D.kottwitzCocharacter C true).hom.hom) * g⁻¹ =
            D.diagonalWeightPointFamily C T q u) ↔
      D.DiagonalWeightPointConjugate C T p q := by
    simp only [DiagonalWeightPointConjugate, p, D.diagonalWeightPointFamily_kottwitz]
  rw [hc, D.diagonalWeightPointConjugate_iff_card_eq]
  apply forall_congr'
  intro τ
  dsimp only [p]
  rw [Finset.filter_congr_decidable, Fin.card_filter_val_lt, min_eq_right (by split_ifs <;> omega)]
  exact eq_comm

end Langlands.Shimura.CentralSimpleUnitaryData
