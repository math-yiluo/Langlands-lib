import Langlands.LinearAlgebra.OrthogonalCocycleDescent

/-! # Cohomology of orthogonal matrix cocycles and congruence of descended forms -/

noncomputable section

universe u w

namespace Langlands.LinearAlgebra.OrthogonalCocycleDescent

open Matrix

section Matrices

variable {R S : Type*} [CommRing R] [CommRing S]
  {n : Type w} [Fintype n] [DecidableEq n]

/-- Change a Gram matrix by an invertible matrix, in the row convention. -/
def gramTransform (P : GL n R) (B : Matrix n n R) : Matrix n n R :=
  (P : Matrix n n R) * B * (P : Matrix n n R)ᵀ

theorem gramTransform_mul (P Q : GL n R) (B : Matrix n n R) :
    gramTransform (P * Q) B = gramTransform P (gramTransform Q B) := by
  simp only [gramTransform, GeneralLinearGroup.coe_mul, transpose_mul, mul_assoc]

@[simp] theorem gramTransform_one (B : Matrix n n R) : gramTransform 1 B = B := by
  simp only [gramTransform, GeneralLinearGroup.coe_one, transpose_one, one_mul, mul_one]

@[simp] theorem gramTransform_inv (P : GL n R) (B : Matrix n n R) :
    gramTransform P⁻¹ (gramTransform P B) = B := by
  rw [← gramTransform_mul, inv_mul_cancel, gramTransform_one]

@[simp] theorem gramTransform_inv_right (P : GL n R) (B : Matrix n n R) :
    gramTransform P (gramTransform P⁻¹ B) = B := by
  rw [← gramTransform_mul, mul_inv_cancel, gramTransform_one]

theorem gramTransform_map (f : R →+* S) (P : GL n R) (B : Matrix n n R) :
    (gramTransform P B).map f =
      gramTransform (GeneralLinearGroup.map f P) (B.map f) := by
  simp only [gramTransform, Matrix.map_mul, Matrix.transpose_map]
  rfl

/-- Congruence of Gram matrices over the ground ring. -/
def GramCongruent (B₁ B₂ : Matrix n n R) : Prop :=
  ∃ Q : GL n R, gramTransform Q B₂ = B₁

end Matrices

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {n : Type w} [Fintype n] [DecidableEq n] {H : Matrix n n k}

/-- Pairwise cohomology of orthogonal matrix cocycles, with the same twist order as
natural group-scheme cocycles. -/
def OrthogonalCocycle.Cohomologous (c₁ c₂ : OrthogonalCocycle (L := L) H) : Prop :=
  ∃ a : GL n L,
    gramTransform a (H.map (algebraMap k L)) = H.map (algebraMap k L) ∧
    ∀ σ, c₂.toFun σ = a⁻¹ * c₁.toFun σ * GeneralLinearGroup.map σ.toRingHom a

theorem Descent.map_matrix (c : OrthogonalCocycle (L := L) H) (d : Descent c)
    (σ : L ≃ₐ[k] L) :
    GeneralLinearGroup.map σ.toRingHom d.matrix = (c.toFun σ)⁻¹ * d.matrix := by
  rw [d.coboundary, map_inv]
  group

theorem map_ground_matrix (P : GL n k) (σ : L ≃ₐ[k] L) :
    GeneralLinearGroup.map σ.toRingHom (GeneralLinearGroup.map (algebraMap k L) P) =
      GeneralLinearGroup.map (algebraMap k L) P := by
  apply Units.ext
  ext i j
  exact σ.commutes (P i j)

variable [FiniteDimensional k L] [IsGalois k L]

/-- A Galois-fixed invertible matrix descends as an invertible ground-field matrix. -/
theorem exists_unit_of_fixed (P : GL n L)
    (hP : ∀ σ : L ≃ₐ[k] L, GeneralLinearGroup.map σ.toRingHom P = P) :
    ∃ Q : GL n k, GeneralLinearGroup.map (algebraMap k L) Q = P := by
  obtain ⟨B, hB⟩ := exists_matrix_of_fixed (P : Matrix n n L)
    (fun σ => congrArg (fun A : GL n L => (A : Matrix n n L)) (hP σ))
  have hdet : B.det ≠ 0 := by
    intro hz
    apply P.det_ne_zero
    rw [← hB]
    change ((algebraMap k L).mapMatrix B).det = 0
    rw [← (algebraMap k L).map_det, hz, map_zero]
  exact ⟨GeneralLinearGroup.mkOfDetNeZero B hdet, Units.ext hB⟩

/-- Orthogonal cohomology makes the descended forms congruent over the ground field. -/
theorem gramCongruent_of_cohomologous
    {c₁ c₂ : OrthogonalCocycle (L := L) H} (d₁ : Descent c₁) (d₂ : Descent c₂)
    (h : c₁.Cohomologous c₂) : GramCongruent d₁.gram d₂.gram := by
  obtain ⟨a, ha, hc⟩ := h
  let P : GL n L := d₁.matrix⁻¹ * a * d₂.matrix
  have hfix (σ : L ≃ₐ[k] L) : GeneralLinearGroup.map σ.toRingHom P = P := by
    dsimp only [P]
    rw [map_mul, map_mul, map_inv, d₁.map_matrix, d₂.map_matrix, hc σ]
    group
  obtain ⟨Q, hQ⟩ := exists_unit_of_fixed P hfix
  refine ⟨Q, ?_⟩
  apply Matrix.map_injective (algebraMap k L).injective
  change (gramTransform Q d₂.gram).map (algebraMap k L) =
    d₁.gram.map (algebraMap k L)
  rw [gramTransform_map, hQ, d₂.gram_eq, d₁.gram_eq]
  change gramTransform (d₁.matrix⁻¹ * a * d₂.matrix)
      (gramTransform d₂.matrix⁻¹ (H.map (algebraMap k L))) =
    gramTransform d₁.matrix⁻¹ (H.map (algebraMap k L))
  simp only [gramTransform_mul, gramTransform_inv_right, ha]

omit [FiniteDimensional k L] [IsGalois k L] in
/-- A congruence of the descended forms gives an orthogonal cochain relating the cocycles. -/
theorem cohomologous_of_gramCongruent
    {c₁ c₂ : OrthogonalCocycle (L := L) H} (d₁ : Descent c₁) (d₂ : Descent c₂)
    (h : GramCongruent d₁.gram d₂.gram) : c₁.Cohomologous c₂ := by
  obtain ⟨Q, hQ⟩ := h
  let QL := GeneralLinearGroup.map (algebraMap k L) Q
  let a : GL n L := d₁.matrix * QL * d₂.matrix⁻¹
  have hforms : gramTransform QL (d₂.gram.map (algebraMap k L)) =
      d₁.gram.map (algebraMap k L) := by
    rw [← gramTransform_map, hQ]
  refine ⟨a, ?_, fun σ => ?_⟩
  · dsimp only [a]
    rw [gramTransform_mul, gramTransform_mul]
    rw [show gramTransform d₂.matrix⁻¹ (H.map (algebraMap k L)) =
      d₂.gram.map (algebraMap k L) from d₂.gram_eq.symm, hforms, d₁.gram_eq]
    change gramTransform d₁.matrix
      (gramTransform d₁.matrix⁻¹ (H.map (algebraMap k L))) = H.map (algebraMap k L)
    exact gramTransform_inv_right _ _
  · dsimp only [a, QL]
    rw [map_mul, map_mul, map_inv, d₁.map_matrix, d₂.map_matrix, map_ground_matrix]
    group

/-- Pairwise orthogonal cohomology is precisely ground-field congruence of the descended forms.
The result holds for any choices of descent data. -/
theorem cohomologous_iff_gramCongruent
    {c₁ c₂ : OrthogonalCocycle (L := L) H} (d₁ : Descent c₁) (d₂ : Descent c₂) :
    c₁.Cohomologous c₂ ↔ GramCongruent d₁.gram d₂.gram :=
  ⟨gramCongruent_of_cohomologous d₁ d₂, cohomologous_of_gramCongruent d₁ d₂⟩

end Langlands.LinearAlgebra.OrthogonalCocycleDescent
