import Langlands.GroupScheme.Rational.InvariantCoordinateIntegral
import Langlands.GroupScheme.MatrixRepresentation.MinimalStableSubrepresentation
import Mathlib.LinearAlgebra.Projection

/-! # Averaging projections into actual stable subspaces -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.MatrixRepresentation

open CoordinateIntegration

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]

/-- The actual representation matrix at an affine point. -/
abbrev integralMatrix (ρ : MatrixRepresentation G n)
    {A : Type u} [CommRing A] [Algebra k A] (x : Lie.AffinePoints G A) : GL n A :=
  ρ.affineMatrix (CommAlgCat.of k A) x

omit [IsAffineHom G.X.hom] in
theorem integralMatrix_naturality (ρ : MatrixRepresentation G n)
    {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (f : A →ₐ[k] B) (x : Lie.AffinePoints G A) :
    integralMatrix ρ (Lie.affineMap G f x) =
      Matrix.GeneralLinearGroup.map f.toRingHom (integralMatrix ρ x) :=
  ρ.affineMatrix_naturality (CommAlgCat.ofHom f) x

/-- Conjugate a ground-field endomorphism by an actual affine point. -/
def conjugateMatrix (ρ : MatrixRepresentation G n) (P : Matrix n n k)
    {A : Type u} [CommRing A] [Algebra k A] (x : Lie.AffinePoints G A) :
    Matrix n n A :=
  (integralMatrix ρ x : Matrix n n A) * P.map (algebraMap k A) *
    (integralMatrix ρ x⁻¹ : Matrix n n A)

omit [IsAffineHom G.X.hom] in
theorem conjugateMatrix_naturality (ρ : MatrixRepresentation G n) (P : Matrix n n k)
    {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (f : A →ₐ[k] B) (x : Lie.AffinePoints G A) :
    (conjugateMatrix ρ P x).map f = conjugateMatrix ρ P (Lie.affineMap G f x) := by
  unfold conjugateMatrix
  rw [← map_inv (Lie.affineMap G f) x, integralMatrix_naturality,
    integralMatrix_naturality]
  change ((integralMatrix ρ x : Matrix n n A) * P.map (algebraMap k A) *
    (integralMatrix ρ x⁻¹ : Matrix n n A)).map f =
      (integralMatrix ρ x : Matrix n n A).map f * P.map (algebraMap k B) *
        (integralMatrix ρ x⁻¹ : Matrix n n A).map f
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 1
  congr 1
  ext i j
  exact f.commutes _

/-- The universal point over its own coordinate algebra. -/
def integralUniversalPoint : Lie.AffinePoints G (Coord G) :=
  (Lie.pointCoordinates G).symm (AlgHom.id k (Coord G))

theorem integralUniversalPoint_map (A : Type u) [CommRing A] [Algebra k A] :
    Lie.affineMap G
      (Algebra.TensorProduct.includeRight : Coord G →ₐ[k] A ⊗[k] Coord G)
      integralUniversalPoint = universalPoint G A := by
  apply (Lie.pointCoordinates G).injective
  rw [Lie.pointCoordinates_naturality, integralUniversalPoint,
    Equiv.apply_symm_apply, universalPoint, Equiv.apply_symm_apply, AlgHom.comp_id]

/-- Average the universal conjugates of a ground-field endomorphism. -/
def averagedMatrix (ρ : MatrixRepresentation G n) (I : InvariantIntegral G)
    (P : Matrix n n k) : Matrix n n k :=
  (conjugateMatrix ρ P integralUniversalPoint).map I.linearForm

omit [DecidableEq n] in
theorem contract_matrix_mul_left
    {A : Type u} [CommRing A] [Algebra k A]
    (ℓ : Coord G →ₗ[k] k) (M : Matrix n n A)
    (Q : Matrix n n (A ⊗[k] Coord G)) :
    (M.map (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] Coord G) * Q).map
        (contract G A ℓ) = M * Q.map (contract G A ℓ) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, map_sum]
  apply Finset.sum_congr rfl
  intro l hl
  change contract G A ℓ (algebraMap A (A ⊗[k] Coord G) (M i l) * Q l j) = _
  rw [← Algebra.smul_def, map_smul]
  rfl

omit [DecidableEq n] in
theorem contract_matrix_mul_right
    {A : Type u} [CommRing A] [Algebra k A]
    (ℓ : Coord G →ₗ[k] k) (M : Matrix n n A)
    (Q : Matrix n n (A ⊗[k] Coord G)) :
    (Q * M.map (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] Coord G)).map
        (contract G A ℓ) = Q.map (contract G A ℓ) * M := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, map_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [mul_comm (Q i l)]
  change contract G A ℓ (algebraMap A (A ⊗[k] Coord G) (M l j) * Q i l) = _
  rw [← Algebra.smul_def, map_smul]
  exact mul_comm _ _

theorem averagedMatrix_baseChange (ρ : MatrixRepresentation G n)
    (I : InvariantIntegral G) (P : Matrix n n k)
    (A : Type u) [CommRing A] [Algebra k A] :
    (conjugateMatrix ρ P (universalPoint G A)).map (I.average (A := A)) =
      (averagedMatrix ρ I P).map (algebraMap k A) := by
  rw [← integralUniversalPoint_map A, ← conjugateMatrix_naturality]
  ext i j
  simp [averagedMatrix, InvariantIntegral.average,
    Algebra.TensorProduct.includeRight_apply]

omit [IsAffineHom G.X.hom] in
theorem conjugateMatrix_mul (ρ : MatrixRepresentation G n) (P : Matrix n n k)
    {A : Type u} [CommRing A] [Algebra k A] (x y : Lie.AffinePoints G A) :
    conjugateMatrix ρ P (x * y) =
      (integralMatrix ρ x : Matrix n n A) * conjugateMatrix ρ P y *
        (integralMatrix ρ x⁻¹ : Matrix n n A) := by
  simp only [conjugateMatrix, integralMatrix, map_mul, mul_inv_rev,
    Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_assoc]

/-- The averaged endomorphism intertwines on every affine test algebra. -/
theorem averagedMatrix_intertwines (ρ : MatrixRepresentation G n)
    (I : InvariantIntegral G) (P : Matrix n n k) :
    Intertwines ρ ρ (averagedMatrix ρ I P) := by
  intro A t
  let Q := conjugateMatrix ρ P (universalPoint G A)
  let M : Matrix n n A := integralMatrix ρ t
  let N : Matrix n n A := integralMatrix ρ t⁻¹
  have htrans :
      Q.map ((leftTranslation G A t).restrictScalars k) =
        M.map (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] Coord G) *
          Q * N.map (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] Coord G) := by
    dsimp only [Q]
    rw [conjugateMatrix_naturality, leftTranslation_universalPoint,
      conjugateMatrix_mul, ← map_inv, integralMatrix_naturality,
      integralMatrix_naturality]
    rfl
  have hi : (Q.map ((leftTranslation G A t).restrictScalars k)).map
      (I.average (A := A)) = Q.map (I.average (A := A)) := by
    ext i j
    exact I.left_invariant A t (Q i j)
  rw [htrans, contract_matrix_mul_right, contract_matrix_mul_left,
    averagedMatrix_baseChange] at hi
  have hNM : N * M = 1 := by
    change (integralMatrix ρ t⁻¹ : Matrix n n A) *
      (integralMatrix ρ t : Matrix n n A) = 1
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  change (averagedMatrix ρ I P).map (algebraMap k A) * M =
    M * (averagedMatrix ρ I P).map (algebraMap k A)
  calc
    _ = (M * (averagedMatrix ρ I P).map (algebraMap k A) * N) * M :=
      congrArg (· * M) hi.symm
    _ = _ := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hNM, Matrix.mul_one]

omit [DecidableEq n] [IsAffineHom G.X.hom] in
theorem linearFunctional_matrix_mul_right
    {A : Type u} [CommRing A] [Algebra k A]
    (ℓ : A →ₗ[k] k) (P : Matrix n n k) (Q : Matrix n n A) :
    (Q * P.map (algebraMap k A)).map ℓ = Q.map ℓ * P := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, map_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [mul_comm (Q i l)]
  change ℓ (algebraMap k A (P l j) * Q i l) = _
  rw [← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

omit [DecidableEq n] [IsAffineHom G.X.hom] in
theorem linearFunctional_matrix_mul_left
    {A : Type u} [CommRing A] [Algebra k A]
    (ℓ : A →ₗ[k] k) (P : Matrix n n k) (Q : Matrix n n A) :
    (P.map (algebraMap k A) * Q).map ℓ = P * Q.map ℓ := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, map_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

omit [IsAffineHom G.X.hom] in
theorem IsStableSubspace.projection_matrix
    {ρ : MatrixRepresentation G n} {W : Submodule k (n → k)}
    (hW : ρ.IsStableSubspace W) (P : Matrix n n k)
    (hcols : ∀ j, (fun i => P i j) ∈ W)
    (hproj : ∀ v, v ∈ W → P *ᵥ v = v)
    {A : Type u} [CommRing A] [Algebra k A] (x : Lie.AffinePoints G A) :
    P.map (algebraMap k A) * (integralMatrix ρ x : Matrix n n A) *
      P.map (algebraMap k A) =
        (integralMatrix ρ x : Matrix n n A) * P.map (algebraMap k A) := by
  rw [Matrix.mul_assoc]
  ext i j
  exact congrFun (projection_mulVec_eq_of_coefficients P
    ((integralMatrix ρ x : Matrix n n A) *ᵥ
      (fun l => algebraMap k A (P l j)))
    (fun ℓ => hproj _ (hW (CommAlgCat.of k A) x _ (hcols j) ℓ))) i

/-- Averaging a projection still has image in the chosen stable subspace and
restricts to the identity there. -/
theorem averagedMatrix_projection
    {ρ : MatrixRepresentation G n} (I : InvariantIntegral G)
    {W : Submodule k (n → k)} (hW : ρ.IsStableSubspace W)
    (P : Matrix n n k) (hcols : ∀ j, (fun i => P i j) ∈ W)
    (hproj : ∀ v, v ∈ W → P *ᵥ v = v) :
    P * averagedMatrix ρ I P = averagedMatrix ρ I P ∧
      averagedMatrix ρ I P * P = P := by
  let x : Lie.AffinePoints G (Coord G) := integralUniversalPoint
  let Pa := P.map (algebraMap k (Coord G))
  let M : Matrix n n (Coord G) := integralMatrix ρ x
  let N : Matrix n n (Coord G) := integralMatrix ρ x⁻¹
  have hs : Pa * M * Pa = M * Pa := hW.projection_matrix P hcols hproj x
  have ht : Pa * N * Pa = N * Pa := hW.projection_matrix P hcols hproj x⁻¹
  have hMN : M * N = 1 := by
    change (integralMatrix ρ x : Matrix n n (Coord G)) *
      (integralMatrix ρ x⁻¹ : Matrix n n (Coord G)) = 1
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hleft : Pa * conjugateMatrix ρ P x = conjugateMatrix ρ P x := by
    change Pa * (M * Pa * N) = M * Pa * N
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hs]
  have hright : conjugateMatrix ρ P x * Pa = Pa := by
    change M * Pa * N * Pa = Pa
    calc
      _ = M * (Pa * N * Pa) := by simp only [Matrix.mul_assoc]
      _ = M * (N * Pa) := by rw [ht]
      _ = Pa := by rw [← Matrix.mul_assoc, hMN, Matrix.one_mul]
  have hnorm : Pa.map I.linearForm = P := by
    ext i j
    change I.linearForm (algebraMap k (Coord G) (P i j)) = P i j
    have hc : algebraMap k (Coord G) (P i j) = (P i j) • (1 : Coord G) := by
      simp [Algebra.smul_def]
    rw [hc, map_smul, I.map_one, smul_eq_mul, mul_one]
  constructor
  · have h := congrArg (fun Q => Q.map I.linearForm) hleft
    rw [linearFunctional_matrix_mul_left] at h
    exact h
  · have h := congrArg (fun Q => Q.map I.linearForm) hright
    rw [linearFunctional_matrix_mul_right, hnorm] at h
    exact h

/-- Every actual stable subspace has an actual stable complement when the group
admits a normalized invariant coordinate integral. -/
theorem IsStableSubspace.exists_stable_complement
    {ρ : MatrixRepresentation G n} (I : InvariantIntegral G)
    {W : Submodule k (n → k)} (hW : ρ.IsStableSubspace W) :
    ∃ U : Submodule k (n → k), ρ.IsStableSubspace U ∧ IsCompl W U := by
  classical
  obtain ⟨d, B, C, hCB, hcols, hproj⟩ := exists_subspace_split_coordinates W
  let P := B * C
  have hrange : LinearMap.range B.mulVecLin = W :=
    range_coordinateInclusion_eq W B C hcols hproj
  have hPmem (v : n → k) : P *ᵥ v ∈ W := by
    rw [← hrange]
    refine ⟨C *ᵥ v, ?_⟩
    exact Matrix.mulVec_mulVec v B C
  have hPcols : ∀ j, (fun i => P i j) ∈ W := by
    intro j
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply'] using hPmem (Pi.single j 1)
  obtain ⟨hPQ, hQP⟩ := averagedMatrix_projection I hW P hPcols hproj
  let Q := averagedMatrix ρ I P
  have hQmem (v : n → k) : Q *ᵥ v ∈ W := by
    have h := hPmem (Q *ᵥ v)
    rw [Matrix.mulVec_mulVec, hPQ] at h
    exact h
  have hQfix (v : n → k) (hv : v ∈ W) : Q *ᵥ v = v := by
    rw [← hproj v hv, Matrix.mulVec_mulVec, hQP, hproj v hv]
  let f : (n → k) →ₗ[k] W := Q.mulVecLin.codRestrict W hQmem
  have hf (v : W) : f v = v := Subtype.ext (hQfix v v.property)
  refine ⟨LinearMap.ker Q.mulVecLin, ?_, ?_⟩
  · exact (isStableSubspace_bot ρ).comap (averagedMatrix_intertwines ρ I P)
  · have h := LinearMap.isCompl_of_proj hf
    change IsCompl W (LinearMap.ker (Q.mulVecLin.codRestrict W hQmem)) at h
    rw [LinearMap.ker_codRestrict] at h
    exact h

end Langlands.GroupScheme.MatrixRepresentation
