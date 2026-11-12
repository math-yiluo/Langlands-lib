import Langlands.GroupScheme.Quaternionic.SymplecticPoints
import Langlands.GroupScheme.FiniteAlgebraWeightedDynamic
import Langlands.GroupScheme.Dynamic.ParabolicLieCriterion

/-!
# Contracting cocharacters of quaternionic symplectic groups

For distinct indices `a, b`, the weighted cocharacter `t ↦ diag(t^{w i})` of the unit group of
`M_n(D)` with weight `w = pairWeight a b` (`1` at `a`, `-1` at `b`, `0` elsewhere) has reduced
norm one: it is the commutator `μ(t) (π μ(t) π⁻¹)⁻¹` of the cocharacter `μ` with weight `1` at
`a` and its conjugate by the transposition matrix `π`, and the reduced norm takes values in a
commutative group. If the Gram matrix `H₀` has `w i + w j = 0` wherever `H₀ i j ≠ 0`, every
value of the cocharacter is an isometry of `H₀`. The cocharacter therefore factors through the
symplectic group of `H₀`.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.Quaternionic

open FiniteAlgebraUnits FiniteAlgebraUnits.WeightedRoot

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  [Algebra.IsCentral K D] {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]

omit [Algebra.IsCentral K D] [Nonempty n] in
/-- The unit of `R ⊗ M_n(D)` underlying a point, transported to matrices over `R ⊗ D`. -/
theorem tensorMatrixEquiv_val_eq {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ (FirstKindInvolution.ambientUnits K D n).X) :
    ((MatrixPoints.tensorMatrixEquiv K D (Module.finBasis K (Matrix n n D)) T x :
        Matrix.GeneralLinearGroup n (((algΓ (CommRingCat.of K)).obj T).unop ⊗[K] D)) :
        Matrix n n (((algΓ (CommRingCat.of K)).obj T).unop ⊗[K] D)) =
      MatrixPoints.coefficientEquiv K D ((algΓ (CommRingCat.of K)).obj T).unop
        (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K (Matrix n n D)) T x :
          ((algΓ (CommRingCat.of K)).obj T).unop ⊗[K] Matrix n n D) :=
  rfl

omit [Algebra.IsCentral K D] [Nonempty n] in
/-- The constant transposition point has the transposition matrix. -/
theorem tensorMatrixEquiv_constPoint_swapUnit (a b : n) (T : Over (Spec (CommRingCat.of K))) :
    MatrixPoints.tensorMatrixEquiv K D (Module.finBasis K (Matrix n n D)) T
        (FirstKindInvolution.constPoint (swapUnit a b) T) = swapUnit a b := by
  apply Units.ext
  rw [tensorMatrixEquiv_val_eq, FirstKindInvolution.pointsEquiv_constPoint]
  change MatrixPoints.coefficientEquiv K D _ ((1 : ((algΓ (CommRingCat.of K)).obj T).unop) ⊗ₜ[K]
    (swapMatrix a b : Matrix n n D)) = _
  rw [FirstKindInvolution.coefficientEquiv_one_tmul_eq_map]
  exact congrArg Units.val
    (map_swapUnit (S := D) (S' := ((algΓ (CommRingCat.of K)).obj T).unop ⊗[K] D)
      (Algebra.TensorProduct.includeRight : D →ₐ[K] _).toRingHom a b)

variable (K D) in
/-- The weighted cocharacter of the unit group of `M_n(D)`. -/
abbrev ambientCocharacter (w : n → ℤ) :
    (Gm (Spec (CommRingCat.of K))).toGrp ⟶ FirstKindInvolution.ambientUnits K D n :=
  cocharacter K D (Module.finBasis K (Matrix n n D)) w

/-- The cocharacter with weight `pairWeight a b` has reduced norm one. -/
theorem ambientCocharacter_pairWeight_reducedNorm (a b : n) {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ (Gm (Spec (CommRingCat.of K))).X) :
    (x ≫ (ambientCocharacter K D (pairWeight a b)).hom.hom) ≫
      (CentralSimpleUnits.reducedNormHom K (Matrix n n D)).hom.hom = 1 := by
  set m := x ≫ (ambientCocharacter K D (n := n) (indicatorWeight a)).hom.hom
  set p := FirstKindInvolution.constPoint (K := K) (D := D) (swapUnit a b) T
  have e : x ≫ (ambientCocharacter K D (pairWeight a b)).hom.hom = m * (p * m * p⁻¹)⁻¹ := by
    apply (MatrixPoints.tensorMatrixEquiv K D (Module.finBasis K (Matrix n n D)) T).injective
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, tensorMatrixEquiv_cocharacter,
      tensorMatrixEquiv_cocharacter, tensorMatrixEquiv_constPoint_swapUnit]
    exact weightMatrix_pairWeight (R := ((algΓ (CommRingCat.of K)).obj T).unop) a b _
  rw [e, MonObj.mul_comp, GrpObj.inv_comp, MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]
  apply (Gm.pointsEquiv (Spec (CommRingCat.of K)) T).injective
  rw [map_mul, map_inv, map_mul, map_mul, map_inv, map_one, mul_inv_cancel_comm,
    mul_inv_cancel]

namespace FirstKindInvolution

variable (σ : FirstKindInvolution K D)

section Algebra

variable {R S : Type u} [CommRing R] [Ring S] [Algebra R S]

omit [Nonempty n] in
/-- The weighted diagonal is fixed by the conjugate transpose of any involution. -/
theorem matrix_weightMatrix (ε : FirstKindInvolution R S) (w : n → ℤ) (t : Rˣ) :
    ε.matrix n ((weightMatrix w t : Matrix.GeneralLinearGroup n S) : Matrix n n S) =
      (weightMatrix w t : Matrix.GeneralLinearGroup n S) := by
  ext i j
  rw [matrix_apply]
  change ε (Matrix.diagonal (fun i => algebraMap R S ((t ^ w i : Rˣ) : R)) j i) =
    Matrix.diagonal (fun i => algebraMap R S ((t ^ w i : Rˣ) : R)) i j
  by_cases h : i = j
  · subst h
    simp only [Matrix.diagonal_apply_eq, map_algebraMap]
  · simp only [Matrix.diagonal_apply_ne _ (Ne.symm h), Matrix.diagonal_apply_ne _ h, ε.map_zero]

omit [Nonempty n] in
/-- The weighted diagonal preserves a Gram matrix supported where the weights add to zero. -/
theorem weightMatrix_mul_mul_weightMatrix (w : n → ℤ) (t : Rˣ) (G : Matrix n n S)
    (hG : ∀ i j, G i j ≠ 0 → w i + w j = 0) :
    ((weightMatrix w t : Matrix.GeneralLinearGroup n S) : Matrix n n S) * G *
        (weightMatrix w t : Matrix.GeneralLinearGroup n S) = G := by
  ext i j
  rw [weightMatrix_val, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : G i j = 0
  · rw [h, mul_zero, zero_mul]
  · rw [mul_assoc, ← Algebra.commutes, ← mul_assoc, ← _root_.map_mul, ← Units.val_mul,
      ← zpow_add, hG i j h, zpow_zero, Units.val_one, _root_.map_one, one_mul]

omit [Nonempty n] in
/-- The weighted diagonal is an isometry of a Gram matrix supported where the weights add to
zero, for any involution of the first kind. -/
theorem weightMatrix_isometry (ε : FirstKindInvolution R S) (w : n → ℤ) (t : Rˣ)
    (G : Matrix n n S) (hG : ∀ i j, G i j ≠ 0 → w i + w j = 0) :
    ((weightMatrix w t : Matrix.GeneralLinearGroup n S) : Matrix n n S) * G *
        ε.matrix n ((weightMatrix w t : Matrix.GeneralLinearGroup n S) : Matrix n n S) = G := by
  rw [matrix_weightMatrix]
  exact weightMatrix_mul_mul_weightMatrix w t G hG

end Algebra

omit [Algebra.IsCentral K D] [Nonempty n] in
/-- The weighted cocharacter takes values in the unitary group of a Gram matrix supported where
the weights add to zero. -/
theorem ambientCocharacter_mem_range_unitaryGroupι (H₀ : Matrix n n D) (w : n → ℤ)
    (hH : ∀ i j, H₀ i j ≠ 0 → w i + w j = 0) {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ (Gm (Spec (CommRingCat.of K))).X) :
    x ≫ (ambientCocharacter K D w).hom.hom ∈
      (SubgroupFunctor.range (σ.unitaryGroupι H₀)).carrier T := by
  rw [mem_range_unitaryGroupι_iff, isometry_iff_coefficientEquiv, ← tensorMatrixEquiv_val_eq,
    tensorMatrixEquiv_cocharacter]
  exact weightMatrix_isometry (R := ((algΓ (CommRingCat.of K)).obj T).unop)
    (σ.baseChange ((algΓ (CommRingCat.of K)).obj T).unop) w _ _
    (fun i j h => hH i j (fun h0 => h (by rw [Matrix.map_apply, h0, _root_.map_zero])))

/-- The cocharacter with weight `pairWeight a b` of the symplectic group of a Gram matrix
supported where these weights add to zero. -/
def symplecticCocharacter (H₀ : Matrix n n D) (a b : n)
    (hH : ∀ i j, H₀ i j ≠ 0 → pairWeight a b i + pairWeight a b j = 0) :
    (Gm (Spec (CommRingCat.of K))).toGrp ⟶ σ.symplecticGroup H₀ :=
  (σ.isRepresentedBy_symplecticAmbientι H₀).liftOfLE (ambientCocharacter K D (pairWeight a b))
    (by
      intro T x hx
      obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
      rw [mem_range_symplecticAmbientι_iff]
      exact ⟨σ.ambientCocharacter_mem_range_unitaryGroupι H₀ _ hH y,
        ambientCocharacter_pairWeight_reducedNorm a b y⟩)

theorem symplecticCocharacter_comp (H₀ : Matrix n n D) (a b : n)
    (hH : ∀ i j, H₀ i j ≠ 0 → pairWeight a b i + pairWeight a b j = 0) :
    σ.symplecticCocharacter H₀ a b hH ≫ σ.symplecticAmbientι H₀ =
      ambientCocharacter K D (pairWeight a b) :=
  SubgroupFunctor.IsRepresentedBy.liftOfLE_comp _ _ _

end FirstKindInvolution

end Langlands.GroupScheme.Quaternionic
