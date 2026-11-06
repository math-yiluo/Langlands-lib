import Langlands.GroupScheme.MatrixRepresentation.AugmentationQuotients
import Langlands.GroupScheme.MatrixRepresentation.AdditiveFrobeniusAlgebra

/-! # Tensor irreducibility from actual augmentation quotient coefficients -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix Kronecker CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation.AdicTensorIrreducibility

open AugmentationQuotients AdditiveTensorAlgebra AdditiveTensorIrreducibility

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  (ρ : MatrixRepresentation G n)

/-- Linear coefficients of the actual representation at its augmentation quotient point. -/
def quotientCoefficientMap (N : ℕ) :
    (quotientAlgebra G N →ₗ[k] k) →ₗ[k] Matrix n n k where
  toFun ℓ := (ρ.affineMatrix (quotientAlgebra G N) (quotientPoint G N) :
    Matrix n n (quotientAlgebra G N)).map ℓ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem quotientCoefficientMap_mulVec (N : ℕ)
    (ℓ : quotientAlgebra G N →ₗ[k] k) (v : n → k) :
    quotientCoefficientMap ρ N ℓ *ᵥ v =
      fun i => ℓ (((ρ.affineMatrix (quotientAlgebra G N) (quotientPoint G N) :
        Matrix n n (quotientAlgebra G N)) *ᵥ
          (fun j => algebraMap k (quotientAlgebra G N) (v j))) i) := by
  funext i
  have hs (a : quotientAlgebra G N) (c : k) :
      ℓ (a * algebraMap k (quotientAlgebra G N) c) = ℓ a * c := by
    rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  change (∑ j, ℓ (ρ.affineMatrix _ _ i j) * v j) =
    ℓ (∑ j, ρ.affineMatrix _ _ i j * algebraMap k (quotientAlgebra G N) (v j))
  simp only [map_sum, hs]

theorem quotientCoefficientMap_mem_invariantAlgebra
    {W : Submodule k (n → k)} (hW : ρ.IsStableSubspace W) (N : ℕ)
    (ℓ : quotientAlgebra G N →ₗ[k] k) :
    quotientCoefficientMap ρ N ℓ ∈ invariantAlgebra W := by
  intro v hv
  rw [quotientCoefficientMap_mulVec]
  exact hW _ (quotientPoint G N) v hv ℓ

/-- A single augmentation quotient supplies every matrix of an irreducible representation. -/
theorem exists_quotientCoefficientMap_surjective [IsAlgClosed k] [IsReduced G.X.left]
    [LocallyOfFiniteType G.X.hom]
    [IsNoetherianRing (CharacterUnits.Coord G)] [IsDomain (CharacterUnits.Coord G)]
    (hρ : ρ.IsIrreducible) :
    ∃ N, Function.Surjective (quotientCoefficientMap ρ N) := by
  obtain ⟨N, hN⟩ := AffineCoefficients.exists_quotient_surjective ρ hρ
    (CoordinateWeights.augmentationIdeal G) CoordinateWeights.augmentationIdeal_ne_top
  refine ⟨N, fun M => ?_⟩
  obtain ⟨q, hq⟩ := hN M
  refine ⟨q, ?_⟩
  change (ρ.affineMatrix (quotientAlgebra G N) (quotientPoint G N) :
    Matrix n n (quotientAlgebra G N)).map q = M
  rw [affineMatrix_quotientPoint]
  exact hq

variable (σ : MatrixRepresentation G m)

/-- On a low augmentation quotient, tensor coefficients are the first matrix factor. -/
theorem quotientCoefficientMap_tensor_frobeniusPower (p : ℕ) [ExpChar k p]
    (N e : ℕ) (hN : N ≤ p ^ e) (ℓ : quotientAlgebra G N →ₗ[k] k) :
    quotientCoefficientMap (ρ.tensor (σ.frobeniusPower p e)) N ℓ =
      leftTensor (m := m) (quotientCoefficientMap ρ N ℓ) := by
  change ((ρ.tensor (σ.frobeniusPower p e)).affineMatrix
    (quotientAlgebra G N) (quotientPoint G N) :
      Matrix (n × m) (n × m) (quotientAlgebra G N)).map ℓ = _
  rw [tensor_affineMatrix, frobeniusPower_affineMatrix_quotientPoint σ p N e hN]
  ext ⟨i, a⟩ ⟨j, b⟩
  change ℓ (ρ.affineMatrix _ _ i j * (1 : Matrix m m (quotientAlgebra G N)) a b) =
    ℓ (ρ.affineMatrix _ _ i j) * (1 : Matrix m m k) a b
  by_cases hab : a = b
  · subst b
    simp only [Matrix.one_apply_eq, mul_one]
  · simp only [Matrix.one_apply_ne hab, mul_zero, map_zero]

/-- Surjective low quotient coefficients force invariance under the entire first matrix factor. -/
theorem leftTensor_mem_invariantAlgebra (p : ℕ) [ExpChar k p] (N e : ℕ)
    (hN : N ≤ p ^ e) (hsurj : Function.Surjective (quotientCoefficientMap ρ N))
    {W : Submodule k (n × m → k)}
    (hW : (ρ.tensor (σ.frobeniusPower p e)).IsStableSubspace W)
    (M : Matrix n n k) :
    leftTensor M ∈ invariantAlgebra W := by
  obtain ⟨ℓ, rfl⟩ := hsurj M
  rw [← quotientCoefficientMap_tensor_frobeniusPower ρ σ p N e hN]
  exact quotientCoefficientMap_mem_invariantAlgebra _ hW N ℓ

omit [IsAffineHom G.X.hom] in
theorem rationalMatrix_tensor (g : rationalPoints G) :
    ((ρ.tensor σ).rationalMatrix g : Matrix (n × m) (n × m) k) =
      (ρ.rationalMatrix g : Matrix n n k) ⊗ₖ (σ.rationalMatrix g : Matrix m m k) := by
  rw [rationalMatrix_eq_affineMatrix (ρ.tensor σ) g,
    rationalMatrix_eq_affineMatrix ρ g, rationalMatrix_eq_affineMatrix σ g,
    tensor_affineMatrix]
  rfl

omit [IsAffineHom G.X.hom] in
theorem rationalMatrix_frobeniusPower (p : ℕ) [ExpChar k p] (e : ℕ)
    (g : rationalPoints G) :
    ((σ.frobeniusPower p e).rationalMatrix g : Matrix m m k) =
      (σ.rationalMatrix g : Matrix m m k).map (characteristicPowerMap k p k e) := by
  rw [rationalMatrix_eq_affineMatrix (σ.frobeniusPower p e) g,
    frobeniusPower_affineMatrix, rationalMatrix_eq_affineMatrix σ g]
  rfl

/-- Invert the first rational matrix to isolate the second factor in the preserving algebra. -/
theorem rightTensor_rationalMatrix_mem_invariantAlgebra
    {W : Submodule k (n × m → k)} (hW : (ρ.tensor σ).IsStableSubspace W)
    (hl : ∀ M : Matrix n n k, leftTensor M ∈ invariantAlgebra W)
    (g : rationalPoints G) :
    rightTensor (n := n) (σ.rationalMatrix g : Matrix m m k) ∈ invariantAlgebra W := by
  have hd : ((ρ.tensor σ).rationalMatrix g : Matrix (n × m) (n × m) k) ∈
      invariantAlgebra W := fun _ hv => hW.rationalMatrix_mulVec_mem g hv
  rw [rationalMatrix_tensor] at hd
  have h := (invariantAlgebra W).mul_mem (hl (↑((ρ.rationalMatrix g)⁻¹))) hd
  change (((↑((ρ.rationalMatrix g)⁻¹) : Matrix n n k) ⊗ₖ (1 : Matrix m m k)) *
    ((ρ.rationalMatrix g : Matrix n n k) ⊗ₖ (σ.rationalMatrix g : Matrix m m k))) ∈
      invariantAlgebra W at h
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, ← Units.val_mul,
    inv_mul_cancel, Units.val_one] at h
  exact h

/-- Burnside and scalar Frobenius surjectivity recover the full second matrix factor. -/
theorem rightTensor_mem_invariantAlgebra [IsAlgClosed k] [IsReduced G.X.left]
    [LocallyOfFiniteType G.X.hom]
    (p : ℕ) [Fact p.Prime] [CharP k p] (e : ℕ) (hσ : σ.IsIrreducible)
    {W : Submodule k (n × m → k)}
    (hW : (ρ.tensor (σ.frobeniusPower p e)).IsStableSubspace W)
    (hl : ∀ M : Matrix n n k, leftTensor M ∈ invariantAlgebra W)
    (M : Matrix m m k) :
    rightTensor M ∈ invariantAlgebra W := by
  let B := (invariantAlgebra W).comap (rightTensor (n := n))
  let C := AdditiveFrobeniusAlgebra.scalarPreimage (characteristicPowerMap k p k e) B
  have hrep : σ.rationalRepresentation =
      Langlands.LinearAlgebra.matrixAction σ.rationalMatrix := by
    ext g v i
    rfl
  let : Representation.IsIrreducible
      (Langlands.LinearAlgebra.matrixAction σ.rationalMatrix) :=
    hrep ▸ hσ.rationalRepresentation
  have hfull := Langlands.LinearAlgebra.matrix_span_eq_top_of_irreducible σ.rationalMatrix
  have hspan : Submodule.span k
      (Set.range fun g => (σ.rationalMatrix g : Matrix m m k)) ≤ C.toSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    change rightTensor ((σ.rationalMatrix g : Matrix m m k).map
      (characteristicPowerMap k p k e)) ∈ invariantAlgebra W
    rw [← rationalMatrix_frobeniusPower]
    exact rightTensor_rationalMatrix_mem_invariantAlgebra ρ _ hW hl g
  have hC (T : Matrix m m k) : T ∈ C := by
    apply hspan
    rw [hfull]
    trivial
  obtain ⟨T, hT⟩ := (iterateFrobeniusEquiv k p e).mapMatrix.surjective M
  change T.map (characteristicPowerMap k p k e) = M at hT
  have h := hC T
  change rightTensor (T.map (characteristicPowerMap k p k e)) ∈ invariantAlgebra W at h
  rwa [hT] at h

omit [IsAffineHom G.X.hom] in
/-- Stability under every matrix forces a coordinate subspace to be zero or full. -/
theorem eq_bot_or_eq_top_of_invariantAlgebra_eq_top
    (W : Submodule k (n → k)) (hfull : invariantAlgebra W = ⊤) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  by_cases hW0 : W = ⊥
  · exact Or.inl hW0
  right
  obtain ⟨v, hv, hv0⟩ := W.ne_bot_iff.mp hW0
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv0
  change v j ≠ 0 at hj
  apply top_unique
  intro w _
  let M : Matrix n n k := fun i l => if l = j then w i / v j else 0
  have hMv : M *ᵥ v = w := by
    funext i
    change (∑ l, M i l * v l) = w i
    rw [Finset.sum_eq_single j]
    · simp [M, div_mul_cancel₀ _ hj]
    · intro l _ hlj
      simp [M, hlj]
    · intro h
      exact (h (Finset.mem_univ j)).elim
  have hM : M ∈ invariantAlgebra W := by
    rw [hfull]
    trivial
  rw [← hMv]
  exact hM v hv

/-- One surjective augmentation quotient proves the actual Frobenius tensor criterion. -/
theorem isIrreducible_tensor_frobeniusPower [IsAlgClosed k] [IsReduced G.X.left]
    [LocallyOfFiniteType G.X.hom]
    (p : ℕ) [Fact p.Prime] [CharP k p] (N e : ℕ) (hN : N ≤ p ^ e)
    (hρ : ρ.IsIrreducible) (hσ : σ.IsIrreducible)
    (hsurj : Function.Surjective (quotientCoefficientMap ρ N)) :
    (ρ.tensor (σ.frobeniusPower p e)).IsIrreducible := by
  let := hρ.nonempty_coordinates
  let := hσ.nonempty_coordinates
  refine ⟨inferInstance, fun W hW => ?_⟩
  have hl := leftTensor_mem_invariantAlgebra ρ σ p N e hN hsurj hW
  have hr := rightTensor_mem_invariantAlgebra ρ σ p e hσ hW hl
  exact eq_bot_or_eq_top_of_invariantAlgebra_eq_top W
    (eq_top_of_leftTensor_mem_of_rightTensor_mem (invariantAlgebra W) hl hr)

/-- A fixed first irreducible representation has one bound valid for every second one. -/
theorem exists_forall_isIrreducible_tensor_frobeniusPower [IsAlgClosed k]
    [IsReduced G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsNoetherianRing (CharacterUnits.Coord G)] [IsDomain (CharacterUnits.Coord G)]
    (p : ℕ) [Fact p.Prime] [CharP k p] (hρ : ρ.IsIrreducible) :
    ∃ E, ∀ e, E ≤ e →
      ∀ {m : Type} [Fintype m] [DecidableEq m]
        (σ : MatrixRepresentation G m), σ.IsIrreducible →
          (ρ.tensor (σ.frobeniusPower p e)).IsIrreducible := by
  obtain ⟨N, hN⟩ := exists_quotientCoefficientMap_surjective ρ hρ
  refine ⟨N, ?_⟩
  intro e he m _ _ σ hσ
  exact isIrreducible_tensor_frobeniusPower ρ σ p N e
    (he.trans (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le) hρ hσ hN

/-- Smooth connected affine groups satisfy the coordinate hypotheses of the general theorem. -/
theorem exists_forall_isIrreducible_tensor_frobeniusPower_of_smooth [IsAlgClosed k]
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (p : ℕ) [Fact p.Prime] [CharP k p] (hρ : ρ.IsIrreducible) :
    ∃ E, ∀ e, E ≤ e →
      ∀ {m : Type} [Fintype m] [DecidableEq m]
        (σ : MatrixRepresentation G m), σ.IsIrreducible →
          (ρ.tensor (σ.frobeniusPower p e)).IsIrreducible := by
  let := CoordinateWeights.isNoetherianRing_coord (G := G)
  let := CharacterLatticeProof.isDomain_coord G
  let : IsLocallyNoetherian G.X.left := LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  let : IsIntegral G.X.left := CharacterLatticeProof.isIntegral_of_smooth k G.X.hom
  exact exists_forall_isIrreducible_tensor_frobeniusPower ρ p hρ

/-- The same uniform bound gives rational-point irreducibility on the entire tensor space. -/
theorem exists_forall_rationalRepresentation_isIrreducible_tensor_frobeniusPower_of_smooth
    [IsAlgClosed k] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (hρ : ρ.rationalRepresentation.IsIrreducible) :
    ∃ E, ∀ e, E ≤ e →
      ∀ {m : Type} [Fintype m] [DecidableEq m]
        (σ : MatrixRepresentation G m), σ.rationalRepresentation.IsIrreducible →
          (ρ.tensor (σ.frobeniusPower p e)).rationalRepresentation.IsIrreducible := by
  let : IsLocallyNoetherian G.X.left := LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  let : IsIntegral G.X.left := CharacterLatticeProof.isIntegral_of_smooth k G.X.hom
  obtain ⟨E, hE⟩ := exists_forall_isIrreducible_tensor_frobeniusPower_of_smooth ρ p
    (isIrreducible_of_rationalRepresentation ρ hρ)
  refine ⟨E, ?_⟩
  intro e he m _ _ σ hσ
  exact (hE e he σ (isIrreducible_of_rationalRepresentation σ hσ)).rationalRepresentation

/-- Each supplied irreducible pair has cofinally many irreducible Frobenius tensors. -/
theorem exists_ge_rationalRepresentation_isIrreducible_tensor_frobeniusPower_of_smooth
    [IsAlgClosed k] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (hρ : ρ.rationalRepresentation.IsIrreducible)
    (hσ : σ.rationalRepresentation.IsIrreducible) (N : ℕ) :
    ∃ e, N ≤ e ∧
      (ρ.tensor (σ.frobeniusPower p e)).rationalRepresentation.IsIrreducible := by
  obtain ⟨E, hE⟩ :=
    exists_forall_rationalRepresentation_isIrreducible_tensor_frobeniusPower_of_smooth ρ p hρ
  exact ⟨max N E, le_max_left N E, hE _ (le_max_right N E) σ hσ⟩

end Langlands.GroupScheme.MatrixRepresentation.AdicTensorIrreducibility
