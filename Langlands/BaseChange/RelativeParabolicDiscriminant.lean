import Langlands.BaseChange.WeylIntegrationData
import Langlands.Group.GL.Blocks
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Relative discriminants for a standard Levi of `GL_n`

The ordinary and twisted determinants on the quotient by the block diagonal
Lie algebra, with the orientations of Henniart–Lemaire, II.4.5.
-/

namespace Langlands.BaseChange

open Langlands.GeneralLinear (BlockShape)

universe u v

variable {n : ℕ} (B : BlockShape n) (K : Type u) [Field K]

/-- The matrix positions between distinct blocks of `B`. -/
abbrev OffBlockPosition := {p : Fin n × Fin n // B.coordinateBlock p.1 ≠ B.coordinateBlock p.2}

/-- Restrict a matrix in standard coordinates to the positions between distinct blocks. -/
def offBlockEntries : Matrix (Fin n) (Fin n) K →ₗ[K] (OffBlockPosition B → K) where
  toFun A p := A p.val.1 p.val.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem offBlockEntries_apply (A : Matrix (Fin n) (Fin n) K) (p : OffBlockPosition B) :
    offBlockEntries B K A p = A p.val.1 p.val.2 := rfl

private theorem offBlockEntries_surjective : Function.Surjective (offBlockEntries B K) := by
  intro a
  refine ⟨fun i j => if h : B.coordinateBlock i ≠ B.coordinateBlock j then
    a ⟨(i, j), h⟩ else 0, ?_⟩
  funext p
  change (if h : B.coordinateBlock p.val.1 ≠ B.coordinateBlock p.val.2 then
    a ⟨p.val, h⟩ else 0) = a p
  simp [p.property]

/-- The block diagonal Lie algebra inside the full matrix Lie algebra. -/
def blockDiagonalLieSubmodule : Submodule K (Matrix (Fin n) (Fin n) K) :=
  (offBlockEntries B K).ker

@[simp]
theorem mem_blockDiagonalLieSubmodule (A : Matrix (Fin n) (Fin n) K) :
    A ∈ blockDiagonalLieSubmodule B K ↔
      ∀ i j, B.coordinateBlock i ≠ B.coordinateBlock j → A i j = 0 := by
  change offBlockEntries B K A = 0 ↔ _
  constructor
  · intro h i j hij
    exact congrFun h ⟨(i, j), hij⟩
  · intro h
    funext p
    exact h p.val.1 p.val.2 p.property

/-- The quotient `𝔤(K)/𝔪(K)` for the actual standard block Levi. -/
abbrev RelativeParabolicLieQuotient := Matrix (Fin n) (Fin n) K ⧸ blockDiagonalLieSubmodule B K

/-- The quotient is identified with the space of off-block entries by restriction. -/
noncomputable def relativeParabolicLieCoordinates :
    RelativeParabolicLieQuotient B K ≃ₗ[K] (OffBlockPosition B → K) :=
  (offBlockEntries B K).quotKerEquivOfSurjective (offBlockEntries_surjective B K)

@[simp]
theorem relativeParabolicLieCoordinates_mk (A : Matrix (Fin n) (Fin n) K) :
    relativeParabolicLieCoordinates B K (Submodule.Quotient.mk A) = offBlockEntries B K A :=
  (offBlockEntries B K).quotKerEquivOfSurjective_apply_mk _ A

private theorem blockDiagonalLieSubmodule_mul {A C : Matrix (Fin n) (Fin n) K}
    (hA : A ∈ blockDiagonalLieSubmodule B K) (hC : C ∈ blockDiagonalLieSubmodule B K) :
    A * C ∈ blockDiagonalLieSubmodule B K := by
  rw [mem_blockDiagonalLieSubmodule] at hA hC ⊢
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases h : B.coordinateBlock i = B.coordinateBlock k
  · rw [hC k j (fun hkj => hij (h.trans hkj)), mul_zero]
  · rw [hA i k h, zero_mul]

private theorem leviEmbedding_mem_blockDiagonalLieSubmodule (m : B.Levi K) :
    (B.leviEmbedding K m).val ∈ blockDiagonalLieSubmodule B K := by
  rw [mem_blockDiagonalLieSubmodule]
  intro a b hab
  obtain ⟨⟨i, x⟩, rfl⟩ := B.indexEquiv.surjective a
  obtain ⟨⟨j, y⟩, rfl⟩ := B.indexEquiv.surjective b
  exact B.leviEmbedding_apply_ne K m x y (by simpa [BlockShape.coordinateBlock] using hab)

private theorem linearAdjoint_preserves_blockDiagonalLie (m : B.Levi K)
    {A : Matrix (Fin n) (Fin n) K} (hA : A ∈ blockDiagonalLieSubmodule B K) :
    linearAdjoint (B.leviEmbedding K m) A ∈ blockDiagonalLieSubmodule B K := by
  change (B.leviEmbedding K m).val * (A * (B.leviEmbedding K m)⁻¹.val) ∈ _
  rw [← map_inv]
  exact blockDiagonalLieSubmodule_mul B K (leviEmbedding_mem_blockDiagonalLieSubmodule B K m)
    (blockDiagonalLieSubmodule_mul B K hA (leviEmbedding_mem_blockDiagonalLieSubmodule B K m⁻¹))

/-- The adjoint action of the embedded Levi element induced on the quotient. -/
def relativeParabolicAdjoint (m : B.Levi K) : Module.End K (RelativeParabolicLieQuotient B K) :=
  (blockDiagonalLieSubmodule B K).mapQ (blockDiagonalLieSubmodule B K)
    (linearAdjoint (B.leviEmbedding K m)) (fun _ h =>
      linearAdjoint_preserves_blockDiagonalLie B K m h)

@[simp]
theorem relativeParabolicAdjoint_mk (m : B.Levi K) (A : Matrix (Fin n) (Fin n) K) :
    relativeParabolicAdjoint B K m (Submodule.Quotient.mk A) =
      Submodule.Quotient.mk (linearAdjoint (B.leviEmbedding K m) A) := rfl

/-- The ordinary determinant `det_K(1 - Ad(m)⁻¹; 𝔤(K)/𝔪(K))`. -/
noncomputable def relativeParabolicDiscriminant (m : B.Levi K) : K :=
  LinearMap.det (LinearMap.id - relativeParabolicAdjoint B K m⁻¹)

section Twisted

variable {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E]

/-- The entrywise action of the field automorphism on the quotient, linear over `F`. -/
def relativeParabolicSigma (σ : E ≃ₐ[F] E) : Module.End F (RelativeParabolicLieQuotient B E) :=
  ((blockDiagonalLieSubmodule B E).restrictScalars F).liftQ
    (((blockDiagonalLieSubmodule B E).mkQ.restrictScalars F).comp σ.toLinearMap.mapMatrix)
    (fun A hA => by
      change (Submodule.Quotient.mk (σ.toLinearMap.mapMatrix A) :
        RelativeParabolicLieQuotient B E) = 0
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      rw [mem_blockDiagonalLieSubmodule]
      intro i j hij
      change σ (A i j) = 0
      rw [(mem_blockDiagonalLieSubmodule B E A).mp hA i j hij, map_zero])

@[simp]
theorem relativeParabolicSigma_mk (σ : E ≃ₐ[F] E) (A : Matrix (Fin n) (Fin n) E) :
    relativeParabolicSigma B σ (Submodule.Quotient.mk A) =
      Submodule.Quotient.mk (A.map σ) := rfl

@[simp]
theorem relativeParabolicLieCoordinates_sigma_apply (σ : E ≃ₐ[F] E)
    (x : RelativeParabolicLieQuotient B E) (p : OffBlockPosition B) :
    relativeParabolicLieCoordinates B E (relativeParabolicSigma B σ x) p =
      σ (relativeParabolicLieCoordinates B E x p) := by
  refine Submodule.Quotient.induction_on (blockDiagonalLieSubmodule B E) x ?_
  intro A
  rw [relativeParabolicSigma_mk, relativeParabolicLieCoordinates_mk,
    relativeParabolicLieCoordinates_mk]
  rfl

/-- The quotient over a finite extension is finite-dimensional also over the base field. -/
theorem finiteDimensional_relativeParabolicLieQuotient [FiniteDimensional F E] :
    FiniteDimensional F (RelativeParabolicLieQuotient B E) :=
  FiniteDimensional.trans F E (RelativeParabolicLieQuotient B E)

@[simp]
theorem relativeParabolicSigma_one :
    relativeParabolicSigma B (1 : E ≃ₐ[F] E) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  refine Submodule.Quotient.induction_on (blockDiagonalLieSubmodule B E) x ?_
  intro A
  rw [relativeParabolicSigma_mk]
  rfl

/-- The twisted determinant `det_F(σ - Ad(m)⁻¹; 𝔤(E)/𝔪(E))`. -/
noncomputable def twistedRelativeParabolicDiscriminant [FiniteDimensional F E]
    (σ : E ≃ₐ[F] E) (m : B.Levi E) : F :=
  LinearMap.det (relativeParabolicSigma B σ - (relativeParabolicAdjoint B E m⁻¹).restrictScalars F)

end Twisted

/-- The ordinary factor is the twisted factor at `E = F`, `σ = 1`. -/
@[simp]
theorem twistedRelativeParabolicDiscriminant_one (m : B.Levi K) :
    twistedRelativeParabolicDiscriminant B (1 : K ≃ₐ[K] K) m =
      relativeParabolicDiscriminant B K m := by
  rw [twistedRelativeParabolicDiscriminant, relativeParabolicSigma_one]
  rfl

end Langlands.BaseChange
