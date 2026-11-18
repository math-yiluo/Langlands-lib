import Langlands.GroupScheme.MatrixRepresentation.AffineCoefficientAlgebra
import Langlands.GroupScheme.Torus.RingRepresentationWeightsBaseChange
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Universal coefficients after a field extension -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation.AffineCoefficientBaseChange

open AffineCoefficients AffineCoefficientAlgebra

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]
  (ρ : MatrixRepresentation G n)

/-- Extending a coordinate endomorphism entrywise. -/
def extensionHom :
    Module.End k (n → k) →ₐ[k] Module.End K (n → K) :=
  (AlgHom.restrictScalars k
    (Matrix.toLinAlgEquiv' : Matrix n n K ≃ₐ[K] Module.End K (n → K)).toAlgHom).comp
    (((Algebra.ofId k K).mapMatrix).comp LinearMap.toMatrixAlgEquiv'.toAlgHom)

@[simp]
theorem extensionHom_mulVecLin (M : Matrix n n k) :
    extensionHom (K := K) (n := n) M.mulVecLin =
      (M.map (algebraMap k K)).mulVecLin := by
  change Matrix.toLin' ((LinearMap.toMatrix' (Matrix.toLin' M)).map (algebraMap k K)) = _
  rw [LinearMap.toMatrix'_toLin']
  rfl

/-- The affine test carrying the old universal point over the new field. -/
def universalTestMap :
    (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj
        ((algSpec (CommRingCat.of K)).obj
          (op (CommAlgCat.of K (K ⊗[k] CharacterUnits.Coord G)))) ⟶
      (algSpec (CommRingCat.of k)).obj (op (CharacterUnits.Coord G)) :=
  Over.homMk
    (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : CharacterUnits.Coord G →ₐ[k]
        K ⊗[k] CharacterUnits.Coord G).toRingHom)) (by
    change Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : CharacterUnits.Coord G →ₐ[k]
          K ⊗[k] CharacterUnits.Coord G).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (CharacterUnits.Coord G))) =
      Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[k] CharacterUnits.Coord G))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k K))
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro c
    exact (Algebra.TensorProduct.includeRight : CharacterUnits.Coord G →ₐ[k]
      K ⊗[k] CharacterUnits.Coord G).commutes c)

/-- The old universal point lifted to the scalar-extended group. -/
def universalTestPoint :
    ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G).affinePoints
        (CommAlgCat.of K (K ⊗[k] CharacterUnits.Coord G)) :=
  (baseChangePointsEquiv (Spec.map (CommRingCat.ofHom (algebraMap k K))) G _).symm
    (universalTestMap (K := K) (G := G) ≫ CharacterUnits.universalPoint G)

/-- The matrix on this lifted point is the old universal matrix with extended entries. -/
theorem affineMatrix_universalTestPoint :
    ((ρ.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).affineMatrix
      (CommAlgCat.of K (K ⊗[k] CharacterUnits.Coord G))
      (universalTestPoint (K := K) (G := G)) :
        Matrix n n (K ⊗[k] CharacterUnits.Coord G)) =
      ρ.universalCharacterMatrix.map
        (Algebra.TensorProduct.includeRight : CharacterUnits.Coord G →ₐ[k]
          K ⊗[k] CharacterUnits.Coord G) := by
  exact congrArg Units.val
    (affineMatrix_baseChange_map ρ (CommRingCat.ofHom (algebraMap k K))
      (CharacterUnits.Coord G)
      (CommAlgCat.of K (K ⊗[k] CharacterUnits.Coord G))
      (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : CharacterUnits.Coord G →ₐ[k]
          K ⊗[k] CharacterUnits.Coord G).toRingHom)
      (universalTestMap (K := K) (G := G)) rfl
      (universalTestPoint (K := K) (G := G))
      (CharacterUnits.universalPoint G) (MulEquiv.apply_symm_apply _ _))

/-- A linear coefficient functional extended to the tensor product. -/
def extendedFunctional (ℓ : CharacterUnits.Coord G →ₗ[k] k) :
    (K ⊗[k] CharacterUnits.Coord G) →ₗ[K] K :=
  (TensorProduct.AlgebraTensorModule.rid k K K).toLinearMap.comp (ℓ.baseChange K)

@[simp]
theorem extendedFunctional_includeRight (ℓ : CharacterUnits.Coord G →ₗ[k] k)
    (a : CharacterUnits.Coord G) :
    extendedFunctional (K := K) ℓ
      (Algebra.TensorProduct.includeRight a) = algebraMap k K (ℓ a) := by
  simp [extendedFunctional, Algebra.TensorProduct.includeRight_apply,
    Algebra.smul_def]

/-- Every extended old coefficient preserves an actual stable subspace after base change. -/
theorem coefficient_preserves {W : Submodule K (n → K)}
    (hW : (ρ.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).IsStableSubspace W)
    (ℓ : CharacterUnits.Coord G →ₗ[k] k) (v : n → K) (hv : v ∈ W) :
    (coefficientMap ρ ℓ).map (algebraMap k K) *ᵥ v ∈ W := by
  have h := hW (CommAlgCat.of K (K ⊗[k] CharacterUnits.Coord G))
    (universalTestPoint (K := K) (G := G)) v hv (extendedFunctional (K := K) ℓ)
  rw [affineMatrix_universalTestPoint] at h
  convert h using 1
  funext i
  have hs (a : K ⊗[k] CharacterUnits.Coord G) (c : K) :
      extendedFunctional (K := K) ℓ (a * algebraMap K _ c) =
        extendedFunctional (K := K) ℓ a * c := by
    rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, coefficientMap,
    map_sum, hs, extendedFunctional_includeRight]
  rfl

/-- Actual stable subspaces after extension are preserved by the old operator algebra. -/
theorem operator_preserves {W : Submodule K (n → K)}
    (hW : (ρ.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).IsStableSubspace W)
    {f : Module.End k (n → k)} (hf : f ∈ operatorAlgebra ρ) :
    ∀ v ∈ W, extensionHom (K := K) f v ∈ W := by
  have hle : operatorAlgebra ρ ≤
      ((preservingAlgebra W).restrictScalars k).comap (extensionHom (K := K)) := by
    rw [operatorAlgebra, Algebra.adjoin_le_iff]
    rintro _ ⟨ℓ, rfl⟩
    change ∀ v ∈ W, extensionHom (K := K) (coefficientMap ρ ℓ).mulVecLin v ∈ W
    rw [extensionHom_mulVecLin]
    intro v hv
    exact coefficient_preserves ρ hW ℓ v hv
  exact hle hf

end Langlands.GroupScheme.MatrixRepresentation.AffineCoefficientBaseChange
