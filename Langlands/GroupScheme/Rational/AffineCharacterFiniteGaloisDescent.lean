import Langlands.GroupScheme.Rational.AffineCharacterFiniteGaloisReconstruction
import Langlands.GroupScheme.Rational.AffineCharacterFiniteGaloisDescentStatement

/-! # Finite-Galois descent of affine character evaluations -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.AffineCharacterFiniteGalois

open Langlands.Plancherel.TorusNormKernel

set_option backward.isDefEq.respectTransparency false

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]
variable (L : FiniteGaloisIntermediateField k K)
variable (v : (L ⊗[k] Coord G)ˣ)
variable (ψ : rationalCharacters (GaloisPointComparison.baseChanged k K G))
variable (hv : Units.map (tensorEmbed (Coord G) L).toMonoidHom v = tensorValue G K ψ)

/-- Direct evaluation commutes with increasing the finite coefficient field. -/
theorem tensorEval_field_compare (y : G.affinePoints (CommAlgCat.of k L)) :
    ((tensorEval G K K (Lie.affineMap G L.toIntermediateField.val y)).restrictScalars k).comp
        (tensorEmbed (Coord G) L) =
      L.toIntermediateField.val.comp ((tensorEval G L L y).restrictScalars k) := by
  apply Algebra.TensorProduct.ext'
  intro c a
  simp only [tensorEval, tensorEmbed, AlgHom.comp_apply,
    Algebra.TensorProduct.lift_tmul, AlgHom.restrictScalars_apply,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.ofId_apply,
    map_mul]
  exact congrArg (fun z : K => (c : K) * z)
    (DFunLike.congr_fun (Lie.pointCoordinates_naturality G L.toIntermediateField.val y) a)

include hv in
/-- The finite tensor model has the original character values in the ambient field. -/
theorem modelValue_field_compare (y : G.affinePoints (CommAlgCat.of k L)) :
    Units.map L.toIntermediateField.val.toMonoidHom (modelValue G L v L y) =
      valueE ψ K (Lie.affineMap G L.toIntermediateField.val y) := by
  calc
    _ = Units.map (tensorEval G K K (Lie.affineMap G L.toIntermediateField.val y)
        ).toMonoidHom (Units.map (tensorEmbed (Coord G) L).toMonoidHom v) := by
      apply Units.ext
      exact (DFunLike.congr_fun (tensorEval_field_compare G L y) (v : L ⊗[k] Coord G)).symm
    _ = _ := by rw [hv, tensorValue_eval]

/-- The actual reconstructed character agrees on every extended rational point. -/
theorem finiteCharacter_rationalEval (g : rationalPoints G) :
    algebraMap L K
        (rationalCharacterEval (finiteCharacter G L v ψ hv)
          (GaloisPointComparison.rationalExtend k L G g) : L) =
      (rationalCharacterEval ψ (GaloisPointComparison.rationalExtend k K G g) : K) := by
  rw [← valueE_baseChangeCoeffEquiv, ← valueE_baseChangeCoeffEquiv]
  have hm := modelValue_field_compare G L v ψ hv
    (GaloisPointComparison.baseChangeCoeffEquiv k L G
      (GaloisPointComparison.rationalExtend k L G g))
  have hf : valueE (finiteCharacter G L v ψ hv) L
      (GaloisPointComparison.baseChangeCoeffEquiv k L G
        (GaloisPointComparison.rationalExtend k L G g)) =
      modelValue G L v L
        (GaloisPointComparison.baseChangeCoeffEquiv k L G
          (GaloisPointComparison.rationalExtend k L G g)) :=
    finiteCharacter_values G L v ψ hv (CommAlgCat.of L L)
      (GaloisPointComparison.baseChangeCoeffEquiv k L G
        (GaloisPointComparison.rationalExtend k L G g))
  rw [hf]
  apply (congrArg Units.val hm).trans
  congr 2
  rw [GaloisPointComparison.baseChangeCoeffEquiv_rationalExtend,
    GaloisPointComparison.baseChangeCoeffEquiv_rationalExtend]
  have h := DFunLike.congr_fun (G.affinePointMap_comp
    (CommAlgCat.ofHom (Algebra.ofId k L))
    (CommAlgCat.ofHom L.toIntermediateField.val))
    (GaloisPointComparison.rationalCoeffEquiv k G g)
  exact h.symm

/-- Every affine character has a finite Galois model for all base-field evaluations. -/
theorem exists_finiteGalois_character [IsGalois k K]
    (ψ : rationalCharacters (GaloisPointComparison.baseChanged k K G)) :
    ∃ L : FiniteGaloisIntermediateField k K,
      ∃ ψL : rationalCharacters (GaloisPointComparison.baseChanged k L G),
        ∀ g : rationalPoints G,
          algebraMap L K
              (rationalCharacterEval ψL (GaloisPointComparison.rationalExtend k L G g) : L) =
            (rationalCharacterEval ψ (GaloisPointComparison.rationalExtend k K G g) : K) := by
  obtain ⟨L, v, hv⟩ := exists_tensorEmbed_unit (Coord G) (tensorValue G K ψ)
  exact ⟨L, finiteCharacter G L v ψ hv, finiteCharacter_rationalEval G L v ψ hv⟩

end Langlands.GroupScheme.AffineCharacterFiniteGalois

namespace Langlands.GroupScheme

/-- Finite-Galois descent of all base-field rational-point character evaluations. -/
theorem affineCharacterFiniteGaloisDescent :
    AffineCharacterFiniteGaloisDescentStatement.{u} := by
  intro k K _ _ _ _ G _ ψ
  exact AffineCharacterFiniteGalois.exists_finiteGalois_character G ψ

end Langlands.GroupScheme
