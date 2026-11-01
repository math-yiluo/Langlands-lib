import Langlands.AlgebraicGeometry.Modules.CoherentEulerPolynomial
import Langlands.AlgebraicGeometry.Modules.AffinePushforwardEulerCharacteristicProof
import Langlands.AlgebraicGeometry.Picard.LineBundleProjectionFormulaProof
import Langlands.AlgebraicGeometry.Picard.ClosedImmersionPullbackAmpleProof
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Actual coherent Euler polynomials under affine pushforward -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

open Langlands.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- The actual projection isomorphism for a coefficient sheaf and every line-bundle power. -/
def coherentTwistPushforwardIso (j : Y ⟶ X) (M : Y.Modules)
    (L : Picard.LineBundle X) (n : ℕ) :
    tensorObj ((Scheme.Modules.pushforward j).obj M) (tensorPow L.obj n) ≅
      (Scheme.Modules.pushforward j).obj
        (tensorObj M (tensorPow ((Picard.LineBundle.pullback j).obj L).obj n)) := by
  let Ln : Picard.LineBundle X :=
    ⟨tensorPow L.obj n, Picard.tensorPow_isLocallyFreeRankOne X L n⟩
  exact tensorComm ((Scheme.Modules.pushforward j).obj M) Ln.obj ≪≫
    Picard.lineBundleProjectionIso j Ln M ≪≫
      (Scheme.Modules.pushforward j).mapIso
        (tensorComm ((Scheme.Modules.pullback j).obj Ln.obj) M ≪≫
          (tensorFunctor Y).mapIso
            ((Iso.refl M).prod (Picard.actualPullbackTensorPowIso j L.obj n)))

namespace HasFiniteAffineSections

/-- Finite morphisms preserve finite generation of sections on affine opens. -/
lemma pushforward {M : Y.Modules} (hM : HasFiniteAffineSections M)
    (j : Y ⟶ X) [IsFinite j] :
    HasFiniteAffineSections ((Scheme.Modules.pushforward j).obj M) := by
  intro U
  let : Algebra Γ(X, U.1) Γ(Y, j ⁻¹ᵁ U.1) := (j.app U.1).hom.toAlgebra
  let : Module Γ(X, U.1) Γ(M, j ⁻¹ᵁ U.1) :=
    Module.compHom _ (j.app U.1).hom
  have : Module.Finite Γ(X, U.1) Γ(Y, j ⁻¹ᵁ U.1) := j.finite_app U.1 U.2
  have : Module.Finite Γ(Y, j ⁻¹ᵁ U.1) Γ(M, j ⁻¹ᵁ U.1) :=
    hM ⟨j ⁻¹ᵁ U.1, U.2.preimage j⟩
  let : IsScalarTower Γ(X, U.1) Γ(Y, j ⁻¹ᵁ U.1) Γ(M, j ⁻¹ᵁ U.1) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact Module.Finite.trans Γ(Y, j ⁻¹ᵁ U.1) Γ(M, j ⁻¹ᵁ U.1)

end HasFiniteAffineSections

namespace DerivedSections

variable {K : Type u} [Field K]
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]

/-- Actual twisted Euler sequences agree under affine pushforward whenever both
coefficient sheaves have finite affine sections and both structure maps are proper. -/
theorem coherentEulerSequence_pushforward (j : Y ⟶ X) [IsAffineHom j]
    [IsProper (j ≫ f)] (M : Y.Modules) [M.IsQuasicoherent]
    (hM : HasFiniteAffineSections M)
    (hP : HasFiniteAffineSections ((Scheme.Modules.pushforward j).obj M))
    (L : Picard.LineBundle X) :
    letI := QuasicoherentLocal.isQuasicoherent_pushforward j M
    coherentEulerSequence f ((Scheme.Modules.pushforward j).obj M) hP L =
      coherentEulerSequence (j ≫ f) M hM ((Picard.LineBundle.pullback j).obj L) := by
  have := QuasicoherentLocal.isQuasicoherent_pushforward j M
  ext n
  have hLn := Picard.tensorPow_isLocallyFreeRankOne X L n
  have hLnY := Picard.tensorPow_isLocallyFreeRankOne Y
    ((Picard.LineBundle.pullback j).obj L) n
  have := QuasicoherentLocal.isQuasicoherent_tensor_lineBundle
    ((Scheme.Modules.pushforward j).obj M) _ hLn
  have := QuasicoherentLocal.isQuasicoherent_tensor_lineBundle M _ hLnY
  let A := tensorObj M (tensorPow ((Picard.LineBundle.pullback j).obj L).obj n)
  let B := tensorObj ((Scheme.Modules.pushforward j).obj M) (tensorPow L.obj n)
  have hA := hasFiniteCohomology_of_coherent (j ≫ f) A (hM.tensor_lineBundle hLnY)
  have hB := hasFiniteCohomology_of_coherent f B (hP.tensor_lineBundle hLn)
  have C := affinePushforwardEulerCharacteristic K Y X j inferInstance f A inferInstance
  have hPA := C.1.mp hA
  have hE := eulerCharacteristic_eq_of_iso f hB hPA
    (coherentTwistPushforwardIso j M L n)
  change (eulerCharacteristic f B hB : ℚ) = (eulerCharacteristic (j ≫ f) A hA : ℚ)
  exact congrArg (Int.cast : ℤ → ℚ) (hE.trans (C.2 hA hPA).symm)

/-- At every common truncation, affine pushforward preserves the actual coherent
Euler polynomial; no support-dimension bound is needed. -/
theorem coherentEulerPolynomial_pushforward (j : Y ⟶ X) [IsAffineHom j]
    [IsProper (j ≫ f)] (M : Y.Modules) [M.IsQuasicoherent]
    (hM : HasFiniteAffineSections M)
    (hP : HasFiniteAffineSections ((Scheme.Modules.pushforward j).obj M))
    (L : Picard.LineBundle X) (d : ℕ) :
    letI := QuasicoherentLocal.isQuasicoherent_pushforward j M
    coherentEulerPolynomial f ((Scheme.Modules.pushforward j).obj M) hP L d =
      coherentEulerPolynomial (j ≫ f) M hM ((Picard.LineBundle.pullback j).obj L) d := by
  have := QuasicoherentLocal.isQuasicoherent_pushforward j M
  unfold coherentEulerPolynomial
  rw [coherentEulerSequence_pushforward f j M hM hP L]

/-- Finite pushforward preserves actual twisted coherent Euler sequences. -/
theorem coherentEulerSequence_finite_pushforward (j : Y ⟶ X) [IsFinite j]
    (M : Y.Modules) [M.IsQuasicoherent] (hM : HasFiniteAffineSections M)
    (L : Picard.LineBundle X) :
    letI := QuasicoherentLocal.isQuasicoherent_pushforward j M
    coherentEulerSequence f ((Scheme.Modules.pushforward j).obj M) (hM.pushforward j) L =
      coherentEulerSequence (j ≫ f) M hM ((Picard.LineBundle.pullback j).obj L) :=
  coherentEulerSequence_pushforward f j M hM (hM.pushforward j) L

/-- Finite, in particular closed-immersion, pushforward preserves every common
coherent Euler polynomial truncation. -/
theorem coherentEulerPolynomial_finite_pushforward (j : Y ⟶ X) [IsFinite j]
    (M : Y.Modules) [M.IsQuasicoherent] (hM : HasFiniteAffineSections M)
    (L : Picard.LineBundle X) (d : ℕ) :
    letI := QuasicoherentLocal.isQuasicoherent_pushforward j M
    coherentEulerPolynomial f ((Scheme.Modules.pushforward j).obj M)
        (hM.pushforward j) L d =
      coherentEulerPolynomial (j ≫ f) M hM ((Picard.LineBundle.pullback j).obj L) d :=
  coherentEulerPolynomial_pushforward f j M hM (hM.pushforward j) L d

end DerivedSections

end Langlands.AlgebraicGeometry.Modules
