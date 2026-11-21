import Langlands.GroupScheme.Quaternionic.SkewHermitianComponentSignedDiscriminant
import Langlands.GroupScheme.Rational.NumberFieldRankThreeGramPureNorm
import Langlands.GroupScheme.Rational.NumberFieldSkewHermitianComponentPlanes
import Langlands.LinearAlgebra.NumberFieldRankSixHyperbolicity

/-! # The hyperbolic symmetric component of a locally isotropic rank-three skew form -/

noncomputable section

universe u

open Matrix
open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic

open KneserThree QuadField Langlands.CentralSimple Langlands.SymmetricBilinear

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2300000

/-- A locally nonsingularly isotropic rank-three skew Gram matrix has quaternion
  coordinates for which the symmetric component over the quadratic field is hyperbolic. -/
def NumberFieldRankThreeSkewComponentStatement : Prop :=
  ∀ (F D : Type u) [Field F] [NumberField F] [DivisionRing D] [Algebra F D]
    [FiniteDimensional F D] [Algebra.IsCentral F D] (σ : FirstKindInvolution F D)
    (hdim : Module.finrank F D = 4) (hsym : Module.finrank F σ.symmetricSubspace = 3),
    let τ := σ.quaternionConjugation hdim hsym
    ∀ (H : Matrix (Fin 3) (Fin 3) D) (hH : τ.IsAntihermitian H),
    IsUnit H → τ.IsLocallyNonsingularIsotropic H →
    ∃ (Q : QuatData F D) (hbar : ∀ z, τ z = Q.bar z),
      reducedNorm F D F (1 ⊗ₜ[F] Q.x) = reducedNorm F (Matrix (Fin 3) (Fin 3) D) F (1 ⊗ₜ[F] H) ∧
      let E := field Q.c
      let V := Fin 3 → D
      letI : Module E V := Module.compHom V Q.ι.toRingHom
      (threeHyperbolicPlanes E).Equivalent (Q.symmetricComponent (AntihermitianForm.ofMatrix hH) hbar).toQuadraticMap

/-- The pure norm representative selects a quadratic field with signed determinant
  negative a square. The local isotropic planes then force three hyperbolic planes. -/
theorem numberFieldRankThreeSkewComponent : NumberFieldRankThreeSkewComponentStatement.{u} := by
  intro F D _ _ _ _ _ _ σ hdim hsym τ H hH hu hl
  obtain ⟨a, ha, ha0, hNa⟩ := FirstKindInvolution.numberFieldRankThreeGramPureNorm F D σ hdim hsym H hH hu hl
  have haτ : τ a = -a := by
    obtain ⟨b, rfl⟩ := τ.mem_alternatingSubspace.mp ha
    rw [FirstKindInvolution.map_sub, FirstKindInvolution.apply_apply, neg_sub]
  obtain ⟨Q, hQa, hbar⟩ := Quaternion.exists_quatData_of_pure σ hdim hsym two_ne_zero ha0 haτ
  have hN : reducedNorm F D F (1 ⊗ₜ[F] Q.x) = reducedNorm F (Matrix (Fin 3) (Fin 3) D) F (1 ⊗ₜ[F] H) := by
    rw [hQa]
    exact hNa
  refine ⟨Q, hbar, hN, ?_⟩
  let E := field Q.c
  let V := Fin 3 → D
  let : NumberField E := NumberField.of_module_finite F E
  let : Module E V := Module.compHom V Q.ι.toRingHom
  let B := AntihermitianForm.ofMatrix hH
  let C := Q.symmetricComponent B hbar
  have hC : C.IsSymm := ⟨fun x y => Q.symmetricComponent_swap B hbar y x⟩
  have hnd : C.Nondegenerate := Q.symmetricComponent_nondegenerate B hbar
    (AntihermitianForm.ofMatrix_separatingLeft hH hu)
  obtain ⟨c, s, _, hd⟩ := Q.exists_component_basis_det_eq_neg_sq τ hbar
    (σ.quaternionConjugation_norm hdim hsym) hH hu hN
  let p : Fin 2 × Fin 3 ≃ Fin 6 := (Fintype.equivFin _).trans (finCongr (by simp))
  let b := c.reindex p
  have hb : (LinearMap.BilinForm.toMatrix b C).det = -(s ^ 2) := by
    rw [det_reindex_basis c p]
    exact hd
  exact numberField_rankSix_hyperbolic C b hC hnd s hb (Q.symmetricComponent_local_isotropic_pair τ hbar hH hu hl)

end Langlands.GroupScheme.Quaternionic
