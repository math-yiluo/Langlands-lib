import Langlands.Representation.Category.Twist
import Langlands.Representation.Induction.Parabolic
import Langlands.Representation.Induction.CharacterTwistProof
import Langlands.Representation.Induction.Equivalences
import Langlands.Representation.Jacquet.Parabolic
import Langlands.Representation.Jacquet.NormalizedCharacterTwistEquiv

/-!
# Actual normalized parabolic functors under a radical-trivial character twist

Both equivalences use the actual inducing-function and coinvariant carriers.
The parabolic character factors through its Levi because its radical is killed.
-/

noncomputable section

open scoped NNReal

namespace Langlands.GeneralLinear.BlockShape

universe uF uV

variable {F : Type uF} [CommRing F] {n : ℕ} (B : BlockShape n)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- An ambient character trivial on the radical factors through the actual
Levi projection on the parabolic. -/
theorem character_eq_leviProjection (χ : GeneralLinear n F →* ℂˣ)
    (hN : B.unipotentSubgroup F ≤ χ.ker) (q : B.parabolic F) :
    χ q.val = χ (B.leviEmbedding F (B.leviProjection F q)) := by
  have hu : χ (((B.unipotentPart F q).val : B.parabolic F) : GeneralLinear n F) = 1 :=
    hN ⟨(B.unipotentPart F q).val, (B.unipotentPart F q).property, rfl⟩
  have hq : q = (B.unipotentPart F q).val *
      B.leviInParabolic F (B.leviProjection F q) :=
    (B.decomposition F).symm_apply_apply q |>.symm
  have h := congrArg (fun r : B.parabolic F => χ r.val) hq
  simpa only [Subgroup.coe_mul, map_mul, hu, one_mul, leviInParabolic_val] using h

/-- A trivial-radical character commutes with the actual normalized coinvariant
quotient, with its character restricted to the embedded product Levi. -/
def normalizedJacquetOfCharacterTwistEquiv (δ : B.Levi F →* ℝ≥0ˣ)
    (χ : GeneralLinear n F →* ℂˣ) (hN : B.unipotentSubgroup F ≤ χ.ker)
    (ρ : Representation ℂ (GeneralLinear n F) V) :
    (B.normalizedJacquetOf δ (Langlands.twist χ ρ)).Equiv
      (Langlands.twist (χ.comp (B.leviEmbedding F)) (B.normalizedJacquetOf δ ρ)) := by
  have hNP : B.unipotentRadical F ≤ (χ.comp (B.parabolic F).subtype).ker := by
    intro q hq
    exact hN ⟨q, hq, rfl⟩
  let e := Jacquet.normalizedActionOfModulusTwistEquiv
    (ρ.comp (B.parabolic F).subtype) (B.unipotentRadical F) ⊤
    B.top_le_normalizer_unipotentRadical (χ.comp (B.parabolic F).subtype) hNP
    (B.topModulus δ)
  exact Representation.Equiv.mk e.toLinearEquiv (fun m => e.isIntertwining' (B.leviToTop m))

@[simp]
theorem normalizedJacquetOfCharacterTwistEquiv_mk (δ : B.Levi F →* ℝ≥0ˣ)
    (χ : GeneralLinear n F →* ℂˣ) (hN : B.unipotentSubgroup F ≤ χ.ker)
    (ρ : Representation ℂ (GeneralLinear n F) V) (v : V) :
    B.normalizedJacquetOfCharacterTwistEquiv δ χ hN ρ
        (B.jacquetMk (Langlands.twist χ ρ) v) = B.jacquetMk ρ v := rfl

section Topology

variable [TopologicalSpace F] [IsTopologicalRing F]

/-- The ambient smooth character restricted along the actual Levi embedding. -/
def restrictSmoothCharacter (χ : Induction.SmoothCharacter ℂ (GeneralLinear n F)) :
    Induction.SmoothCharacter ℂ (B.Levi F) where
  toMonoidHom := χ.toMonoidHom.comp (B.leviEmbedding F)
  isOpen_ker := χ.isOpen_ker.preimage (B.leviEmbeddingContinuous F).continuous

/-- Scalar character multiplication commutes with the supplied normalization
in the actual parabolic covariance action. -/
theorem inducingRepresentation_characterTwist
    (δ : Induction.SmoothCharacter ℂ (B.Levi F))
    (χ : Induction.SmoothCharacter ℂ (GeneralLinear n F))
    (hN : B.unipotentSubgroup F ≤ χ.toMonoidHom.ker)
    (σ : Representation ℂ (B.Levi F) V) :
    Langlands.twist (χ.toMonoidHom.comp (B.parabolic F).subtype)
        (B.inducingRepresentation δ σ) =
      B.inducingRepresentation δ
        (Langlands.twist (χ.toMonoidHom.comp (B.leviEmbedding F)) σ) := by
  ext q v
  change (χ.toMonoidHom q.val : ℂ) •
      ((δ.toMonoidHom (B.leviProjection F q) : ℂ) • σ (B.leviProjection F q) v) =
    (δ.toMonoidHom (B.leviProjection F q) : ℂ) •
      ((χ.toMonoidHom (B.leviEmbedding F (B.leviProjection F q)) : ℂ) •
        σ (B.leviProjection F q) v)
  rw [B.character_eq_leviProjection χ.toMonoidHom hN q]
  exact smul_comm _ _ _

/-- The actual normalized induced representation commutes with a smooth
ambient twist trivial on the radical. The forward map multiplies the induced
function at x by χ(x). -/
def normalizedInducedOfCharacterTwistEquiv
    (δ : Induction.SmoothCharacter ℂ (B.Levi F))
    (χ : Induction.SmoothCharacter ℂ (GeneralLinear n F))
    (hN : B.unipotentSubgroup F ≤ χ.toMonoidHom.ker)
    (σ : Representation ℂ (B.Levi F) V) :
    (Langlands.twist χ.toMonoidHom (B.normalizedInducedOf δ σ)).Equiv
      (B.normalizedInducedOf δ
        (Langlands.twist (χ.toMonoidHom.comp (B.leviEmbedding F)) σ)) :=
  (Induction.smoothInductionTwistEquiv (B.parabolic F) χ
    (B.inducingRepresentation δ σ)).trans
      (Induction.smoothInducedEquiv (B.parabolic F)
        (Langlands.equivOfRepresentationEq
          (B.inducingRepresentation_characterTwist δ χ hN σ)))

@[simp]
theorem normalizedInducedOfCharacterTwistEquiv_eval
    (δ : Induction.SmoothCharacter ℂ (B.Levi F))
    (χ : Induction.SmoothCharacter ℂ (GeneralLinear n F))
    (hN : B.unipotentSubgroup F ≤ χ.toMonoidHom.ker)
    (σ : Representation ℂ (B.Levi F) V)
    (f : Induction.SmoothFunctions (B.parabolic F) (B.inducingRepresentation δ σ))
    (x : GeneralLinear n F) :
    Induction.eval _ _ (B.normalizedInducedOfCharacterTwistEquiv δ χ hN σ f) x =
      (χ.toMonoidHom x : ℂ) • Induction.eval _ _ f x := rfl

end Topology
end Langlands.GeneralLinear.BlockShape
