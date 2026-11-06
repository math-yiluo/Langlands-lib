import Langlands.Correspondence.AssemblyLSegmentReduction
import Langlands.LocalFactor.WeilDeligneEulerStatement
import Langlands.LocalFactor.WeilDeligneEulerSum
import Langlands.WeilDeligne.TensorDual
import Langlands.Representation.Twist.DualProof
import Langlands.Weil.Local.ParameterOperations

/-! # Local block-pair Euler comparisons for assembly -/

noncomputable section

universe uK uG uV uW uF uP

namespace Langlands.LocalFactor.WeilDeligne

open WeilDeligneRepresentation

variable {K : Type uK} [Field K] {G : Type uG} [Group G] {ν : G →* Kˣ}

private theorem zeroTensorTwist_action (χ : G →* Kˣ)
    (A : FiniteRepresentation.{uK, uG, uV} K G)
    (B : FiniteRepresentation.{uK, uG, uW} K G) (g : G) :
    (tensor (zeroMonodromy ν (FiniteRepresentation.twist χ A))
      (zeroMonodromy ν B)).representation g =
      (χ g : K) • (FiniteRepresentation.tensor A B).representation g := by
  change TensorProduct.map ((χ g : K) • A.representation g) (B.representation g) =
    (χ g : K) • TensorProduct.map (A.representation g) (B.representation g)
  exact TensorProduct.map_smul_left _ _ _

private theorem zeroTensorTwist_monodromy (χ : G →* Kˣ)
    (A : FiniteRepresentation.{uK, uG, uV} K G)
    (B : FiniteRepresentation.{uK, uG, uW} K G) :
    (tensor (zeroMonodromy ν (FiniteRepresentation.twist χ A))
      (zeroMonodromy ν B)).monodromy = 0 := by
  apply TensorProduct.ext'
  intro x y
  change
    (TensorProduct.map (0 : Module.End K A) (1 : Module.End K B)) (x ⊗ₜ[K] y) +
      (TensorProduct.map (1 : Module.End K A) (0 : Module.End K B)) (x ⊗ₜ[K] y) =
      (0 : TensorProduct K A B)
  simp

/-- An inertia-trivial twist of the first zero-monodromy factor scales the
Frobenius operator on the invariants of the full tensor product. -/
theorem rationalLFactor_zeroTensorTwist (χ : G →* Kˣ)
    (I : Subgroup G) [I.Normal] (hχ : ∀ i : I, χ i = 1) (Φ : G)
    (A : FiniteRepresentation.{uK, uG, uV} K G)
    (B : FiniteRepresentation.{uK, uG, uW} K G) :
    rationalLFactor (tensor (zeroMonodromy ν (FiniteRepresentation.twist χ A))
        (zeroMonodromy ν B)) I Φ =
      rationalFactor ((χ Φ : K) •
        (FiniteRepresentation.invariants I (FiniteRepresentation.tensor A B)).representation Φ) := by
  apply rationalLFactor_eq_of_embedding Φ _
    (FiniteRepresentation.invariantSubspace (FiniteRepresentation.tensor A B) I).subtype
    Subtype.val_injective
  · intro w
    constructor
    · rw [zeroTensorTwist_monodromy]
      rfl
    · intro i
      rw [zeroTensorTwist_action]
      change (χ i : K) • (FiniteRepresentation.tensor A B).representation i w.val = w.val
      rw [hχ i, Units.val_one, one_smul]
      exact w.property i
  · intro v _ hv
    refine ⟨⟨v, ?_⟩, rfl⟩
    intro i
    have h := hv i
    rw [zeroTensorTwist_action] at h
    change (χ i : K) • (FiniteRepresentation.tensor A B).representation i v = v at h
    rw [hχ i, Units.val_one, one_smul] at h
    exact h
  · intro w
    rw [zeroTensorTwist_action]
    rfl

private def dualTwistZeroEquiv (χ : G →* Kˣ)
    (A : FiniteRepresentation.{uK, uG, uV} K G) :
    WeilDeligneRepresentation.Equiv (dual (zeroMonodromy ν (FiniteRepresentation.twist χ A)))
      (zeroMonodromy ν (FiniteRepresentation.twist χ⁻¹ (FiniteRepresentation.dual A))) where
  representationEquiv := by
    refine Representation.Equiv.mk (LinearEquiv.refl K (Module.Dual K A)) ?_
    intro g
    change (Langlands.twist χ A.representation).dual g =
      (Langlands.twist χ⁻¹ A.representation.dual) g
    rw [Langlands.dual_twist]
  comm_monodromy := by
    change LinearMap.id ∘ₗ (-(0 : Module.End K A).dualMap) =
      (0 : Module.End K (Module.Dual K A)) ∘ₗ LinearMap.id
    ext ℓ v
    simp

/-- Dualizing the twisted tensor inverts the twisting character and takes
invariants after tensoring the two dual Weil representations. -/
theorem rationalLFactor_dual_zeroTensorTwist (χ : G →* Kˣ)
    (I : Subgroup G) [I.Normal] (hχ : ∀ i : I, χ i = 1) (Φ : G)
    (A : FiniteRepresentation.{uK, uG, uV} K G)
    (B : FiniteRepresentation.{uK, uG, uW} K G) :
    rationalLFactor (dual (tensor
        (zeroMonodromy ν (FiniteRepresentation.twist χ A)) (zeroMonodromy ν B))) I Φ =
      rationalFactor ((χ⁻¹ Φ : K) •
        (FiniteRepresentation.invariants I (FiniteRepresentation.tensor
          (FiniteRepresentation.dual A) (FiniteRepresentation.dual B))).representation Φ) := by
  rw [rationalLFactor_eq_of_equiv I (tensorDualEquiv _ _).symm Φ,
    rationalLFactor_eq_of_equiv I
      (tensorEquiv (dualTwistZeroEquiv χ A) (dualZeroMonodromyEquiv B)) Φ]
  exact rationalLFactor_zeroTensorTwist χ⁻¹ I (by intro i; simp [hχ i]) Φ _ _

end Langlands.LocalFactor.WeilDeligne

namespace Langlands.Correspondence

open scoped BigOperators
open Weil.Local WeilDeligneRepresentation LocalFactor LocalFactor.WeilDeligne

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The algebraic pair-block Euler formula implies the local arithmetic
block-pair L-factor product used in segment inheritance. -/
theorem arithmeticBlockPairLFactor_of_wdEulerPairBlock
    (hE : WDEulerPairBlockStatement.{0, uF, uP, uP}) :
    ArithmeticBlockPairLFactor.{uF, uP} F := by
  intro B B' a b
  change rationalLFactor
      (tensor (block (localNormCharacter F).toMonoidHom B (a + 1))
        (block (localNormCharacter F).toMonoidHom B' (b + 1)))
      (localInertia F) (localGeometricFrobenius F) =
    ∏ j : Fin (min (a + 1) (b + 1)),
      rationalLFactor (tensor
        (zeroMonodromy (localNormCharacter F).toMonoidHom
          (FiniteRepresentation.twist
            ((localNormCharacter F).toMonoidHom ^ (a + b - (j : ℕ))) B))
        (zeroMonodromy (localNormCharacter F).toMonoidHom B'))
        (localInertia F) (localGeometricFrobenius F)
  have h := (hE ℂ (localWeilGroup F) (localNormCharacter F).toMonoidHom
    (localInertia F) (localNormCharacter_on_inertia F)
    (localGeometricFrobenius F) B B' a b).2.1
  change rationalLFactor _ _ _ = _ at h
  rw [h]
  apply Finset.prod_congr rfl
  intro j _
  rw [rationalLFactor_zeroTensorTwist _ _ (by
    intro i
    simp [localNormCharacter_on_inertia F i])]
  simp

/-- The local rational L-factor of the dual of a tensor of uncentered blocks
is a product of dual zero-monodromy pair factors, with positive twist `j`
before taking the dual. -/
def ArithmeticDualBlockPairLFactor : Prop :=
  ∀ (B B' : LocalWeilRepresentation.{uF, uP} F) (a b : ℕ),
    rationalLFactorClass (localInertia F) (localGeometricFrobenius F)
        (dualClass (tensorClass
          (classOf (block (localNormCharacter F).toMonoidHom B (a + 1)))
          (classOf (block (localNormCharacter F).toMonoidHom B' (b + 1))))) =
      ∏ j : Fin (min (a + 1) (b + 1)),
        rationalLFactorClass (localInertia F) (localGeometricFrobenius F)
          (dualClass (tensorClass
            (classOf (zeroMonodromy (localNormCharacter F).toMonoidHom
              (FiniteRepresentation.twist
                ((localNormCharacter F).toMonoidHom ^ (j : ℕ)) B)))
            (classOf (zeroMonodromy (localNormCharacter F).toMonoidHom B'))))

/-- The supplied algebraic dual-pair formula gives the local dual block-pair
product after tensor-duality transport and inversion of the twisting character. -/
theorem arithmeticDualBlockPairLFactor_of_wdEulerDualPairBlock
    (hE : WDEulerDualPairBlockStatement.{0, uF, uP, uP}) :
    ArithmeticDualBlockPairLFactor.{uF, uP} F := by
  intro B B' a b
  change rationalLFactor (dual
      (tensor (block (localNormCharacter F).toMonoidHom B (a + 1))
        (block (localNormCharacter F).toMonoidHom B' (b + 1))))
      (localInertia F) (localGeometricFrobenius F) =
    ∏ j : Fin (min (a + 1) (b + 1)),
      rationalLFactor (dual (tensor
        (zeroMonodromy (localNormCharacter F).toMonoidHom
          (FiniteRepresentation.twist ((localNormCharacter F).toMonoidHom ^ (j : ℕ)) B))
        (zeroMonodromy (localNormCharacter F).toMonoidHom B')))
        (localInertia F) (localGeometricFrobenius F)
  have h := (hE ℂ (localWeilGroup F) (localNormCharacter F).toMonoidHom
    (localInertia F) (localNormCharacter_on_inertia F)
    (localGeometricFrobenius F) B B' a b).2.1
  change rationalLFactor _ _ _ = _ at h
  rw [rationalLFactor_eq_of_equiv (localInertia F) (tensorDualEquiv _ _).symm
    (localGeometricFrobenius F), h]
  apply Finset.prod_congr rfl
  intro j _
  rw [rationalLFactor_dual_zeroTensorTwist _ _ (by
    intro i
    simp [localNormCharacter_on_inertia F i])]
  simp [zpow_neg]

/-- Conditional local Euler comparisons for segment-pair assembly. The two
algebraic pair-block formulas remain explicit premises. -/
def AssemblyBlockPairEulerReductionStatement : Prop :=
  (WDEulerPairBlockStatement.{0, uF, uP, uP} →
    ArithmeticBlockPairLFactor.{uF, uP} F) ∧
  (WDEulerDualPairBlockStatement.{0, uF, uP, uP} →
    ArithmeticDualBlockPairLFactor.{uF, uP} F)

theorem assemblyBlockPairEulerReduction :
    AssemblyBlockPairEulerReductionStatement.{uF, uP} F :=
  ⟨arithmeticBlockPairLFactor_of_wdEulerPairBlock F,
    arithmeticDualBlockPairLFactor_of_wdEulerDualPairBlock F⟩

end Langlands.Correspondence
