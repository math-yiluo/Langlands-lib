import Langlands.Representation.Unitary.CentralCharacterStatement
import Langlands.Representation.Smooth.Schur.Proof

/-!
# Unitary central characters of unitarizable representations

The actual Schur character is unitary because its scalar action preserves a
positive definite Hermitian form.
-/

namespace Langlands

universe uG uV

/-- Irreducibility, admissibility and an invariant positive form supply an
actual smooth unitary character of the full center. -/
theorem unitarizableCentralCharacter :
    UnitarizableCentralCharacterStatement.{uG, uV} := by
  classical
  intro G _ _ _ V _ _ ρ ha hi hu
  let := hi
  let : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨b⟩ := hu
  obtain ⟨χ, ⟨hlc, hact⟩, _⟩ := admissibleSchur_centralCharacter ρ ha hi
  have hnorm (z : Subgroup.center G) : ‖(χ z : ℂ)‖ = 1 := by
    let : InnerProductSpace.Core ℂ V := b.toInnerProductCore
    let : Inner ℂ V := ⟨b.inner⟩
    have hb : b.inner v v ≠ 0 := fun h => hv (b.definite v h)
    have hinvariant := b.invariant (z : G) v v
    rw [hact] at hinvariant
    change inner ℂ ((χ z : ℂ) • v) ((χ z : ℂ) • v) = inner ℂ v v at hinvariant
    rw [InnerProductSpace.Core.inner_smul_left,
      InnerProductSpace.Core.inner_smul_right] at hinvariant
    have hproduct : starRingEnd ℂ (χ z : ℂ) * (χ z : ℂ) = 1 := by
      apply mul_right_cancel₀ hb
      simpa only [mul_assoc, one_mul] using hinvariant
    have h := congrArg norm hproduct
    change ‖star (χ z : ℂ) * (χ z : ℂ)‖ = ‖(1 : ℂ)‖ at h
    simp only [norm_mul, norm_star, norm_one] at h
    nlinarith [norm_nonneg (χ z : ℂ)]
  exact ⟨{
    character := χ
    isOpen_ker := hlc.isOpen_fiber 1
    norm_eq_one := hnorm
    acts := hact }⟩

end Langlands
