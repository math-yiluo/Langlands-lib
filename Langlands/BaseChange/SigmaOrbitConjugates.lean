import Langlands.BaseChange.CuspidalSigmaLift
import Langlands.BaseChange.CyclicAlgebraTopology
import Langlands.Representation.Induction.BinaryProduct
import Langlands.VirtualRepresentation.Supercuspidal.FieldTransport
import Mathlib.Logic.Equiv.Fin.Rotate

/-! # The conjugate factors of a supercuspidal orbit product -/

namespace Langlands.BaseChange

universe u v uW

variable {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E]
  {n : ℕ} {W : Type uW} [AddCommGroup W] [Module ℂ W]

private theorem comp_entrywiseAut_one (P : Representation ℂ (GeneralLinear n E) W) :
    P.comp (entrywiseAut (1 : E ≃ₐ[F] E) n).toMonoidHom = P := by
  apply MonoidHom.ext
  intro g
  change P (entrywiseAut (1 : E ≃ₐ[F] E) n g) = P g
  rw [entrywiseAut_one_apply]

/-- Composition of the actual entrywise pullbacks follows multiplication of automorphisms. -/
theorem comp_entrywiseAut_mul (P : Representation ℂ (GeneralLinear n E) W) (σ τ : E ≃ₐ[F] E) :
    (P.comp (entrywiseAut σ n).toMonoidHom).comp (entrywiseAut τ n).toMonoidHom =
      P.comp (entrywiseAut (σ * τ) n).toMonoidHom := by
  apply MonoidHom.ext
  intro g
  exact congrArg P (entrywiseAut_mul_apply σ τ g).symm

variable (σ : E ≃ₐ[F] E) (P : Representation ℂ (GeneralLinear n E) W)
  {s : ℕ} (hperiod : ∀ i : ℕ,
    Nonempty (P.Equiv (P.comp (entrywiseAut (σ ^ i) n).toMonoidHom)) ↔ s ∣ i)

include hperiod in
/-- A period as in the cuspidal converse is a positive divisor of the cyclic degree. -/
theorem sigmaConjugate_period_pos_dvd {l : ℕ} (hσ : IsCyclicAlgebra σ l) : 0 < s ∧ s ∣ l := by
  have hd : s ∣ l := (hperiod l).mp (by
    rw [hσ.pow_eq_one, comp_entrywiseAut_one]
    exact ⟨Representation.Equiv.refl P⟩)
  exact ⟨Nat.pos_of_dvd_of_pos hd hσ.pos, hd⟩

include hperiod in
/-- Cancelling the smaller pullback identifies equivalence of conjugates with a period test. -/
theorem sigmaConjugates_equiv_iff_dvd_sub {i j : ℕ} (hij : i ≤ j) :
    Nonempty (Representation.Equiv (P.comp (entrywiseAut (σ ^ i) n).toMonoidHom)
      (P.comp (entrywiseAut (σ ^ j) n).toMonoidHom)) ↔ s ∣ j - i := by
  have hpow : σ ^ (j - i) * σ ^ i = σ ^ j := by rw [← pow_add, Nat.sub_add_cancel hij]
  constructor
  · rintro ⟨e⟩
    have he := BinaryTensor.compEquiv e (entrywiseAut (σ ^ i)⁻¹ n).toMonoidHom
    have hq : σ ^ j * (σ ^ i)⁻¹ = σ ^ (j - i) := by rw [← hpow, mul_inv_cancel_right]
    rw [comp_entrywiseAut_mul, comp_entrywiseAut_mul, mul_inv_cancel, hq,
      comp_entrywiseAut_one] at he
    exact (hperiod _).mp ⟨he⟩
  · intro hd
    obtain ⟨e⟩ := (hperiod _).mpr hd
    have he := BinaryTensor.compEquiv e (entrywiseAut (σ ^ i) n).toMonoidHom
    rw [comp_entrywiseAut_mul, hpow] at he
    exact ⟨he⟩

include hperiod in
/-- The first `s` conjugates are pairwise inequivalent, even for nontrivial stabilizer. -/
theorem sigmaConjugates_pairwise_inequivalent :
    Pairwise fun (i j : Fin s) =>
      IsEmpty (Representation.Equiv (P.comp (entrywiseAut (σ ^ (i : ℕ)) n).toMonoidHom)
        (P.comp (entrywiseAut (σ ^ (j : ℕ)) n).toMonoidHom)) := by
  have hlt (i j : Fin s) (hij : i < j) :
      ¬ Nonempty (Representation.Equiv (P.comp (entrywiseAut (σ ^ (i : ℕ)) n).toMonoidHom)
        (P.comp (entrywiseAut (σ ^ (j : ℕ)) n).toMonoidHom)) := by
    intro h
    have h' : (i : ℕ) < (j : ℕ) := hij
    have hd := (sigmaConjugates_equiv_iff_dvd_sub σ P hperiod h'.le).mp h
    have := Nat.le_of_dvd (by omega) hd
    omega
  intro i j hij
  refine ⟨fun e => ?_⟩
  rcases lt_or_gt_of_ne hij with h | h
  · exact hlt i j h ⟨e⟩
  · exact hlt j i h ⟨e.symm⟩

include hperiod in
/-- Pullback by `σ` sends each of the first `s` conjugates to the next one, cyclically. -/
theorem sigmaConjugate_entrywiseAut_equiv_finRotate (i : Fin s) :
    Nonempty (Representation.Equiv ((P.comp (entrywiseAut (σ ^ (i : ℕ)) n).toMonoidHom).comp
      (entrywiseAut σ n).toMonoidHom)
      (P.comp (entrywiseAut (σ ^ (finRotate s i : ℕ)) n).toMonoidHom)) := by
  cases s with
  | zero => exact Fin.elim0 i
  | succ s =>
    rw [comp_entrywiseAut_mul, ← pow_succ]
    by_cases hi : i = Fin.last s
    · subst i
      rw [finRotate_last, Fin.val_zero, pow_zero, comp_entrywiseAut_one, Fin.val_last]
      exact ⟨((hperiod _).mpr (dvd_refl _)).some.symm⟩
    · rw [coe_finRotate_of_ne_last hi]
      exact ⟨Representation.Equiv.refl _⟩

section Topology

variable [TopologicalSpace F] [TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology F E]

/-- Supercuspidality is preserved by the entrywise conjugation in `sigmaOrbitProduct`. -/
theorem isSupercuspidal_comp_entrywiseAut (hP : GeneralLinear.IsSupercuspidal P) :
    GeneralLinear.IsSupercuspidal (P.comp (entrywiseAut σ n).toMonoidHom) := by
  have hσ : Continuous σ := IsModuleTopology.continuous_of_linearMap σ.toLinearEquiv.toLinearMap
  have hσs : Continuous σ.symm :=
    IsModuleTopology.continuous_of_linearMap σ.symm.toLinearEquiv.toLinearMap
  exact GeneralLinear.isSupercuspidal_comp_fieldEquiv n σ.toRingEquiv hσ hσs P hP

end Topology

end Langlands.BaseChange
