import Langlands.BaseChange.SigmaLiftCharacterIdentity.Parameters
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Topology.Instances.Matrix

/-! # Openness of the σ-regular locus from norm existence -/

noncomputable section

namespace Langlands.BaseChange.SigmaLiftCharacterIdentity

open Langlands.JacquetLanglands _root_.Polynomial

variable {R : Type*} [CommRing R] {n : ℕ}

/-- A resultant with fixed degree bounds for the characteristic polynomial and its derivative. -/
private def regularityResultant (g : GeneralLinear n R) : R :=
  let p := (g : Matrix (Fin n) (Fin n) R).charpoly
  p.resultant p.derivative n (n - 1)

private lemma continuous_regularityResultant [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (regularityResultant (R := R) (n := n)) := by
  unfold regularityResultant resultant
  apply Continuous.matrix_det
  refine continuous_pi fun i => continuous_pi fun j => ?_
  induction j using Fin.addCases with
  | left j =>
    simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
    split
    · simp only [coeff_derivative]
      exact (continuous_charpoly_coefficient (R := R) (n := n) (↑i - ↑j + 1)).mul_const _
    · exact continuous_const
  | right j =>
    simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
    split
    · exact continuous_charpoly_coefficient (R := R) (n := n) (↑i - ↑j)
    · exact continuous_const

variable {F : Type*} [Field F] {E : Type*} [CommRing E] [Algebra F E]
variable {σ : E ≃ₐ[F] E} {l : ℕ}

private lemma regularityResultant_ne_zero_iff (g : GeneralLinear n F) :
    regularityResultant g ≠ 0 ↔ IsRegularSemisimple g := by
  let p := (g : Matrix (Fin n) (Fin n) F).charpoly
  have hmonic : p.Monic := Matrix.charpoly_monic _
  have hdeg : p.natDegree = n := by simp [p, Matrix.charpoly_natDegree_eq_dim]
  change p.resultant p.derivative n (n - 1) ≠ 0 ↔ p.Separable
  have hder : p.derivative.natDegree ≤ n - 1 :=
    hdeg ▸ natDegree_derivative_le p
  have hresult : p.resultant p.derivative n (n - 1) = p.resultant p.derivative := calc
    _ = p.resultant p.derivative n (p.derivative.natDegree +
        (n - 1 - p.derivative.natDegree)) := by rw [Nat.add_sub_of_le hder]
    _ = _ := by
      rw [resultant_add_right_deg _ _ _ _ _ le_rfl, ← hdeg, coeff_natDegree,
        hmonic.leadingCoeff, one_pow, one_mul]
  rw [hresult, ← isUnit_iff_ne_zero, isUnit_resultant_iff_isCoprime hmonic, separable_def]

private lemma regularityResultant_associated {δ : GeneralLinear n E} {γ : GeneralLinear n F}
    (h : IsNormAssociated σ l δ γ) :
    regularityResultant (cyclicNorm σ l δ) = algebraMap F E (regularityResultant γ) := by
  obtain ⟨x, hx⟩ := h
  have hmap : ((baseChange F E n γ : GeneralLinear n E) : Matrix (Fin n) (Fin n) E).charpoly =
      ((γ : Matrix (Fin n) (Fin n) F).charpoly).map (algebraMap F E) :=
    Matrix.charpoly_map _ _
  have hp : (cyclicNorm σ l δ : Matrix (Fin n) (Fin n) E).charpoly =
      ((γ : Matrix (Fin n) (Fin n) F).charpoly).map (algebraMap F E) := by
    have hconj := congrArg (fun g : GeneralLinear n E =>
      (g : Matrix (Fin n) (Fin n) E).charpoly) hx
    simpa only [Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj'] using
      hconj.trans hmap
  unfold regularityResultant
  dsimp only
  rw [hp, derivative_map, resultant_map_map]

/-- The σ-regular locus is open when each twisted element has an associated ordinary
element. The proof uses only the existence clause of the cyclic norm lemma. -/
theorem isOpen_sigmaRegular_of_norm_exists [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [TopologicalSpace E] [IsTopologicalRing E]
    [IsModuleTopology F E] (hE : IsCyclicAlgebra σ l)
    (hnorm : ∀ δ : GeneralLinear n E, ∃ γ : GeneralLinear n F, IsNormAssociated σ l δ γ) :
    IsOpen {δ : GeneralLinear n E | IsSigmaRegular σ l δ} := by
  have : Module.Finite F E := hE.1
  have : Nontrivial E := Module.finrank_pos_iff.mp (hE.2.1.symm ▸ hE.pos)
  have := finiteAlgebra_t2Space F E
  let r (δ : GeneralLinear n E) := regularityResultant (cyclicNorm σ l δ)
  have hset : {δ : GeneralLinear n E | IsSigmaRegular σ l δ} = r ⁻¹' ({0} : Set E)ᶜ := by
    ext δ
    change IsSigmaRegular σ l δ ↔ r δ ≠ 0
    constructor
    · rintro ⟨γ, hassoc, hreg⟩
      change regularityResultant (cyclicNorm σ l δ) ≠ 0
      rw [regularityResultant_associated hassoc]
      intro hz
      exact (regularityResultant_ne_zero_iff γ).2 hreg
        ((algebraMap F E).injective (hz.trans (map_zero _).symm))
    · intro hr
      obtain ⟨γ, hassoc⟩ := hnorm δ
      refine ⟨γ, hassoc, (regularityResultant_ne_zero_iff γ).1 ?_⟩
      change regularityResultant (cyclicNorm σ l δ) ≠ 0 at hr
      rw [regularityResultant_associated hassoc] at hr
      exact fun hg => hr (hg ▸ map_zero _)
  rw [hset]
  exact isClosed_singleton.isOpen_compl.preimage
    (continuous_regularityResultant.comp (continuous_cyclicNorm σ l))

/-- Openness of the σ-regular set, the part of regular openness and conullity used
in the forward implication. -/
def SigmaRegularOpenStatement.{u, v} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (E : Type v) [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
    [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ), IsCyclicAlgebra σ l →
    IsOpen {δ : GeneralLinear n E | IsSigmaRegular σ l δ}

theorem sigmaRegularOpen_of_cyclicNormLemma.{u, v} (hnorm : CyclicNormLemmaStatement.{u, v}) :
    SigmaRegularOpenStatement.{u, v} := by
  intro F _ _ _ _ E _ _ _ _ _ σ l n hE
  exact isOpen_sigmaRegular_of_norm_exists hE (hnorm F E σ l n hE).1

end Langlands.BaseChange.SigmaLiftCharacterIdentity
