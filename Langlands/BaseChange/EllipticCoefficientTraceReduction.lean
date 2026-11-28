import Langlands.BaseChange.CharacterLocalValueConjugation
import Langlands.BaseChange.CoefficientTraceSchur
import Langlands.BaseChange.EllipticCoefficientTraceStatement
import Langlands.BaseChange.SquareIntegrableCoefficientCharacterFormulaStatement
import Langlands.BaseChange.SquareIntegrableCoefficientNonellipticVanishingStatement
import Langlands.Representation.Smooth.FixedVectors.FiniteTypes

/-! # The elliptic part of the trace of a square-integrable coefficient from two analytic
statements -/

noncomputable section

namespace Langlands.BaseChange

open JacquetLanglands MeasureTheory HarishChandraSchwartz

section Conjugation

variable {F : Type*} [Field F] {n : ℕ}

/-- Regular semisimplicity is invariant under conjugation. -/
theorem isRegularSemisimple_inv_mul_mul_iff (a g : GeneralLinear n F) :
    IsRegularSemisimple (a⁻¹ * g * a) ↔ IsRegularSemisimple g := by
  have h : ((a⁻¹ * g * a : GeneralLinear n F) : Matrix (Fin n) (Fin n) F).charpoly =
      (g : Matrix (Fin n) (Fin n) F).charpoly := by
    rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
    exact Matrix.charpoly_units_conj' a g
  simp only [IsRegularSemisimple, h]

end Conjugation

/-- The character formula for conjugate square-integrable coefficients and the vanishing of
the non-elliptic part of a class function times such a coefficient together imply the
elliptic trace identity `EllipticCoefficientTraceStatement`. -/
def EllipticCoefficientTraceReductionStatement.{u, uV} : Prop :=
  SquareIntegrableCoefficientCharacterFormulaStatement.{u, uV} →
    SquareIntegrableCoefficientNonellipticVanishingStatement.{u, uV} →
      EllipticCoefficientTraceStatement.{u, uV}

theorem ellipticCoefficientTraceReduction.{u, uV} :
    EllipticCoefficientTraceReductionStatement.{u, uV} := by
  classical
  intro hA hC F _ _ _ _ _ n hn G Z μ _ V W _ _ _ _ ρ π hρ hπ hirρ hirπ cρ cπ hc d hd
    Θρ hΘρ v ℓ
  have := LocalFieldTopology.generalLinear_nonarchimedean F n
  have := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  have := LocalFieldTopology.generalLinear_t2Space F n
  have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
  -- A compact open subgroup fixing `v`.
  obtain ⟨K, hKc, -, hK⟩ := exists_compactOpen_fixing_finite π hπ.isAdmissible.1
    (fun _ : Unit => v) Set.univ Filter.univ_mem
  let H : CompactOpenSubgroup G := ⟨K, hKc⟩
  have hv : v ∈ fixedVectors π H.toSubgroup := hK ()
  -- The trace of `ρ` on the conjugate coefficient, by Schur orthogonality.
  obtain ⟨T, hT, -, hTval⟩ := exists_integral_traceCoefficient_mul_star_coefficient
    μ ρ π hρ hπ hirρ hirπ cρ cπ hc d hd H v hv ℓ
  -- The same trace by the character formula.
  obtain ⟨Θ, hΘ, hrest⟩ := hA F n hn ρ hρ hirρ
  obtain ⟨Ψ, hΨ, hΨint, hΨval⟩ := hrest μ π hπ hirπ cρ cπ hc v ℓ
  -- `Θ` is a class function on the regular semisimple set.
  have hclass : ∀ g a : G, IsRegularSemisimple g → Θ (a⁻¹ * g * a) = Θ g := fun g a hg =>
    (hΘ _ ((isRegularSemisimple_inv_mul_mul_iff a g).2 hg)).unique ((hΘ g hg).conjugate a)
  -- The non-elliptic part integrates to zero.
  obtain ⟨Φ', hΦ', hΦ'int, hΦ'val⟩ := hC F n hn μ π hπ hirπ Θ hclass v ℓ Ψ hΨ hΨint
  refine ⟨fun q => Ψ q - Φ' q, ?_, hΨint.sub hΦ'int, ?_⟩
  · intro g
    change Ψ (QuotientGroup.mk g) - Φ' (QuotientGroup.mk g) = _
    rw [hΨ g, hΦ' g]
    by_cases hg : IsRegularElliptic g
    · have hval : Θ g = Θρ ⟨g, hg⟩ := (hΘ g hg.isRegularSemisimple).unique (hΘρ ⟨g, hg⟩)
      rw [ite_eq_left hg, dite_eq_left hg, sub_zero, hval]
    · rw [ite_eq_right hg, dite_eq_right hg, sub_self]
  · rw [integral_sub hΨint hΦ'int, hΦ'val, sub_zero, hΨval H hv T hT, hTval]

end Langlands.BaseChange
