import Langlands.Representation.RankinSelberg.CentralSpectralElement
import Langlands.HarmonicAnalysis.PadicLatticeTopology
import Langlands.HarmonicAnalysis.RowSchwartzAction

/-! # A positive row shell for the inverse-uniformizer central translation -/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis GeneralLinear

universe uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) (n : ℕ)

/-- A compact row cutoff and its central difference give a zero-or-one shell
vanishing at zero and equal to one on the last row of the identity. -/
def HasPositiveCentralRowShell : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  ∃ Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier),
    Φ 0 = 1 ∧
    let Ψ := Φ - rowTranslate (centralSpectralElement T (n + 1)) Φ
    Ψ 0 = 0 ∧ Ψ (lastRow (1 : Langlands.GeneralLinear (n + 1) F.Carrier)) = 1 ∧
      ∀ x, Ψ x = 0 ∨ Ψ x = 1

/-- Multiplication by the inverse-uniformizer scalar acts coordinatewise. -/
theorem vecMul_centralSpectralElement
    (x : Fin (n + 1) → F.Carrier) (i : Fin (n + 1)) :
    Matrix.vecMul x (centralSpectralElement T (n + 1)).val i =
      x i * T.uniformizer⁻¹ := by
  change Matrix.vecMul x (Matrix.diagonal fun _ =>
    (((LocalFactor.PadicAbelian.uniformizerUnit T)⁻¹ : F.Carrierˣ) : F.Carrier)) i = _
  rw [Matrix.vecMul_diagonal]
  rfl

/-- The actual integer row lattice supplies the positive central shell for
every supplied p-adic topology. -/
theorem hasPositiveCentralRowShell : HasPositiveCentralRowShell T n := by
  let := T.topology
  let := T.fieldT2
  let := T.valuativeRel
  let := T.localField
  classical
  let B : Set (Fin (n + 1) → F.Carrier) :=
    Set.univ.pi fun _ => (T.additiveLattice 0 : Set F.Carrier)
  have hBc : IsCompact B :=
    isCompact_univ_pi fun _ => T.isCompact_additiveLattice 0
  have hBo : IsOpen B :=
    isOpen_set_pi Set.finite_univ fun _ _ => T.isOpen_additiveLattice 0
  have hB (x : Fin (n + 1) → F.Carrier) :
      x ∈ B ↔ ∀ i, T.normalizedAbs (x i) ≤ 1 := by
    simp only [B, Set.mem_pi, Set.mem_univ, forall_const, SetLike.mem_coe,
      T.mem_additiveLattice_zero, ← T.normalizedAbs_le_one_iff_mem_integers]
  have hq : (1 : ℝ) < T.residueCardinality := by
    exact_mod_cast T.residueCardinality_gt_one
  have hz : T.normalizedAbs T.uniformizer⁻¹ = (T.residueCardinality : ℝ) :=
    inverseUniformizer_normalizedAbsoluteValue T
  have hsub (x : Fin (n + 1) → F.Carrier)
      (hx : Matrix.vecMul x (centralSpectralElement T (n + 1)).val ∈ B) : x ∈ B := by
    apply (hB x).mpr
    intro i
    have hi := (hB _).mp hx i
    rw [vecMul_centralSpectralElement, T.normalizedAbs_mul, hz] at hi
    have hn := T.normalizedAbs_nonneg (x i)
    nlinarith
  have hB0 : (0 : Fin (n + 1) → F.Carrier) ∈ B :=
    (hB _).mpr fun i => by simp [T.normalizedAbs_zero]
  have hB1 : lastRow (1 : Langlands.GeneralLinear (n + 1) F.Carrier) ∈ B := by
    apply (hB _).mpr
    intro i
    simp only [lastRow, Units.val_one, Matrix.one_apply]
    split <;> simp [T.normalizedAbs_zero, T.normalizedAbs_one]
  have hz1 : Matrix.vecMul
      (lastRow (1 : Langlands.GeneralLinear (n + 1) F.Carrier))
      (centralSpectralElement T (n + 1)).val ∉ B := by
    intro h
    have hi := (hB _).mp h (Fin.last n)
    rw [vecMul_centralSpectralElement] at hi
    simp only [lastRow, Units.val_one, Matrix.one_apply_eq, one_mul, hz] at hi
    exact (not_le_of_gt hq) hi
  let Φ := Hecke.TestFunction.characteristic ⟨hBc.isClosed, hBo⟩ hBc
  have hΦ (x : Fin (n + 1) → F.Carrier) :
      Φ x = B.indicator (fun _ => (1 : ℂ)) x := rfl
  refine ⟨Φ, ?_, ?_, ?_, ?_⟩
  · rw [hΦ, Set.indicator_of_mem hB0]
  · change Φ 0 - Φ (Matrix.vecMul 0 (centralSpectralElement T (n + 1)).val) = 0
    simp only [Matrix.zero_vecMul, sub_self]
  · change Φ (lastRow 1) -
      Φ (Matrix.vecMul (lastRow 1) (centralSpectralElement T (n + 1)).val) = 1
    simp only [hΦ,
      Set.indicator_of_mem hB1, Set.indicator_of_notMem hz1, sub_zero]
  · intro x
    change Φ x - Φ (Matrix.vecMul x (centralSpectralElement T (n + 1)).val) = 0 ∨
      Φ x - Φ (Matrix.vecMul x (centralSpectralElement T (n + 1)).val) = 1
    simp only [hΦ]
    by_cases hx : Matrix.vecMul x (centralSpectralElement T (n + 1)).val ∈ B
    · exact Or.inl (by
        rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hsub x hx), sub_self])
    · rw [Set.indicator_of_notMem hx, sub_zero]
      by_cases hxB : x ∈ B
      · exact Or.inr (Set.indicator_of_mem hxB _)
      · exact Or.inl (Set.indicator_of_notMem hxB _)

end Langlands.RankinSelberg
