import Langlands.Representation.RankinSelberg.RootModelExpansionStatement
import Langlands.Representation.RankinSelberg.RootTorusProductProof

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker
open scoped BigOperators

universe uF uV uW

/-- Uniform root-coordinate expansion of the actual translated coefficients. -/
theorem equalRankRootExpansion {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) :
    EqualRankRootExpansionStatement.{uF, uV, uW} F T n := by
  classical
  let := T.topology
  let A := Fin (n + 1) → F.Carrierˣ
  let d : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
  let w : A → ℂ := fun a =>
    (∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^
      ((i.val + 1) * (n - i.val)))⁻¹
  intro V _ _ W _ _ π σ ψ hπ hσ
  obtain ⟨X, hX, hπ⟩ := hπ
  obtain ⟨Y, hY, hσ⟩ := hσ
  let I := {χ // χ ∈ X} × {χ // χ ∈ Y}
  let η : I → A → ℂ := fun z a => z.1.val (d a) * z.2.val (d a) * w a
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  obtain ⟨hη, hprod⟩ := rootTorusProduct F T n X Y hX hY
  refine ⟨Fintype.card I, fun j => η (e.symm j), ?_, ?_⟩
  · intro j
    exact hη (e.symm j)
  · intro ℓ ℓ' f f' Φ k
    obtain ⟨φ, hφ⟩ := hπ ℓ (modelRepresentation π ℓ k f)
    obtain ⟨φ', hφ'⟩ := hσ ℓ' (modelRepresentation σ ℓ' k f')
    have hf (a : A) :
        f.val.val (GeneralLinear.Iwasawa.diagonalUnits a * k) =
          ∑ χ : {χ // χ ∈ X}, φ χ.val (fun i : Fin n =>
            ((a i.castSucc / a i.succ : F.Carrierˣ) : F.Carrier)) * χ.val a := by
      exact (hφ a).trans (Finset.sum_coe_sort X (fun χ =>
        φ χ (fun i : Fin n =>
          ((a i.castSucc / a i.succ : F.Carrierˣ) : F.Carrier)) * χ a)).symm
    have hf' (a : A) :
        f'.val.val (GeneralLinear.Iwasawa.diagonalUnits a * k) =
          ∑ χ : {χ // χ ∈ Y}, φ' χ.val (fun i : Fin n =>
            ((a i.castSucc / a i.succ : F.Carrierˣ) : F.Carrier)) * χ.val a := by
      exact (hφ' a).trans (Finset.sum_coe_sort Y (fun χ =>
        φ' χ (fun i : Fin n =>
          ((a i.castSucc / a i.succ : F.Carrierˣ) : F.Carrier)) * χ a)).symm
    obtain ⟨Ψ, hΨ⟩ := hprod (fun χ => φ χ.val) (fun χ => φ' χ.val) Φ k
    refine ⟨fun j => Ψ (e.symm j), ?_⟩
    intro a
    have hh := hΨ a
    rw [← hf (d a), ← hf' (d a)] at hh
    exact hh.trans (e.symm.sum_comp
      (fun z => Ψ z (fun i => (a i : F.Carrier)) * η z a)).symm

end Langlands.RankinSelberg
