import Langlands.Representation.Aubert.QuasicuspidalJacquetSpectrumStatement
import Langlands.Representation.Aubert.QuasicuspidalJacquetClassProof
import Langlands.Representation.Exponents.ExactClassCentralSpectrumProof
import Langlands.Representation.Exponents.JacquetEigenvectorProof
import Langlands.Group.GL.CompactOpen

/-! Generalized split-center spectrum from actual quasicuspidal Jacquet classes. -/

noncomputable section

namespace Langlands.Aubert

open GeneralLinear Parabolic CuspidalSupport SmoothRep

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The actual conditional Jacquet-class identity preserves generalized
split-center occurrence, using admissibility of the supplied representations. -/
theorem quasicuspidalJacquetSpectrum :
    QuasicuspidalJacquetSpectrumStatement.{uF, uV} F T := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro n B π τ hπ hτ hπadm hτadm ε hε hD hqc hNonzero
  let JR := (T.normalizedJacquetFunctor B.reverse).obj π
  let JT := (T.normalizedJacquetFunctor B).obj τ
  let C := (transportFunctor B.reverse B B.reversePermutation
    (conjugatesLevi_reversePermutation F.Carrier B)).obj JR
  have hJR : JR.HasFiniteLength :=
    normalizedJacquetK0_hasFiniteLength.{uF, uV} F T B.reverse π hπ
  have hJT : JT.HasFiniteLength :=
    normalizedJacquetK0_hasFiniteLength.{uF, uV} F T B τ hτ
  have hC : C.HasFiniteLength :=
    transportFunctor_preservesFiniteLength F.Carrier B.reverse B B.reversePermutation
      (conjugatesLevi_reversePermutation F.Carrier B) JR hJR
  obtain ⟨hsign, hclass⟩ :=
    quasicuspidalJacquetClass.{uF, uV} F T n B π τ hπ hτ ε hε hD hqc hNonzero
  rw [normalizedJacquetK0_finiteLengthClass F T B τ hτ hJT,
    normalizedJacquetK0_finiteLengthClass F T B.reverse π hπ hJR,
    leviTransportK0_finiteLengthClass F.Carrier B.reverse B B.reversePermutation
      (conjugatesLevi_reversePermutation F.Carrier B) JR hJR hC] at hclass
  have hJTadm : IsAdmissible JT.representation :=
    Parabolic.isAdmissible_normalizedJacquet F T B τ.representation hτadm
  have hJRadm : IsAdmissible JR.representation :=
    Parabolic.isAdmissible_normalizedJacquet F T B.reverse π.representation hπadm
  have hCadm : IsAdmissible C.representation :=
    isAdmissible_transport B.reversePermutation
      (conjugatesLevi_reversePermutation F.Carrier B) hJRadm
  let := T.leviTopologicalGroup B
  have hcofinal : ∀ H : OpenSubgroup (B.Levi F.Carrier),
      ∃ K : OpenSubgroup (B.Levi F.Carrier),
        IsCompact (K : Set (B.Levi F.Carrier)) ∧ K ≤ H := by
    intro H
    obtain ⟨K, hK, hKH⟩ :=
      T.leviCompactOpen B H (H.isOpen.mem_nhds H.one_mem)
    exact ⟨K, hK, fun _ hx => hKH hx⟩
  let c : (Fin B.length → F.Carrierˣ) →* Subgroup.center (B.Levi F.Carrier) :=
    (B.blockScalarLevi F.Carrier).codRestrict _
      (B.blockScalarLevi_mem_center F.Carrier)
  have hcont : Continuous (B.blockScalarLevi F.Carrier) := by
    change Continuous fun a : Fin B.length → F.Carrierˣ =>
      fun k => GeneralLinear.scalar (n := B.size k) (a k)
    exact continuous_pi fun k =>
      GeneralLinear.scalarContinuous.continuous.comp (continuous_apply k)
  have hc : Continuous c := hcont.subtype_mk _
  refine ⟨hsign, ?_⟩
  intro χ
  exact exactClassCentralSpectrum.{uF, uF, max uF uV}
    (B.Levi F.Carrier) hcofinal (Fin B.length → F.Carrierˣ) c hc
    JT C hJT hC hJTadm hCadm hclass χ

end Langlands.Aubert
