import Langlands.Representation.Classification.SpehComplementaryLineSeparationStatement
import Langlands.Representation.Classification.SpehComplementarySegments
import Langlands.Representation.Classification.MultisegmentSocleExhaustionProof
import Langlands.Representation.Classification.TadicSupportIdentification
import Langlands.Representation.Classification.SupercuspidalSupportTwist

/-! # Irreducibility of opposite complementary twists on one integral line -/

noncomputable section

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The actual cuspidal supports of opposite complementary twists force their
socle multisegments to be mutually unlinked. -/
theorem integralLineComplementaryIrreducibilityReduction :
    IntegralLineComplementaryIrreducibilityReduction.{uF, uV} F T := by
  classical
  intro hunlinked
  let := T.topology
  intro n hn S s hs ρ hsupport α hα hα0
  have hS : Representation.IsIrreducible S.representation := by
    obtain ⟨k, τ, -, h, A, hA, hirr, hsub⟩ := hs
    exact hirr
  let B := BlockShape.uniform 2 n hn
  let u : Fin B.length → ℝ := fun i => if (i : ℕ) = 0 then α else -α
  let π : ∀ i : Fin B.length,
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier) :=
    T.twistedBlocks B (fun _ => S) u
  have hparam (i : Fin B.length) :
      ∃ a : T.Multisegment.{max uF uV, uF}, a.IsZelevinskySocle (π i) ∧
        ∀ Δ ∈ a, ∃ m : ℤ, Δ.base = ρ.twist ((m : ℝ) + u i) := by
    have hπ : Representation.IsIrreducible (π i).representation :=
      (SmoothRep.isIrreducible_twist_iff (T.determinantPowerCharacter n (u i))
        (T.isOpen_ker_determinantPowerCharacter n (u i)) S).mpr hS
    obtain ⟨a, -, ha⟩ := multisegmentSocleExhaustion.{uF, uV} F T n (π i) hπ
    refine ⟨a, ha, ?_⟩
    have heq := glSupercuspidalSupportUniqueness.{max uF uV, uF}
      p F T n hn (π i) hπ _ _
      (isSupercuspidalSupport_of_isZelevinskySocle ha) (hs.twist (u i))
    intro Δ hΔ
    have hbase : Δ.base ∈ a.cuspidalContent := by
      change Δ.base ∈ Multiset.join (a.map Segment.cuspidalContent)
      exact Multiset.mem_join.mpr
        ⟨Δ.cuspidalContent, Multiset.mem_map.mpr ⟨Δ, hΔ, rfl⟩,
          (Segment.mem_cuspidalContent Δ _).mpr Δ.base_mem_support⟩
    rw [heq] at hbase
    obtain ⟨τ, hτ, htw⟩ := Multiset.mem_map.mp hbase
    obtain ⟨m, hm⟩ := hsupport τ hτ
    refine ⟨m, ?_⟩
    rw [hm, CuspidalDatum.twist_twist] at htw
    simpa only [add_comm] using htw.symm
  choose a ha hbase using hparam
  have hcross : ∀ i j, i ≠ j → ∀ Δ ∈ a i, ∀ Γ ∈ a j, ¬ Δ.IsLinked Γ := by
    intro i j hij Δ hΔ Γ hΓ
    obtain ⟨m, hm⟩ := hbase i Δ hΔ
    obtain ⟨l, hl⟩ := hbase j Γ hΓ
    apply not_isLinked_of_nonintegral_base_twists ρ _ _ _ _ hm hl
    intro z hz
    have hi : (i : ℕ) < 2 := i.isLt
    have hj : (j : ℕ) < 2 := j.isLt
    have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    by_cases hi0 : (i : ℕ) = 0
    · have hj0 : (j : ℕ) ≠ 0 := by omega
      simp only [u, hi0, hj0, ite_true, ite_false] at hz
      apply twice_complementary_exponent_ne_int hα hα0 (z - m + l)
      push_cast
      linarith
    · have hj0 : (j : ℕ) = 0 := by omega
      simp only [u, hi0, hj0, ite_true, ite_false] at hz
      apply twice_complementary_exponent_ne_int hα hα0 (m - l - z)
      push_cast
      linarith
  have hprod := hunlinked (2 * n) B a π ha hcross
  obtain ⟨d, -, -, -, hirr, -⟩ := hprod
  exact hirr

end Langlands.Classification
