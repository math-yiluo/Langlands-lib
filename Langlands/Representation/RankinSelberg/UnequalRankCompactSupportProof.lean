import Langlands.Representation.RankinSelberg.UnequalRankCompactSupportStatement
import Langlands.Representation.RankinSelberg.UnequalRankIwasawaSupportProof
import Langlands.Representation.Whittaker.SmoothSimpleRootSupportProof

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker

universe uF uV

/-- Every actual Whittaker-type coefficient has compact rectangular support
in the unequal-rank block, uniformly in the smaller general linear group. -/
theorem unequalRankCompactSupport
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n j k : ℕ) :
    UnequalRankCompactSupportStatement.{uF, uV} F T n j k := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro ψ V _ _ π hπ ℓ _ f
  obtain ⟨R, hR, hs⟩ :=
    Whittaker.smoothSimpleRootSupport.{uF, uV} F T (n + (j + k + 1))
      ψ V π hπ.1.1 ℓ f
  obtain ⟨C, hC, hg⟩ := unequalRankIwasawaSupport F T n j k R hR
  refine ⟨C, hC, ?_⟩
  intro g x hf
  obtain ⟨ϖ, hϖ⟩ := GeneralLinear.Iwasawa.exists_isUniformizingElement F.Carrier
  obtain ⟨u, hu, lam, κ, hκ, hm⟩ :=
    GeneralLinear.Iwasawa.exists_iwasawa hϖ (unequalRankMatrix j k g x)
  let a : Fin (n + (j + k + 1) + 1) → F.Carrierˣ := fun i => ϖ ^ lam i
  have hm' : unequalRankMatrix j k g x =
      u * GeneralLinear.Iwasawa.diagonalUnits a * κ := hm
  have hn : f.val.val (GeneralLinear.Iwasawa.diagonalUnits a * κ) ≠ 0 := by
    intro hz
    apply hf
    rw [hm', mul_assoc]
    change f.val.val ((⟨u, hu⟩ : GeneralLinear.upperUnipotent _ F.Carrier).val *
      (GeneralLinear.Iwasawa.diagonalUnits a * κ)) = 0
    rw [f.val.property ⟨u, hu⟩, hz, mul_zero]
  exact hg g x u a κ hu hκ hm' (hs a κ hκ hn)

end Langlands.RankinSelberg
