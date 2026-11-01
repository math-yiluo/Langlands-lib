import Langlands.Representation.Aubert.SignedEffectivityStatement
import Langlands.Representation.Aubert.LengthFilteredJacquetConcentration
import Langlands.Representation.Aubert.WholeTargetGradedConcentration
import Langlands.Representation.Aubert.QuasicuspidalCutVanishing
import Langlands.Representation.CuspidalSupport.LeviAssociation

/-! Common-sign effectivity from the actual corrected support filtration. -/

noncomputable section

namespace Langlands.Aubert

open GeneralLinear SmoothRep CuspidalSupport ActualCutComplex

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

set_option maxHeartbeats 600000

/-- The support sign is common to every irreducible constituent of induction
from the given irreducible quasicuspidal Levi representation. -/
theorem signedEffectivity : SignedEffectivityStatement.{uF,uV} F T := by
  let := T.topology
  intro n B σ hσ hqc π hπ hsub
  by_cases hn : n = 0
  · subst n
    exact effective_rankZero.{uF,uV} F T B π (hasFiniteLength_of_isIrreducible hπ)
  have hn' : 0 < n := Nat.pos_of_ne_zero hn
  have hboundB : HasJacquetBlockBound.{uF,uV} F T B π :=
    quasicuspidal_subquotient_hasJacquetBlockBound.{uF,uV} F T B σ hqc π hsub
  have hgraded (C : BlockShape n) (hBC : LevisAssociated (F := F.Carrier) B C) :
      UpperSingletonGradedConcentrationBelow.{uF,max uF uV} T π C (B.length - 1) := by
    have hlen : B.length = C.length := hBC.length_eq
    have hboundC : HasJacquetBlockBound.{uF,uV} F T C π := by
      intro D hD
      apply hboundB D
      rwa [hlen]
    rw [hlen]
    intro θ w hθ hLower hwθ
    exact ⟨fun hm => bundledSupportQuotient_injective_before_target.{uF,uV}
      T π C θ w hwθ hboundC hθ hLower hm,
      fun k hk => bundledSupportQuotient_exact_below_target.{uF,uV}
        T π C θ w hwθ hboundC hθ hLower k hk⟩
  have hzero (k : ℕ) (hk : B.length - 1 < k) (C : BlockShape n)
      (_hBC : LevisAssociated (F := F.Carrier) B C) :
      Subsingleton ((jacquetDiagram T C π.representation).Degree k) := by
    apply (jacquetDegree_subsingleton_iff.{uF,max uF uV} T C π.representation k).mp
    exact jacquet_degree_subsingleton_of_aboveSupport.{uF,uV} F T B C π
      (quasicuspidal_degreesVanishAboveSupport.{uF,uV} F T B hn' σ hqc π hsub) k hk
  exact effective_of_associatedJacquet.{uF,uV} F T B hn' σ
    (hasFiniteLength_of_isIrreducible hσ) hqc π (hasFiniteLength_of_isIrreducible hπ) hsub
    (jacquetConcentratedAt_of_upperSingletonGraded.{uF,uV} T
      (LevisAssociated (F := F.Carrier) B) π (B.length - 1) hgraded hzero)

end Langlands.Aubert
