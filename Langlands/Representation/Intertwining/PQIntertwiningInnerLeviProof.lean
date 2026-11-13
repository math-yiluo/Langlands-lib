import Langlands.Representation.Intertwining.PQIntertwiningLeviStatements
import Langlands.Representation.Intertwining.InnerLeviRegularity
import Langlands.Representation.Intertwining.InnerLeviIntegrationDomain

/-! # Renard VII.3.5 (ii): intertwining operators and induction in stages, inner Levi

Proof of `PQIntertwiningInnerLeviStatement`. The integration domain `V = N̄₁(F) ∩ N₂(F)` is the
image of `V' = N̄₁'(F) ∩ N₂'(F)` under `emb : L(F) → G(F)`, so Haar measures on `V'` push
forward to compatible Haar measures on `V`, and every compatible Haar measure on `V` is such an
image. Induction in stages provides `f̃`; regularity passes from `P₁P₂` to `P₁'P₂'` through
the restriction `T f = f̃(1)`; the operator identity follows from uniqueness of the
integral-normalized operator.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

universe u v

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VII.3.5, Proposition, part (ii). -/
theorem pqIntertwiningInnerLevi : PQIntertwiningInnerLeviStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ M P₁ N₁ P₂ N₂ Pb₁ Nb₁ Q L U P₁' N₁' P₂' N₂' Pb₁' Nb₁'
    p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂
    pb₁ lb₁ rb₁ hpb₁ hlb₁ hrb₁ _ q lQ rQ hq hlQ hrQ hmulQ h₂₁ hb hPP hPQ₁ hPQ₂
  have := hlQ.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints L) := RationalPointFamily.pointTopology
  have := leviPoints_locallyCompactSpace q lQ hq hlQ
  have := leviPoints_nonarchimedeanGroup q lQ hq hlQ
  intro p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' p₂' l₂' r₂' hp₂' hl₂' hr₂' hmul₂'
    pb₁' lb₁' rb₁' hpb₁' hlb₁' hrb₁' _ hM₁ h₂₁' hb' hPP' hPL₁ hPL₂ A a ha emb c V V'
    _ _ _ _ Compatible
  have hM₂ : l₂' ≫ p₂' ≫ lQ ≫ q = l₂ ≫ p₂ := by
    rw [h₂₁, ← hM₁, ← Category.assoc, h₂₁', Category.assoc]
  have hVV : V = V'.map (rationalPoints.map (lQ ≫ q)) :=
    innerIntegrationDomain_eq_map hG p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂
      hpb₁ hlb₁ hrb₁ q lQ rQ hq hlQ hrQ hmulQ h₂₁ hb hPP hPQ₁ hPQ₂
      p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' p₂' l₂' r₂' hp₂' hl₂' hr₂' hmul₂'
      hpb₁' hlb₁' hrb₁' hM₁ h₂₁' hb' hPP' hPL₁ hPL₂
  obtain ⟨e, he⟩ := exists_leviSubgroupEquiv q lQ hq hlQ V V' hVV
  have hcomp : ∀ φ : rationalPoints G → ℂ,
      (fun x : V' => φ (emb x)) = fun x : V' => φ (e x) :=
    fun φ => funext fun x => congrArg φ (he x).symm
  refine ⟨?_, ?_⟩
  · intro haar' hhaar'
    obtain ⟨h₁, h₂⟩ := map_isHaarMeasure_integral_eq V e haar'
    refine ⟨haar'.map e, h₁, ?_⟩
    intro φ _ _
    rw [hcomp φ]
    exact h₂ φ
  · have := hl₁.isConnectedReductive.isAffineHom
    let : TopologicalSpace (rationalPoints M) := leviPointTopology l₁ hl₁
    intro σ X₁ X₂ evalG₁ evalG₂ evalL₁ evalL₂ evalQ₁
    refine ⟨fun f => ⟨SmoothRep.hom ((leviInductionStagesIso p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
        q lQ rQ hq hlQ hrQ hmulQ p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' hPQ₁ hM₁
        (hPL₁.trans (inf_comm _ _)) hG).hom.app σ) f,
      leviInductionStagesIso_eval' p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ q lQ rQ hq hlQ hrQ hmulQ
        p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' hPQ₁ hM₁ (hPL₁.trans (inf_comm _ _)) hG σ f⟩,
      fun hreg => ⟨innerLevi_isPQRegular hG p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ p₂ l₂ r₂ hp₂ hl₂ hr₂
        hmul₂ q lQ rQ hq hlQ hrQ hmulQ hPQ₁ hPQ₂ p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁'
        p₂' l₂' r₂' hp₂' hl₂' hr₂' hmul₂' hM₁ hM₂ hPL₁ hPL₂ a σ hreg, ?_⟩⟩
    intro haar' haar hhaar' hhaar hcompat J J' hJ hJ' f F hF g x
    have : SecondCountableTopology (rationalPoints G) :=
      RationalPointFamily.reductiveRationalPoint_secondCountable k G hG
    have hVc : IsClosed (V : Set (rationalPoints G)) :=
      (isClosed_pointImage_comp pb₁ rb₁ hpb₁.isClosedSubgroup hrb₁.1.isClosedSubgroup).inter
        (isClosed_pointImage_comp p₂ r₂ hp₂.isClosedSubgroup hr₂.1.isClosedSubgroup)
    have hhaar_eq : haar = haar'.map e := by
      refine haar_eq_map_of_integral_eq V hVc e haar' haar ?_
      intro φ hφ hφs
      rw [← hcomp φ]
      exact hcompat φ hφ hφs
    exact innerLevi_integralIntertwiner_formula hG p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
      p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂ q lQ rQ hq hlQ hrQ hmulQ hPQ₁ hPQ₂
      p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' p₂' l₂' r₂' hp₂' hl₂' hr₂' hmul₂' hM₁ hM₂ hPL₁ hPL₂
      a ha V V' inf_le_right e he haar' haar hhaar_eq σ hreg J J' hJ hJ' f F hF g x

end Langlands.Aubert.General.RepresentedParabolic
