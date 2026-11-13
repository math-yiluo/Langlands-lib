import Langlands.Representation.Intertwining.PQIntertwiningLeviStatements
import Langlands.Representation.Intertwining.PQOuterLeviRegularity

/-! # Proof of Renard VII.3.5 (iii)

Intertwining operators and induction in stages for two parabolics `P₁ ⊂ Q₁`, `P₂ ⊂ Q₂`
whose Levi subgroups `L` of `Q₁` and `Q₂` agree and with `P₁ ∩ L = P₂ ∩ L`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- **Renard VII.3.5 (iii)**: for `P₁ ∩ L = P₂ ∩ L`, `Qᵢ = PᵢL = LUᵢ`, the integration domains
`N̄₁ ∩ N₂` and `Ū₁ ∩ U₂` carry compatible Haar measures, the stage identification
`f ↦ f̃` exists, and if `i_{P'}^L(σ)` is `Q₁Q₂`-regular then `σ` is `P₁P₂`-regular and
`J_{Q₂|Q₁}(i_{P'}^L(σ)) f̃ = (J_{P₂|P₁}(σ) f)~`. -/
theorem pqIntertwiningOuterLevi : PQIntertwiningOuterLeviStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ M P₁ N₁ P₂ N₂ Pb₁ Nb₁ L Q₁ U₁ Q₂ U₂ Qb₁ Ub₁ P' N'
    p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂
    pb₁ lb₁ rb₁ hpb₁ hlb₁ hrb₁ _hmulb₁
    q₁ lQ₁ rQ₁ hq₁ hlQ₁ hrQ₁ hmulQ₁ q₂ lQ₂ rQ₂ hq₂ hlQ₂ hrQ₂ hmulQ₂
    qb₁ lqb₁ rqb₁ hqb₁ hlqb₁ hrqb₁ _hmulqb₁
    hlev₂ hlevb hopp hlevQ₂ hlevQb hoppQ hPQ₁ hPQ₂
  have := hlQ₁.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints L) := RationalPointFamily.pointTopology
  have := leviPoints_locallyCompactSpace q₁ lQ₁ hq₁ hlQ₁
  have := leviPoints_nonarchimedeanGroup q₁ lQ₁ hq₁ hlQ₁
  intro p' l' r' hp' hl' hr' hmul' hM hP'₁ hP'₂ A a ha AL aL haL emb c₁ c₂ V W _ _ _ _
    Compatible
  have hVW : V = W := outerRadical_inf_eq hG hp₁ hl₁ hp₂ hl₂ hr₂ hmul₂ hpb₁ hlb₁ hrb₁
    hq₁ hlQ₁ hq₂ hlQ₂ hrQ₂ hmulQ₂ hqb₁ hlqb₁ hrqb₁ hp' hl' hr' hmul'
    hlev₂ hlevb hopp hlevQ₂ hlevQb hoppQ hPQ₁ hPQ₂ hM hP'₁ hP'₂
  have hV : IsClosed (V : Set (rationalPoints G)) :=
    (isClosed_pointImage_comp pb₁ rb₁ hpb₁.isClosedSubgroup hrb₁.1.isClosedSubgroup).inter
      (isClosed_pointImage_comp p₂ r₂ hp₂.isClosedSubgroup hr₂.1.isClosedSubgroup)
  refine ⟨fun haarW _ => ?_, ?_⟩
  · obtain ⟨haarV, hH, hint⟩ := exists_haar_integral_eq_of_subgroup_eq hVW haarW
    exact ⟨haarV, hH, fun φ _ _ => hint φ⟩
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l₁ hl₁
  intro σ X evalG₁ evalG₂ evalL evalQ₁ evalQ₂
  let Φ₁ := (leviInductionStagesIso p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
    q₁ lQ₁ rQ₁ hq₁ hlQ₁ hrQ₁ hmulQ₁ p' l' r' hp' hl' hr' hmul' hPQ₁ hM
    (hP'₁.trans (inf_comm _ _)) hG).app σ
  have hF : ∀ (f : (leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj σ)
      (g : rationalPoints G) (x : rationalPoints L),
      evalL (evalQ₁ (SmoothRep.hom Φ₁.hom f) g) x = (c₁ x)⁻¹ • evalG₁ f (emb x * g) :=
    leviInductionStagesIso_eval' p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
      q₁ lQ₁ rQ₁ hq₁ hlQ₁ hrQ₁ hmulQ₁ p' l' r' hp' hl' hr' hmul' hPQ₁ hM
      (hP'₁.trans (inf_comm _ _)) hG σ
  refine ⟨fun f => ⟨SmoothRep.hom Φ₁.hom f, hF f⟩, fun hreg =>
    ⟨outer_isPQRegular hG hp₁ hl₁ hr₁ hmul₁ hp₂ hl₂ hr₂ hmul₂ hq₁ hlQ₁ hrQ₁ hmulQ₁
      hq₂ hlQ₂ hrQ₂ hmulQ₂ hp' hl' hr' hmul' hlev₂ hlevQ₂ hPQ₁ hPQ₂ hM hP'₁ hP'₂
      a ha aL haL σ hreg, ?_⟩⟩
  intro haarW haarV _ _ hcompat J JQ hJ hJQ f F hFf g x
  have hFeq : F = SmoothRep.hom Φ₁.hom f :=
    leviInductionStages_ext q₁ lQ₁ rQ₁ hq₁ hlQ₁ hrQ₁ hmulQ₁ p' l' r' hp' hl' hr' hmul' σ F
      (SmoothRep.hom Φ₁.hom f) (fun g x => (hFf g x).trans (hF f g x).symm)
  have hop := outer_intertwiner_stages hG hp₁ hl₁ hr₁ hmul₁ hp₂ hl₂ hr₂ hmul₂
    hq₁ hlQ₁ hrQ₁ hmulQ₁ hq₂ hlQ₂ hrQ₂ hmulQ₂ hp' hl' hr' hmul' hlev₂ hlevQ₂ hPQ₁ hPQ₂
    hM hP'₁ hP'₂ aL haL V W hVW hV haarW haarV hcompat σ hreg J JQ hJ hJQ f
  have hJQ' : JQ F = SmoothRep.hom ((leviInductionStagesIso p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂
      q₂ lQ₂ rQ₂ hq₂ hlQ₂ hrQ₂ hmulQ₂ p' l' r' hp' hl' hr' hmul' hPQ₂
      (outer_levi₂_eq hlev₂ hlevQ₂ hM) (outer_parabolic₂_eq hlevQ₂ hP'₂) hG).hom.app σ)
      (J f) :=
    (congrArg JQ hFeq).trans hop
  have hemb : rationalPoints.map (lQ₂ ≫ q₂) x = emb x := by
    change rationalPoints.map (lQ₂ ≫ q₂) x = rationalPoints.map (lQ₁ ≫ q₁) x
    rw [hlevQ₂]
  refine (congrArg (fun H => evalL (evalQ₂ H g) x) hJQ').trans ?_
  refine (leviInductionStagesIso_eval' p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂
    q₂ lQ₂ rQ₂ hq₂ hlQ₂ hrQ₂ hmulQ₂ p' l' r' hp' hl' hr' hmul' hPQ₂
    (outer_levi₂_eq hlev₂ hlevQ₂ hM) (outer_parabolic₂_eq hlevQ₂ hP'₂) hG σ (J f) g x).trans ?_
  exact congrArg (fun y => (c₂ x)⁻¹ • evalG₂ (J f) (y * g)) hemb

end Langlands.Aubert.General.RepresentedParabolic
