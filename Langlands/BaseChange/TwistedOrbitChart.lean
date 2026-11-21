import Langlands.TraceFormula.TwistedOrbital

noncomputable section

open Filter Set Topology

namespace Langlands.BaseChange

open Langlands.QuotientIntegration Langlands.TraceFormula

universe u v

/-- A section with fixed stabilizer and local lifts near the identity gives
a product chart over its parameters. -/
def TwistedOrbitChartStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (B : Type v) [TopologicalSpace B] (θ : G →* G), Continuous θ →
    ∀ (p : G → B), Continuous p →
    (∀ (g x : G), p (twistedConj θ g x) = p x) →
    ∀ (V : Set B) (H : Subgroup G) (s : V → G), Continuous s →
    ∀ (hp_s : ∀ b, p (s b) = b),
    (∀ b, twistedCentralizer θ (s b) = H) →
    (∀ x : p ⁻¹' V, ∃ g : G, twistedConj θ g (s ⟨p x, x.property⟩) = x) →
    (∀ (b : V) (W : Set G), W ∈ 𝓝 (1 : G) →
      ∀ᶠ x : p ⁻¹' V in 𝓝 (⟨s b, show p (s b) ∈ V from (hp_s b).symm ▸ b.property⟩ : p ⁻¹' V),
        ∃ g ∈ W, twistedConj θ g (s ⟨p x, x.property⟩) = x) →
    ∃ e : V × LeftQuotient H ≃ₜ (p ⁻¹' V : Set G),
      (∀ b g, (e (b, leftQuotientMap H g) : G) = twistedConj θ g (s b)) ∧
      (∀ z, p (e z) = z.1)

theorem exists_twistedOrbitChart : TwistedOrbitChartStatement.{u, v} := by
  intro G _ _ _ B _ θ hθ p hp hinv V H s hs hp_s hH horbit hlift
  let D := (p ⁻¹' V : Set G)
  let parameter (x : D) : V := ⟨p x, x.property⟩
  have hparameter : Continuous parameter :=
    (hp.comp continuous_subtype_val).subtype_mk _
  let F (b : V) : LeftQuotient H → G :=
    descend H (fun g => twistedConj θ g (s b)) (fun c g => by
      have hc : (c : G) ∈ twistedCentralizer θ (s b) := hH b ▸ c.property
      exact twistedConj_left_mul θ (s b) ⟨c, hc⟩ g)
  have hF (b : V) (q : LeftQuotient H) : p (F b q) = b := by
    induction q using Quotient.inductionOn with
    | h g => exact (hinv g (s b)).trans (hp_s b)
  let f (z : V × LeftQuotient H) : D :=
    ⟨F z.1 z.2, show p (F z.1 z.2) ∈ V from (hF z.1 z.2).symm ▸ z.1.property⟩
  have hf (b : V) (g : G) : (f (b, leftQuotientMap H g) : G) = twistedConj θ g (s b) := rfl
  have hfp (z : V × LeftQuotient H) : parameter (f z) = z.1 :=
    Subtype.ext (hF z.1 z.2)
  have hconj (g : G) : Continuous (fun x : G => twistedConj θ g x) :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hcont : Continuous f := by
    let q : V × G → V × LeftQuotient H := Prod.map id (leftQuotientMap H)
    have hq : IsOpenQuotientMap q :=
      IsOpenQuotientMap.id.prodMap (leftQuotient_isOpenQuotientMap H)
    apply hq.continuous_comp_iff.mp
    apply Continuous.subtype_mk
    exact (continuous_snd.inv.mul (hs.comp continuous_fst)).mul (hθ.comp continuous_snd)
  have hinj : Function.Injective f := by
    rintro ⟨b, q⟩ ⟨b', q'⟩ heq
    have hb : b = b' := (hfp _).symm.trans ((congrArg parameter heq).trans (hfp _))
    subst b'
    revert heq
    induction q using Quotient.inductionOn with
    | h g =>
      induction q' using Quotient.inductionOn with
      | h g' =>
        intro heq
        have hgg := congrArg Subtype.val heq
        change twistedConj θ g (s b) = twistedConj θ g' (s b) at hgg
        congr 1
        apply Quotient.sound
        change (QuotientGroup.rightRel H) g g'
        rw [QuotientGroup.rightRel_apply, ← hH b, mem_twistedCentralizer]
        rw [← twistedConj_apply, ← twistedConj_mul, ← hgg, twistedConj_mul, mul_inv_cancel,
          twistedConj_one]
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨g, hg⟩ := horbit x
    exact ⟨(parameter x, leftQuotientMap H g), Subtype.ext hg⟩
  have hopen : IsOpenMap f := by
    intro U hU
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨⟨b, q⟩, hq, rfl⟩
    revert hq
    induction q using Quotient.inductionOn with
    | h g =>
      intro hg
      let y := f (b, leftQuotientMap H g)
      obtain ⟨U₁, hU₁, U₂, hU₂, hsub⟩ := mem_nhds_prod_iff.mp (hU.mem_nhds hg)
      let W := (fun c : G => leftQuotientMap H (c * g)) ⁻¹' U₂
      have hW : W ∈ 𝓝 (1 : G) := by
        have hc := (leftQuotient_isOpenQuotientMap H).continuous.comp
          (continuous_id.mul (continuous_const : Continuous (fun _ : G => g)))
        apply hc.continuousAt
        simpa using hU₂
      let back (x : D) : D :=
        ⟨twistedConj θ g⁻¹ x, show p (twistedConj θ g⁻¹ x) ∈ V from (hinv g⁻¹ x).symm ▸ x.property⟩
      have hback : Continuous back :=
        ((hconj g⁻¹).comp continuous_subtype_val).subtype_mk _
      have hby : back y = (⟨s b, show p (s b) ∈ V from (hp_s b).symm ▸ b.property⟩ : D) := by
        apply Subtype.ext
        change twistedConj θ g⁻¹ (twistedConj θ g (s b)) = s b
        rw [twistedConj_mul, mul_inv_cancel, twistedConj_one]
      have hy₁ : ∀ᶠ x in 𝓝 y, parameter x ∈ U₁ := by
        have hy : parameter y = b := hfp _
        apply hparameter.continuousAt
        rwa [hy]
      have hy₂ := (hback.continuousAt : Tendsto back (𝓝 y) (𝓝 (back y))).eventually
        (show ∀ᶠ x : D in 𝓝 (back y), ∃ c ∈ W,
          twistedConj θ c (s (parameter x)) = x by
          rw [hby]
          exact hlift b W hW)
      change ∀ᶠ x in 𝓝 y, x ∈ f '' U
      filter_upwards [hy₁, hy₂] with x hx₁ hx₂
      obtain ⟨c, hc, heq⟩ := hx₂
      have hpar : parameter (back x) = parameter x := Subtype.ext (hinv g⁻¹ x)
      rw [hpar] at heq
      refine ⟨(parameter x, leftQuotientMap H (c * g)), hsub ⟨hx₁, hc⟩, Subtype.ext ?_⟩
      rw [hf, ← twistedConj_mul, heq]
      change twistedConj θ g (twistedConj θ g⁻¹ x) = x
      rw [twistedConj_mul, inv_mul_cancel, twistedConj_one]
  exact ⟨(Equiv.ofBijective f ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen hcont hopen,
    hf, fun z => hF z.1 z.2⟩

end Langlands.BaseChange
