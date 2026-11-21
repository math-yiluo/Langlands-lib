import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! # Averaging over a normalized subgroup preserves quotient integrals

Let `Λ` be a countable subgroup of a measurable group `H` with a strict measurable
fundamental domain `D` for left multiplication, and let `j : V → H` be an injective
measurable homomorphism whose image is normalized by `Λ`. Let `Γ ≤ V` be a subgroup with
`j Γ ⊆ Λ` that is stable under conjugation by `Λ`, and let `C` be a measurable fundamental
domain of `Γ` in `V`. For a left `Λ`-invariant `F ≥ 0` on `H`,
averaging `F` over `C` on the left does not change its integral over `D`:

`∫_D ∫_C F (j v * g) dν(v) dμ(g) = ν C * ∫_D F dμ`.

This is the measure-theoretic core of the statement that a constant term along a unipotent
radical `U` preserves integrals over `P₀(F) \ G(𝔸)` (Bernstein–Lapid §7.3). -/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u v

open MeasureTheory Set Function
open scoped ENNReal

namespace Langlands.Analysis.FibreAverage

section Reindex

variable {Γ Λ : Type*} [Group Γ] [MulAction Γ Λ]

variable (Γ) in
/-- A choice of one point in every orbit. -/
private def orbitRep (l : Λ) : Λ :=
  (Quotient.out (Quotient.mk (MulAction.orbitRel Γ Λ) l) : Λ)

private theorem orbitRep_smul (γ : Γ) (l : Λ) : orbitRep Γ (γ • l) = orbitRep Γ l := by
  unfold orbitRep
  congr 1
  exact Quotient.sound ((MulAction.orbitRel_apply).mpr (MulAction.mem_orbit l γ))

variable (Γ) in
private theorem exists_smul_eq_orbitRep (l : Λ) : ∃ γ : Γ, γ • l = orbitRep Γ l := by
  have h : MulAction.orbitRel Γ Λ (orbitRep Γ l) l :=
    Quotient.mk_out (s := MulAction.orbitRel Γ Λ) l
  obtain ⟨γ, hγ⟩ := (MulAction.orbitRel_apply).mp h
  exact ⟨γ, hγ⟩

variable (Γ) in
/-- The indicator of the chosen orbit representatives. -/
private def repWeight (l : Λ) : ℝ≥0∞ := by
  classical exact if l = orbitRep Γ l then 1 else 0

private theorem tsum_repWeight_smul (hfree : ∀ (γ γ' : Γ) (l : Λ), γ • l = γ' • l → γ = γ')
    (l : Λ) : ∑' γ : Γ, repWeight Γ (γ • l) = 1 := by
  obtain ⟨γ₀, hγ₀⟩ := exists_smul_eq_orbitRep Γ l
  classical
  rw [tsum_eq_single γ₀]
  · have h : γ₀ • l = orbitRep Γ (γ₀ • l) := by rw [orbitRep_smul, hγ₀]
    simp only [repWeight]
    split_ifs
    rfl
  · intro γ hγ
    have hne : γ • l ≠ orbitRep Γ (γ • l) := by
      rw [orbitRep_smul, ← hγ₀]
      exact fun h => hγ (hfree _ _ _ h)
    simp only [repWeight]
    split_ifs <;> first | rfl | (exfalso; contradiction)

/-- Two families with the same sums over every free orbit have the same total sum. -/
theorem tsum_eq_tsum_of_orbit_sums (hfree : ∀ (γ γ' : Γ) (l : Λ), γ • l = γ' • l → γ = γ')
    (a b : Λ → ℝ≥0∞) (hab : ∀ l, ∑' γ : Γ, a (γ • l) = ∑' γ : Γ, b (γ • l)) :
    ∑' l, a l = ∑' l, b l := by
  have key : ∀ c : Λ → ℝ≥0∞,
      ∑' l, c l = ∑' l, repWeight Γ l * ∑' γ : Γ, c (γ • l) := by
    intro c
    calc ∑' l, c l = ∑' l, c l * ∑' γ : Γ, repWeight Γ (γ⁻¹ • l) := by
          refine tsum_congr fun l => ?_
          rw [show ∑' γ : Γ, repWeight Γ (γ⁻¹ • l) = 1 from
            ((Equiv.inv Γ).tsum_eq (fun γ => repWeight Γ (γ • l))).trans
              (tsum_repWeight_smul hfree l), mul_one]
      _ = ∑' γ : Γ, ∑' l, c l * repWeight Γ (γ⁻¹ • l) := by
          simp_rw [← ENNReal.tsum_mul_left]
          exact ENNReal.tsum_comm
      _ = ∑' γ : Γ, ∑' m, c (γ • m) * repWeight Γ m := by
          refine tsum_congr fun γ => ?_
          rw [← (MulAction.toPerm γ : Equiv.Perm Λ).tsum_eq]
          simp
      _ = ∑' l, repWeight Γ l * ∑' γ : Γ, c (γ • l) := by
          rw [ENNReal.tsum_comm]
          refine tsum_congr fun m => ?_
          rw [← ENNReal.tsum_mul_left]
          exact tsum_congr fun γ => mul_comm _ _
  rw [key a, key b]
  exact tsum_congr fun l => by rw [hab l]

end Reindex

variable {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableInv H]
  {V : Type*} [Group V] [MeasurableSpace V] [MeasurableMul₂ V] [MeasurableInv V]

omit [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableInv H] in
/-- For a strict fundamental domain, the indicators of the translates sum to one. -/
theorem tsum_indicator_mul_eq_one (Λ : Subgroup H) {D : Set H}
    (hD : ∀ x : H, ∃! l : Λ, (l : H) * x ∈ D) (x : H) :
    ∑' l : Λ, D.indicator (fun _ => (1 : ℝ≥0∞)) ((l : H) * x) = 1 := by
  obtain ⟨l₀, hl₀, huniq⟩ := hD x
  rw [tsum_eq_single l₀]
  · simp [hl₀]
  · intro l hl
    have : (l : H) * x ∉ D := fun h => hl (huniq l h)
    simp [this]

variable (μ : Measure H) [μ.IsMulLeftInvariant] [SFinite μ]
  (Λ : Subgroup H) [Countable Λ] (D : Set H) (hDm : MeasurableSet D)
  (hD : ∀ x : H, ∃! l : Λ, (l : H) * x ∈ D)
  (j : V →* H) (hj : Measurable j) (hjinj : Injective j)
  (Γ : Subgroup V) (hΓ : ∀ v ∈ Γ, j v ∈ Λ)
  (cj : Λ → V → V) (hcj : ∀ l v, j (cj l v) = l * j v * (l : H)⁻¹)
  (hΓc : ∀ (l : Λ) (v : V), v ∈ Γ → cj l v ∈ Γ)
  (ν : Measure V) [ν.IsMulLeftInvariant] [ν.IsInvInvariant] [SFinite ν]
  (hcjm : ∀ l, MeasurePreserving (cj l) ν ν)
  (C : Set V) (hCm : MeasurableSet C) (hC : IsFundamentalDomain Γ C ν)

include hjinj hΓ in
private theorem countable_Γ : Countable Γ := by
  refine Injective.countable (f := fun γ : Γ => (⟨j (γ : V), hΓ γ γ.2⟩ : Λ)) ?_
  intro γ γ' h
  exact Subtype.ext (hjinj (congrArg Subtype.val h))

/-- The homomorphism `Γ → Λ`. -/
private def toΛ (hΓ : ∀ v ∈ Γ, j v ∈ Λ) : Γ →* Λ where
  toFun γ := ⟨j (γ : V), hΓ γ γ.2⟩
  map_one' := Subtype.ext (map_one j)
  map_mul' γ γ' := Subtype.ext (map_mul j (γ : V) γ')

include hjinj hcj in
private theorem cj_inv_cj (l : Λ) (v : V) : cj l⁻¹ (cj l v) = v := by
  apply hjinj
  rw [hcj, hcj]
  simp [mul_assoc]

include hjinj hcj in
private theorem cj_mul (l : Λ) (v w : V) : cj l (v * w) = cj l v * cj l w := by
  apply hjinj
  rw [map_mul, hcj, hcj, hcj, map_mul]
  simp [mul_assoc]

include hjinj hcj hΓ hΓc hcjm hC in
/-- The conjugate of the fundamental domain is again a fundamental domain. -/
private theorem isFundamentalDomain_preimage_cj (r : Λ) :
    IsFundamentalDomain Γ (cj r⁻¹ ⁻¹' C) ν := by
  let e : Γ → Γ := fun γ => ⟨cj r γ, hΓc r γ γ.2⟩
  have he : Bijective e := by
    refine ⟨fun γ γ' h => ?_, fun γ => ?_⟩
    · apply Subtype.ext
      have := congrArg (fun x : Γ => cj r⁻¹ (x : V)) h
      simpa [e, cj_inv_cj Λ j hjinj cj hcj] using this
    · refine ⟨⟨cj r⁻¹ γ, hΓc r⁻¹ γ γ.2⟩, Subtype.ext ?_⟩
      have := cj_inv_cj Λ j hjinj cj hcj r⁻¹ (γ : V)
      simpa [e] using this
  refine hC.preimage_of_equiv (hcjm r⁻¹).quasiMeasurePreserving he fun γ x => ?_
  change cj r⁻¹ (cj r γ * x) = (γ : V) * cj r⁻¹ x
  rw [cj_mul Λ j hjinj cj hcj, cj_inv_cj Λ j hjinj cj hcj]

/-- The indicator of `D` with value `1`. -/
local notation "𝟙[" D "]" => Set.indicator D (fun _ => (1 : ℝ≥0∞))

include hDm hj in
private theorem measurable_indicator_comp {X : Type*} [MeasurableSpace X] {φ : X → H}
    (hφ : Measurable φ) : Measurable fun x => 𝟙[D] (φ x) :=
  (measurable_const.indicator hDm).comp hφ

include hjinj hΓ hC hCm hDm hj in
/-- Orbit sums of the first family. -/
private theorem tsum_orbit_left (g : H) (r : H) :
    ∑' γ : Γ, ∫⁻ v in C, 𝟙[D] ((j v)⁻¹ * (j (γ : V) * r) * g) ∂ν =
      ∫⁻ x, 𝟙[D] (j x * r * g) ∂ν := by
  have : Countable Γ := countable_Γ Λ j hjinj Γ hΓ
  let φ : V → ℝ≥0∞ := fun x => 𝟙[D] ((j x)⁻¹ * r * g)
  have h1 : ∀ γ : Γ, ∫⁻ v in C, 𝟙[D] ((j v)⁻¹ * (j (γ : V) * r) * g) ∂ν =
      ∫⁻ v in C, φ (γ⁻¹ • v) ∂ν := by
    intro γ
    refine setLIntegral_congr_fun hCm fun v _ => ?_
    simp only [φ, Subgroup.smul_def, smul_eq_mul, map_mul, map_inv, Subgroup.coe_inv, mul_inv_rev,
      inv_inv, mul_assoc]
  rw [tsum_congr h1, ← hC.lintegral_eq_tsum' φ]
  have := lintegral_inv_eq_self (μ := ν) (fun x => 𝟙[D] (j x * r * g))
  simpa [φ, map_inv] using this

include hjinj hcj hΓ hΓc hcjm hC hCm hDm hj in
/-- Orbit sums of the second family. -/
private theorem tsum_orbit_right (g : H) (r : Λ) :
    ∑' γ : Γ, ∫⁻ w in C, 𝟙[D] (j (γ : V) * r * j w * g) ∂ν =
      ∫⁻ x, 𝟙[D] (j x * r * g) ∂ν := by
  have : Countable Γ := countable_Γ Λ j hjinj Γ hΓ
  let ψ : V → ℝ≥0∞ := fun x => 𝟙[D] (j x * r * g)
  have hψ : Measurable ψ := measurable_indicator_comp D hDm j hj
    (((hj.mul_const _).mul_const _))
  let Y : Set V := cj r⁻¹ ⁻¹' C
  have hYm : MeasurableSet Y := (hcjm r⁻¹).measurable hCm
  have hY : IsFundamentalDomain Γ Y ν :=
    isFundamentalDomain_preimage_cj Λ j hjinj Γ hΓ cj hcj hΓc ν hcjm C hC r
  have h1 : ∀ γ : Γ, ∫⁻ w in C, 𝟙[D] (j (γ : V) * r * j w * g) ∂ν =
      ∫⁻ x in Y, ψ (γ • x) ∂ν := by
    intro γ
    have hrw : ∀ w, j (γ : V) * r * j w * g = j ((γ : V) * cj r w) * r * g := by
      intro w
      have : j (cj r w) * r = r * j w := by rw [hcj]; group
      rw [map_mul, mul_assoc (j (γ : V)) (j (cj r w)), this]
      group
    have hmem : ∀ w, w ∈ C ↔ cj r w ∈ Y := by
      intro w
      change w ∈ C ↔ cj r⁻¹ (cj r w) ∈ C
      rw [cj_inv_cj Λ j hjinj cj hcj]
    calc ∫⁻ w in C, 𝟙[D] (j (γ : V) * r * j w * g) ∂ν
        = ∫⁻ w, Y.indicator (fun x => ψ (γ • x)) (cj r w) ∂ν := by
          rw [← lintegral_indicator hCm]
          refine lintegral_congr fun w => ?_
          by_cases hw : w ∈ C
          · rw [indicator_of_mem hw, indicator_of_mem ((hmem w).mp hw)]
            simp only [ψ, Subgroup.smul_def, smul_eq_mul, hrw]
          · rw [indicator_of_notMem hw, indicator_of_notMem (fun h => hw ((hmem w).mpr h))]
      _ = ∫⁻ x, Y.indicator (fun x => ψ (γ • x)) x ∂ν :=
          (hcjm r).lintegral_comp ((hψ.comp (measurable_const_smul _)).indicator hYm)
      _ = ∫⁻ x in Y, ψ (γ • x) ∂ν := lintegral_indicator hYm _
  rw [tsum_congr h1, ← hY.lintegral_eq_tsum'' ψ]

include hjinj hcj hΓ hΓc hcjm hC hCm hDm hj hD in
/-- The fibre-counting identity: for every `g`, averaging the translates of `D` over `C`
gives total mass `ν C`. -/
theorem tsum_lintegral_indicator_eq (g : H) :
    ∑' l : Λ, ∫⁻ v in C, 𝟙[D] ((j v)⁻¹ * l * g) ∂ν = ν C := by
  have : Countable Γ := countable_Γ Λ j hjinj Γ hΓ
  let : MulAction Γ Λ := MulAction.compHom Λ (toΛ Λ j Γ hΓ)
  have hsmul : ∀ (γ : Γ) (l : Λ), ((γ • l : Λ) : H) = j (γ : V) * l := fun _ _ => rfl
  have hfree : ∀ (γ γ' : Γ) (l : Λ), γ • l = γ' • l → γ = γ' := by
    intro γ γ' l h
    have h' := congrArg (fun x : Λ => (x : H) * (l : H)⁻¹) h
    simp only [hsmul, mul_inv_cancel_right] at h'
    exact Subtype.ext (hjinj h')
  have hb : ∑' l : Λ, ∫⁻ w in C, 𝟙[D] (l * j w * g) ∂ν = ν C := by
    have hmeas : ∀ l : Λ, Measurable fun w => 𝟙[D] ((l : H) * j w * g) := fun l =>
      measurable_indicator_comp D hDm j hj (((measurable_const_mul _).comp hj).mul_const _)
    rw [← lintegral_tsum fun l => (hmeas l).aemeasurable]
    simp_rw [mul_assoc, tsum_indicator_mul_eq_one Λ hD]
    simp
  rw [← hb]
  refine tsum_eq_tsum_of_orbit_sums hfree
    (fun l : Λ => ∫⁻ v in C, 𝟙[D] ((j v)⁻¹ * l * g) ∂ν)
    (fun l : Λ => ∫⁻ w in C, 𝟙[D] (l * j w * g) ∂ν) fun l => ?_
  simp only [hsmul]
  rw [tsum_orbit_left Λ D hDm j hj hjinj Γ hΓ ν C hCm hC g l]
  exact (tsum_orbit_right Λ D hDm j hj hjinj Γ hΓ cj hcj hΓc ν hcjm C hCm hC g l).symm

include hjinj hcj hΓ hΓc hcjm hC hCm hDm hj hD in
/-- **Averaging over a fundamental domain of `Γ ≤ j⁻¹ Λ` preserves integrals over a
fundamental domain of `Λ`.** For a measurable left `Λ`-invariant `F ≥ 0`,
`∫_D ∫_C F (j v * g) dν(v) dμ(g) = ν C * ∫_D F dμ`. -/
theorem setLIntegral_fibreAverage {F : H → ℝ≥0∞} (hF : Measurable F)
    (hFΛ : ∀ l : Λ, ∀ x, F (l * x) = F x) :
    ∫⁻ g in D, ∫⁻ v in C, F (j v * g) ∂ν ∂μ = ν C * ∫⁻ g in D, F g ∂μ := by
  have hDfd : IsFundamentalDomain Λ D μ :=
    IsFundamentalDomain.mk' hDm.nullMeasurableSet hD
  have hind : ∀ l : Λ, Measurable fun p : H × V => 𝟙[D] ((j p.2)⁻¹ * l * p.1) := fun l =>
    measurable_indicator_comp D hDm j hj
      ((((hj.comp measurable_snd).inv).mul_const _).mul measurable_fst)
  have hB : ∀ v : V, ∫⁻ g in D, F (j v * g) ∂μ =
      ∫⁻ g in D, F g * ∑' l : Λ, 𝟙[D] ((j v)⁻¹ * l * g) ∂μ := by
    intro v
    let ψ : H → ℝ≥0∞ := fun h => 𝟙[D] ((j v)⁻¹ * h) * F h
    calc ∫⁻ g in D, F (j v * g) ∂μ = ∫⁻ g, ψ (j v * g) ∂μ := by
          rw [← lintegral_indicator hDm]
          refine lintegral_congr fun g => ?_
          simp only [ψ, inv_mul_cancel_left]
          by_cases hg : g ∈ D
          · simp [hg]
          · simp [hg]
      _ = ∫⁻ h, ψ h ∂μ := lintegral_mul_left_eq_self ψ (j v)
      _ = ∑' l : Λ, ∫⁻ g in D, ψ (l • g) ∂μ := hDfd.lintegral_eq_tsum'' ψ
      _ = ∑' l : Λ, ∫⁻ g in D, F g * 𝟙[D] ((j v)⁻¹ * l * g) ∂μ := by
          refine tsum_congr fun l => setLIntegral_congr_fun hDm fun g _ => ?_
          simp only [ψ, Subgroup.smul_def, smul_eq_mul, hFΛ, mul_assoc]
          exact mul_comm _ _
      _ = ∫⁻ g in D, ∑' l : Λ, F g * 𝟙[D] ((j v)⁻¹ * l * g) ∂μ := by
          refine (lintegral_tsum fun l => ?_).symm
          exact (hF.mul ((hind l).comp (measurable_id.prodMk measurable_const))).aemeasurable
      _ = _ := by simp_rw [ENNReal.tsum_mul_left]
  calc ∫⁻ g in D, ∫⁻ v in C, F (j v * g) ∂ν ∂μ
      = ∫⁻ v in C, ∫⁻ g in D, F (j v * g) ∂μ ∂ν :=
        lintegral_lintegral_swap
          (hF.comp ((hj.comp measurable_snd).mul measurable_fst)).aemeasurable
    _ = ∫⁻ v in C, ∫⁻ g in D, F g * ∑' l : Λ, 𝟙[D] ((j v)⁻¹ * l * g) ∂μ ∂ν :=
        lintegral_congr fun v => hB v
    _ = ∫⁻ g in D, ∫⁻ v in C, F g * ∑' l : Λ, 𝟙[D] ((j v)⁻¹ * l * g) ∂ν ∂μ :=
        (lintegral_lintegral_swap ((hF.comp measurable_fst).mul
          (Measurable.tsum fun l => hind l)).aemeasurable).symm
    _ = ∫⁻ g in D, F g * ν C ∂μ := by
        refine lintegral_congr fun g => ?_
        have hv : ∀ l : Λ, Measurable fun v : V => 𝟙[D] ((j v)⁻¹ * l * g) := fun l =>
          (hind l).comp (measurable_const.prodMk measurable_id)
        rw [lintegral_const_mul _ (Measurable.tsum hv),
          lintegral_tsum fun l => (hv l).aemeasurable,
          tsum_lintegral_indicator_eq Λ D hDm hD j hj hjinj Γ hΓ cj hcj hΓc ν hcjm C hCm hC g]
    _ = ν C * ∫⁻ g in D, F g ∂μ := by
        rw [lintegral_mul_const _ hF, mul_comm]

/-- **Statement form.** Averaging a left `Λ`-invariant function over a fundamental domain `C`
of a conjugation-stable `Γ ≤ j⁻¹ Λ` preserves its integral over a strict fundamental domain `D` of `Λ`, up to the
factor `ν C`. -/
def FundamentalDomainFibreAverageStatement : Prop :=
  ∀ {H : Type u} [Group H] [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableInv H]
    {V : Type v} [Group V] [MeasurableSpace V] [MeasurableMul₂ V] [MeasurableInv V]
    (μ : Measure H) [μ.IsMulLeftInvariant] [SFinite μ]
    (Λ : Subgroup H) [Countable Λ] (D : Set H), MeasurableSet D →
    (∀ x : H, ∃! l : Λ, (l : H) * x ∈ D) →
    ∀ (j : V →* H), Measurable j → Injective j →
    ∀ (Γ : Subgroup V), (∀ w ∈ Γ, j w ∈ Λ) →
    ∀ (cj : Λ → V → V), (∀ l w, j (cj l w) = l * j w * (l : H)⁻¹) →
    (∀ (l : Λ) (w : V), w ∈ Γ → cj l w ∈ Γ) →
    ∀ (ν : Measure V) [ν.IsMulLeftInvariant] [ν.IsInvInvariant] [SFinite ν],
    (∀ l, MeasurePreserving (cj l) ν ν) →
    ∀ (C : Set V), MeasurableSet C → IsFundamentalDomain Γ C ν →
    ∀ {F : H → ℝ≥0∞}, Measurable F → (∀ l : Λ, ∀ x, F (l * x) = F x) →
      ∫⁻ g in D, ∫⁻ w in C, F (j w * g) ∂ν ∂μ = ν C * ∫⁻ g in D, F g ∂μ

/-- Proof of `FundamentalDomainFibreAverageStatement`. -/
theorem fundamentalDomainFibreAverage : FundamentalDomainFibreAverageStatement.{u, v} := by
  intro H _ _ _ _ V _ _ _ _ μ _ _ Λ _ D hDm hD j hj hjinj Γ hΓ cj hcj hΓc ν _ _ _ hcjm C hCm hC
    F hF hFΛ
  exact setLIntegral_fibreAverage μ Λ D hDm hD j hj hjinj Γ hΓ cj hcj hΓc ν hcjm C hCm hC hF hFΛ

end Langlands.Analysis.FibreAverage
