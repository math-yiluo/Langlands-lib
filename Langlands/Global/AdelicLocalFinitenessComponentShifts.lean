import Langlands.Global.AdelicSplitComponentL2Translation

/-! # Translated Harish-Chandra components for points normalizing `U_J(𝔸)`

The operators "translate by `b` after the Harish-Chandra component" of
`AdelicSplitComponentL2Translation`, for any point `b ∈ G(𝔸)` that commutes with `L_J(𝔸)` and
normalizes `U_J(𝔸)`, not only for images of points of the split component. Powers of such points
have the same properties.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Opposite
open scoped CategoryTheory.MonObj ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme AdelicSubgroupPoints Langlands.Analysis.FibreAverage
open Langlands.Global.HarishChandraDecomposition Langlands.Global.StandardConstantTerm
open Classical

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

/-- Weighted `L²` bound for translation by a point `b` commuting with `L_J(𝔸)` and normalizing
`U_J(𝔸)`, on functions and weights invariant under `P₀(F)` and `U_J(𝔸)`, when
`W(g) ≤ κ W(b g)`. -/
theorem setLIntegral_enorm_sq_mul_left_le {J : Set (characterLattice 𝓕.T)}
    (hJ : J ⊆ simpleRelativeRoots 𝓕.i 𝓕.ν) (b : AdelicGroupPoints F G)
    (hlevi : ∀ x ∈ adelicPoints F G (standardLevi 𝓕.i 𝓕.ν J), b * x = x * b)
    (hb : ∀ w ∈ adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν J),
      b * w * b⁻¹ ∈ adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν J))
    (hb' : ∀ w ∈ adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν J),
      b⁻¹ * w * b ∈ adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν J))
    {f : AdelicGroupPoints F G → ℂ} (hf : Measurable f)
    (hfΛ : ∀ l ∈ minimalParabolicImage F G 𝓕.i 𝓕.ν, ∀ x, f (l * x) = f x)
    (hfU : ∀ w ∈ adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν J), ∀ x, f (w * x) = f x)
    {W : AdelicGroupPoints F G → ℝ≥0∞} (hW : Measurable W)
    (hWΛ : ∀ l ∈ minimalParabolicImage F G 𝓕.i 𝓕.ν, ∀ x, W (l * x) = W x)
    (hWU : ∀ w ∈ adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν J), ∀ x, W (w * x) = W x)
    {κ : ℝ≥0∞} (hκ : ∀ g, W g ≤ κ * W (b * g)) :
    haveI hcl := isClosed_adelicPoints_standardUnipotent F G 𝓕.i 𝓕.ν J
    haveI : LocallyCompactSpace (adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν J)) :=
      hcl.locallyCompactSpace
    ∫⁻ g in LeftCosetSpace.fundamentalDomain (minimalParabolicImage F G 𝓕.i 𝓕.ν)
        (isDiscrete_minimalParabolicImage F G 𝓕.i 𝓕.ν),
        ‖f (b * g)‖ₑ ^ 2 * W g ∂Measure.haar ≤
      κ * (mulEquivHaarChar (conjPoints F G b hb hb') : ℝ≥0∞) *
        ∫⁻ g in LeftCosetSpace.fundamentalDomain (minimalParabolicImage F G 𝓕.i 𝓕.ν)
          (isDiscrete_minimalParabolicImage F G 𝓕.i 𝓕.ν), ‖f g‖ₑ ^ 2 * W g ∂Measure.haar := by
  let hcl := isClosed_adelicPoints_standardUnipotent F G 𝓕.i 𝓕.ν J
  let : LocallyCompactSpace (adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν J)) :=
    hcl.locallyCompactSpace
  let φ : AdelicGroupPoints F G → ℝ≥0∞ := fun g => ‖f g‖ₑ ^ 2 * W g
  have hφ : Measurable φ := (hf.enorm.pow_const 2).mul hW
  have hφΛ : ∀ l ∈ minimalParabolicImage F G 𝓕.i 𝓕.ν, ∀ x, φ (l * x) = φ x :=
    fun l hl x => by simp only [φ, hfΛ l hl x, hWΛ l hl x]
  have hφU : ∀ w ∈ adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν J), ∀ x, φ (w * x) = φ x :=
    fun w hw x => by simp only [φ, hfU w hw x, hWU w hw x]
  have key := setLIntegral_mul_left_eq F G 𝓕.i 𝓕.ν (hG := 𝓕.connectedReductive)
    (hi := 𝓕.maximalSplit) (hν := 𝓕.generic) hJ b hlevi hb hb' hφ hφΛ hφU
  calc ∫⁻ g in LeftCosetSpace.fundamentalDomain (minimalParabolicImage F G 𝓕.i 𝓕.ν)
          (isDiscrete_minimalParabolicImage F G 𝓕.i 𝓕.ν), ‖f (b * g)‖ₑ ^ 2 * W g ∂Measure.haar
      ≤ ∫⁻ g in LeftCosetSpace.fundamentalDomain (minimalParabolicImage F G 𝓕.i 𝓕.ν)
          (isDiscrete_minimalParabolicImage F G 𝓕.i 𝓕.ν), κ * φ (b * g) ∂Measure.haar := by
        refine lintegral_mono fun g => ?_
        calc ‖f (b * g)‖ₑ ^ 2 * W g ≤ ‖f (b * g)‖ₑ ^ 2 * (κ * W (b * g)) := by
              gcongr
              exact hκ g
          _ = κ * φ (b * g) := by simp only [φ]; ring
    _ = κ * ∫⁻ g in LeftCosetSpace.fundamentalDomain (minimalParabolicImage F G 𝓕.i 𝓕.ν)
          (isDiscrete_minimalParabolicImage F G 𝓕.i 𝓕.ν), φ (b * g) ∂Measure.haar :=
        lintegral_const_mul _ (hφ.comp (measurable_const_mul b))
    _ = _ := by rw [key, mul_assoc]

/-- **Translated Harish-Chandra components for a normalizing point.** Let `W` be a measurable
weight, left invariant under `P₀(F)` and under `U_K(𝔸)` for every `K ⊆ Δ₀`. For contractions
`T S` of `L²(μ_W)` computing the folded constant terms and a point `b` commuting with `L_J(𝔸)`
and normalizing `U_J(𝔸)`, `J = P ∩ Δ₀`, with `W(g) ≤ κ W(b g)` and `κ < ∞`, "translate by `b`
after the component `∑_{S ⊆ P} (−1)^{|P ∖ S|} T S`" is a continuous linear operator of norm at
most `(κ c(b))^{1/2} 2^{|P|}`, computed on every measurable representative. -/
theorem translatedComponent_of_point (W : AdelicGroupPoints F G → ℝ≥0∞) (hW : Measurable W)
    (hWΛ : ∀ l ∈ minimalParabolicImage F G 𝓕.i 𝓕.ν, ∀ x, W (l * x) = W x)
    (hWU : ∀ J ⊆ simpleRelativeRoots 𝓕.i 𝓕.ν,
      ∀ w ∈ adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν J), ∀ x, W (w * x) = W x)
    (T : Finset (characterLattice 𝓕.T) →
        (Lp ℂ 2 (𝓕.weightedHaar W) →L[ℂ] Lp ℂ 2 (𝓕.weightedHaar W)))
    (hT1 : ∀ S, ‖T S‖ ≤ 1)
    (hT2 : ∀ S (Fn : Lp ℂ 2 (𝓕.weightedHaar W)) {f : AdelicGroupPoints F G → ℂ}, Measurable f →
        f =ᵐ[𝓕.weightedHaar W] Fn → T S Fn =ᵐ[𝓕.weightedHaar W] 𝓕.componentFoldCT S f)
    (P : Finset (characterLattice 𝓕.T)) (b : AdelicGroupPoints F G)
    (hlevi : ∀ x ∈ adelicPoints F G (standardLevi 𝓕.i 𝓕.ν (𝓕.finsetIndex P).1), b * x = x * b)
    (hb : ∀ w ∈ adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex P).1),
      b * w * b⁻¹ ∈ adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex P).1))
    (hb' : ∀ w ∈ adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex P).1),
      b⁻¹ * w * b ∈ adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex P).1))
    {κ : ℝ≥0∞} (hκtop : κ ≠ ∞) (hκ : ∀ g, W g ≤ κ * W (b * g)) :
    haveI hcl := isClosed_adelicPoints_standardUnipotent F G 𝓕.i 𝓕.ν (𝓕.finsetIndex P).1
    haveI : LocallyCompactSpace (adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex P).1)) :=
      hcl.locallyCompactSpace
    ∃ L : Lp ℂ 2 (𝓕.weightedHaar W) →L[ℂ] Lp ℂ 2 (𝓕.weightedHaar W),
      ‖L‖ ≤ ((κ * (mulEquivHaarChar (conjPoints F G b hb hb') : ℝ≥0∞)) ^ (1 / 2 : ℝ)).toReal *
        2 ^ P.card ∧
      ∀ (Fn : Lp ℂ 2 (𝓕.weightedHaar W)) {f : AdelicGroupPoints F G → ℂ}, Measurable f →
        f =ᵐ[𝓕.weightedHaar W] Fn →
        L Fn =ᵐ[𝓕.weightedHaar W] fun g => alternatingSum (fun S => 𝓕.componentFoldCT S f) P
          (b * g) := by
  let hcl := isClosed_adelicPoints_standardUnipotent F G 𝓕.i 𝓕.ν (𝓕.finsetIndex P).1
  let : LocallyCompactSpace (adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex P).1)) :=
    hcl.locallyCompactSpace
  let Pinv : (AdelicGroupPoints F G → ℂ) → Prop := fun h =>
    (∀ l ∈ minimalParabolicImage F G 𝓕.i 𝓕.ν, ∀ x, h (l * x) = h x) ∧
    (∀ w ∈ adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex P).1), ∀ x,
      h (w * x) = h x)
  have hsub : ∀ f g, Pinv f → Pinv g → Pinv (f - g) := fun f g hf hg =>
    ⟨fun l hl x => by simp only [Pi.sub_apply, hf.1 l hl x, hg.1 l hl x],
     fun w hw x => by simp only [Pi.sub_apply, hf.2 w hw x, hg.2 w hw x]⟩
  have hadd : ∀ f g, Pinv f → Pinv g → Pinv (f + g) := fun f g hf hg =>
    ⟨fun l hl x => by simp only [Pi.add_apply, hf.1 l hl x, hg.1 l hl x],
     fun w hw x => by simp only [Pi.add_apply, hf.2 w hw x, hg.2 w hw x]⟩
  have hsmul : ∀ (c : ℂ) f, Pinv f → Pinv (c • f) := fun c f hf =>
    ⟨fun l hl x => by simp only [Pi.smul_apply, hf.1 l hl x],
     fun w hw x => by simp only [Pi.smul_apply, hf.2 w hw x]⟩
  let c : ℝ≥0∞ := (mulEquivHaarChar (conjPoints F G b hb hb') : ℝ≥0∞)
  have hKtop : κ * c ≠ ∞ := ENNReal.mul_ne_top hκtop (by simp only [c]; exact ENNReal.coe_ne_top)
  have hbound : ∀ f, Measurable f → Pinv f →
      ∫⁻ g in LeftCosetSpace.fundamentalDomain (minimalParabolicImage F G 𝓕.i 𝓕.ν)
          (isDiscrete_minimalParabolicImage F G 𝓕.i 𝓕.ν), ‖f (b * g)‖ₑ ^ 2 * W g ∂Measure.haar ≤
        κ * c * ∫⁻ g in LeftCosetSpace.fundamentalDomain (minimalParabolicImage F G 𝓕.i 𝓕.ν)
          (isDiscrete_minimalParabolicImage F G 𝓕.i 𝓕.ν), ‖f g‖ₑ ^ 2 * W g ∂Measure.haar :=
    fun f hf hP => 𝓕.setLIntegral_enorm_sq_mul_left_le (𝓕.finsetIndex P).2 b hlevi hb hb' hf hP.1
      hP.2 hW hWΛ (hWU (𝓕.finsetIndex P).1 (𝓕.finsetIndex P).2) hκ
  have hrep : ∀ (Fn : Lp ℂ 2 (𝓕.weightedHaar W)) {f : AdelicGroupPoints F G → ℂ}, Measurable f →
      f =ᵐ[𝓕.weightedHaar W] Fn →
      Measurable (alternatingSum (fun S => 𝓕.componentFoldCT S f) P) ∧
      Pinv (alternatingSum (fun S => 𝓕.componentFoldCT S f) P) ∧
      alternatingSum (fun S => 𝓕.componentFoldCT S f) P =ᵐ[𝓕.weightedHaar W]
        alternatingSum T P Fn := by
    intro Fn f hf hfF
    refine ⟨?_, ⟨fun l hl x => ?_, fun w hw x => ?_⟩, ?_⟩
    · unfold alternatingSum
      have h := Finset.measurable_sum P.powerset
        (f := fun S => ((-1 : ℂ) ^ (P \ S).card) • 𝓕.componentFoldCT S f)
        fun S _ => (𝓕.measurable_componentFoldCT S hf).const_smul _
      convert h using 1
      funext x
      simp [Finset.sum_apply]
    · unfold alternatingSum
      simp only [Finset.sum_apply, Pi.smul_apply]
      exact Finset.sum_congr rfl fun S hS => by
        rw [(𝓕.componentFoldCT_invariant (Finset.mem_powerset.mp hS) f).1 l hl x]
    · unfold alternatingSum
      simp only [Finset.sum_apply, Pi.smul_apply]
      exact Finset.sum_congr rfl fun S hS => by
        rw [(𝓕.componentFoldCT_invariant (Finset.mem_powerset.mp hS) f).2 w hw x]
    · exact (alternatingSum_apply_ae T Fn (fun S => 𝓕.componentFoldCT S f)
        (fun S => hT2 S Fn hf hfF) P).symm
  have hTrep : ∀ Fn, ∃ h : AdelicGroupPoints F G → ℂ, Measurable h ∧ Pinv h ∧
      h =ᵐ[𝓕.weightedHaar W] alternatingSum T P Fn := fun Fn => by
    have hm := Lp.aestronglyMeasurable Fn
    obtain ⟨h1, h2, h3⟩ := hrep Fn hm.stronglyMeasurable_mk.measurable hm.ae_eq_mk.symm
    exact ⟨_, h1, h2, h3⟩
  refine ⟨Langlands.Analysis.InvariantTranslation.translateCLM b Pinv (κ * c) hW hsub hadd hsmul
    hKtop hbound (alternatingSum T P) hTrep, ?_, fun Fn f hf hfF => ?_⟩
  · refine (Langlands.Analysis.InvariantTranslation.norm_translateCLM_le _ Pinv (κ * c) hW hsub
      hadd hsmul hKtop hbound (alternatingSum T P) hTrep).trans ?_
    exact mul_le_mul_of_nonneg_left (norm_alternatingSum_le T hT1 P) ENNReal.toReal_nonneg
  · obtain ⟨h1, h2, h3⟩ := hrep Fn hf hfF
    exact Langlands.Analysis.InvariantTranslation.translateCLM_ae b Pinv (κ * c) hW hsub hadd
      hsmul hKtop hbound (alternatingSum T P) hTrep Fn h1 h2 h3

/-- `b ∈ G(𝔸)` commutes with every point of `L_J(𝔸)` and normalizes `U_J(𝔸)` in both
directions. -/
def IsLeviNormalizingPoint (J : Set (characterLattice 𝓕.T)) (b : AdelicGroupPoints F G) : Prop :=
  (∀ x ∈ adelicPoints F G (standardLevi 𝓕.i 𝓕.ν J), b * x = x * b) ∧
    (∀ w ∈ adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν J),
      b * w * b⁻¹ ∈ adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν J)) ∧
    (∀ w ∈ adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν J),
      b⁻¹ * w * b ∈ adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν J))

variable {𝓕} in
/-- The powers `b^q`, `q ∈ ℕ`, of a point commuting with `L_J(𝔸)` and normalizing `U_J(𝔸)`
have the same properties. -/
theorem IsLeviNormalizingPoint.pow {J : Set (characterLattice 𝓕.T)} {b : AdelicGroupPoints F G}
    (hb : 𝓕.IsLeviNormalizingPoint J b) (q : ℕ) : 𝓕.IsLeviNormalizingPoint J (b ^ q) := by
  obtain ⟨hlevi, hb, hb'⟩ := hb
  induction q with
  | zero => simp [IsLeviNormalizingPoint]
  | succ q ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨fun x hx => ?_, fun w hw => ?_, fun w hw => ?_⟩
    · rw [pow_succ, mul_assoc, hlevi x hx, ← mul_assoc, h1 x hx, mul_assoc]
    · have := h2 _ (hb w hw)
      rw [pow_succ, mul_inv_rev]
      simpa only [mul_assoc] using this
    · have := hb' _ (h3 w hw)
      rw [pow_succ, mul_inv_rev]
      simpa only [mul_assoc] using this

/-- Iterating the forward comparison `W(g) ≤ κ W(b g)` gives `W(g) ≤ κ^q W(b^q g)` for
`q ∈ ℕ`. -/
theorem weight_le_pow {W : AdelicGroupPoints F G → ℝ≥0∞} {b : AdelicGroupPoints F G} {κ : ℝ≥0∞}
    (hκ : ∀ g, W g ≤ κ * W (b * g)) (q : ℕ) (g : AdelicGroupPoints F G) :
    W g ≤ κ ^ q * W (b ^ q * g) := by
  induction q generalizing g with
  | zero => simp
  | succ q ih =>
    calc W g ≤ κ ^ q * W (b ^ q * g) := ih g
      _ ≤ κ ^ q * (κ * W (b * (b ^ q * g))) := by gcongr; exact hκ _
      _ = κ ^ (q + 1) * W (b ^ (q + 1) * g) := by
        rw [← mul_assoc, ← pow_succ, ← mul_assoc, ← pow_succ']

/-- The translated components by the powers `b^q`, `q ∈ ℕ`, of a normalizing point, for a
measurable weight `W` left invariant under `P₀(F)` and every `U_K(𝔸)`, `K ⊆ Δ₀`, with the forward
comparison `W(g) ≤ κ W(b g)`, `κ < ∞`. Negative powers are not covered: the forward comparison
does not bound the pullback by `b⁻¹` on weighted `L²` classes. -/
theorem exists_translatedComponent_pow (W : AdelicGroupPoints F G → ℝ≥0∞) (hW : Measurable W)
    (hWΛ : ∀ l ∈ minimalParabolicImage F G 𝓕.i 𝓕.ν, ∀ x, W (l * x) = W x)
    (hWU : ∀ J ⊆ simpleRelativeRoots 𝓕.i 𝓕.ν,
      ∀ w ∈ adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν J), ∀ x, W (w * x) = W x)
    (T : Finset (characterLattice 𝓕.T) →
        (Lp ℂ 2 (𝓕.weightedHaar W) →L[ℂ] Lp ℂ 2 (𝓕.weightedHaar W)))
    (hT1 : ∀ S, ‖T S‖ ≤ 1)
    (hT2 : ∀ S (Fn : Lp ℂ 2 (𝓕.weightedHaar W)) {f : AdelicGroupPoints F G → ℂ}, Measurable f →
        f =ᵐ[𝓕.weightedHaar W] Fn → T S Fn =ᵐ[𝓕.weightedHaar W] 𝓕.componentFoldCT S f)
    (P : Finset (characterLattice 𝓕.T)) (b : AdelicGroupPoints F G)
    (hlevi : ∀ x ∈ adelicPoints F G (standardLevi 𝓕.i 𝓕.ν (𝓕.finsetIndex P).1), b * x = x * b)
    (hb : ∀ w ∈ adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex P).1),
      b * w * b⁻¹ ∈ adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex P).1))
    (hb' : ∀ w ∈ adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex P).1),
      b⁻¹ * w * b ∈ adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex P).1))
    {κ : ℝ≥0∞} (hκtop : κ ≠ ∞) (hκ : ∀ g, W g ≤ κ * W (b * g)) :
    ∃ L : ℕ → (Lp ℂ 2 (𝓕.weightedHaar W) →L[ℂ] Lp ℂ 2 (𝓕.weightedHaar W)),
      ∀ q (Fn : Lp ℂ 2 (𝓕.weightedHaar W)) {f : AdelicGroupPoints F G → ℂ}, Measurable f →
        f =ᵐ[𝓕.weightedHaar W] Fn →
        L q Fn =ᵐ[𝓕.weightedHaar W] fun g => alternatingSum (fun S => 𝓕.componentFoldCT S f) P
          (b ^ q * g) := by
  have h (q : ℕ) := IsLeviNormalizingPoint.pow (𝓕 := 𝓕) ⟨hlevi, hb, hb'⟩ q
  choose L _ hL using fun q => 𝓕.translatedComponent_of_point W hW hWΛ hWU T hT1 hT2 P (b ^ q)
    (h q).1 (h q).2.1 (h q).2.2 (ENNReal.pow_ne_top hκtop) (weight_le_pow hκ q)
  exact ⟨L, hL⟩

end Langlands.Global.StandardParabolicFamily
