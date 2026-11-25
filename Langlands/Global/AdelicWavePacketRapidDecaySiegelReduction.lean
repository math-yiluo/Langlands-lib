import Langlands.Global.AdelicWavePacketCompletenessReduction
import Langlands.Global.AdelicSiegelMeasureReduction
import Langlands.Global.AdelicRepresentationHeightPropernessProof

/-! # Rapid decay of wave packets from Siegel-set estimates

Delorme 2023, Proposition 5.4 with (2.5), (2.10) and Lemma 2.1, split into two propositions on
the Siegel sets `z · Ω_N Ω_M A_{T₀}(t) K · Ω` of `G(𝔸)`, with `z ∈ A_G`:

* `WavePacketSiegelDecayStatement` (Delorme, (5.2) in the proof of Proposition 5.4): every wave
  packet `Θ` is continuous and left `G(F)`-invariant, and on every Siegel set
  `|Θ(x)| ≤ B_n δ(a)^{1/2} σ(x)^{-n}` for every `n`, where `a` is the torus coordinate of `x`,
  `δ(a) = ∏_{β > 0} |β(a)|^{m_β}` and `σ(x) = 1 + log max(1, ‖x‖)`;
* `SiegelDominatedIntegrabilityStatement` (derived from Lapid 2013, §2, (2), (3) and property 5,
  equation (5), quoted as Delorme (2.5)): there are a Siegel set and `d` such that every
  measurable left `G(F)`-invariant function `f ≥ 0` with `f(x) ≤ δ(a) σ(x)^{-d}` for every point
  `x` of the Siegel set and every admissible torus coordinate `a` of `x` has finite integral
  over `[G]`.

The theorem `wavePacketRapidDecay_of_siegel` derives `WavePacketRapidDecayStatement` from the
two. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  AdelicSiegelFactors

section Definitions

variable (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- The logarithmic height `σ(x) = 1 + log max(1, ‖x‖_ρ)` on `G(𝔸)` (Delorme 2023, §2, after
(2.7)), for the Mœglin–Waldspurger height `‖x‖_ρ = RepresentationGrowth.adelicSourceNorm` of
the matrix embedding `rho`. `rationalLogHeight` is its infimum over the coset `G(F) x`. -/
def adelicLogHeight {N : ℕ} (rho : MatrixRepresentation G (Fin N))
    (x : AdelicGroupPoints F G) : ℝ :=
  1 + Real.log (max 1 (RepresentationGrowth.adelicSourceNorm F G rho x))

variable (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (ν : cocharacterLattice T) (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T)

/-- The modulus `δ_{P₀}(a) = ∏_{β ∈ Φ⁺} |β(a)|^{m_β} = e^{2ρ₀(H₀(a))}` of the standard minimal
parabolic of `(T, i, ν)` at a point `a` of the positive torus `A_{T₀}`, where `m_β` is the
dimension of the `β`-weight space of `T` on the Lie algebra of `G`. It is the right side of the
published `PositiveTorusUnipotentModulusStatement`. -/
def siegelModulus (a : PositiveRealTorus.intrinsicSubgroup F T₀) : ℝ :=
  ∏ᶠ (β : characterLattice T) (_ : β ∈ positiveRelativeRoots i ν),
    ((PositiveRealTorus.normCharacter F T₀ (j ≫ β) a : ℝ≥0) : ℝ) ^
      Module.finrank F (weightSpace i β)

/-- `x` lies in the Siegel set `A_G · Ω_N Ω_M A_{T₀}(t) K · Ω` with torus coordinate `a`:
`x = z · n m a k · w` with `z ∈ A_G` (`RestrictionSplitCentre.canonicalSubgroup`), `n ∈ Ω_N`,
`m ∈ Ω_M`, `a` in the weak simple-root chamber `|β(a)| ≥ t`, `k` in the compact subgroup of
`C`, and `w ∈ Ω`. The middle factor `n m a k` is a point of the published
`weakSiegelProduct` (`mem_productSet_iff`). -/
def IsSiegelPoint
    (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
    (t : ℝ≥0ˣ) (Ω : Set (AdelicGroupPoints F G))
    (a : PositiveRealTorus.intrinsicSubgroup F T₀) (x : AdelicGroupPoints F G) : Prop :=
  ∃ z ∈ RestrictionSplitCentre.canonicalSubgroup F G, ∃ n ∈ C.omegaN, ∃ m ∈ C.omegaM,
    a ∈ PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t ∧
      ∃ k ∈ C.compactSubgroup, ∃ w ∈ Ω,
        x = z * (map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) n *
          map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m *
            positiveMap F G T i T₀ j a * k) * w

end Definitions

/-- **Siegel-set decay of wave packets** (Delorme 2023, (5.2) in the proof of Proposition 5.4,
with Proposition 4.1 and Lemma 5.3). For the data of `WavePacketRapidDecayStatement`, every
wave packet `Θ` of `IsWavePacket` is continuous and left `G(F)`-invariant, and for every
algebraic Siegel setup `(T, i, ν, T₀, j)`, compact factors `C` (with any compact subgroup),
threshold `t`, compact set `Ω` and `n : ℕ` there is `B` such that
`‖Θ(x)‖ ≤ B δ(a)^{1/2} / σ(x)^n` for every point `x` of the Siegel set
`A_G · Ω_N Ω_M A_{T₀}(t) K · Ω` with torus coordinate `a`. -/
def WavePacketSiegelDecayStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
      (∃ (P₀ : GroupScheme (Spec (CommRingCat.of F))) (_ : IsAffine P₀.X.left) (p₀ : P₀ ⟶ G)
        (_ : IsClosedImmersion p₀.hom.hom.left),
        IsMinimalParabolicSubgroup p₀ ∧ IsIwasawaCompact p₀ K) →
    ∀ Θ : AdelicGroupPoints F G → ℂ, IsWavePacket F G K rho hsmooth hcalc Θ →
      Continuous Θ ∧
      (∀ q ∈ rationalSubgroup F G, ∀ g : AdelicGroupPoints F G, Θ (q * g) = Θ g) ∧
      ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
        (ν : cocharacterLattice T) (T₀ : CommGroupScheme (Spec (CommRingCat.of F)))
        (j : T₀ ⟶ T), IsSiegelAlgebraicSetup F G T i ν T₀ j →
      ∀ (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
        (t : ℝ≥0ˣ) (Ω : Set (AdelicGroupPoints F G)), IsCompact Ω →
      ∀ n : ℕ, ∃ B : ℝ, ∀ (a : PositiveRealTorus.intrinsicSubgroup F T₀)
        (x : AdelicGroupPoints F G), IsSiegelPoint F G T i ν T₀ j C t Ω a x →
          ‖Θ x‖ ≤ B * Real.sqrt (siegelModulus F G T i ν T₀ j a) /
            adelicLogHeight F G rho x ^ n

/-- **Integrability of Siegel-dominated functions on `[G]`** (derived from Lapid 2013, §2, (2),
(3) and (5), quoted as Delorme 2023, (2.5)). For every number field
`F`, connected reductive `G` and closed matrix embedding `rho`, there are an algebraic Siegel
setup, compact factors `C`, a threshold `t`, a compact set `Ω` and `d : ℕ` such that every
measurable left `G(F)`-invariant `f : G(𝔸) → [0, ∞]` with `f(x) ≤ δ(a) / σ(x)^d` at every point `x` of the
Siegel set `A_G · Ω_N Ω_M A_{T₀}(t) K · Ω` with torus coordinate `a` has finite integral over
`[G] = G(F) \ G(𝔸)` for the quotient `μG` of Haar measure by counting measure. -/
def SiegelDominatedIntegrabilityStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ {N : ℕ} (rho : MatrixRepresentation G (Fin N)), IsClosedSubgroup rho →
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
      (ν : cocharacterLattice T) (T₀ : CommGroupScheme (Spec (CommRingCat.of F)))
      (j : T₀ ⟶ T), IsSiegelAlgebraicSetup F G T i ν T₀ j ∧
    ∃ (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
      (t : ℝ≥0ˣ) (Ω : Set (AdelicGroupPoints F G)) (d : ℕ), IsCompact Ω ∧
      ∀ f : AdelicGroupPoints F G → ℝ≥0∞, Measurable f →
        (∀ q ∈ rationalSubgroup F G, ∀ g : AdelicGroupPoints F G, f (q * g) = f g) →
        (∀ (a : PositiveRealTorus.intrinsicSubgroup F T₀) (x : AdelicGroupPoints F G),
          IsSiegelPoint F G T i ν T₀ j C t Ω a x →
            f x ≤ ENNReal.ofReal
              (siegelModulus F G T i ν T₀ j a / adelicLogHeight F G rho x ^ d)) →
        ∫⁻ y : RationalQuotient F G, f y.out ∂(LeftCosetSpace.discreteQuotientMeasure
          (rationalSubgroup F G) (isDiscrete_rationalSubgroup F G) Measure.haar) < ∞

section Proof

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- The chosen representative of the coset of `g` is a rational left translate of `g`. -/
theorem out_mk_eq_rational_mul (g : AdelicGroupPoints F G) :
    ∃ q ∈ rationalSubgroup F G,
      (LeftCosetSpace.mk (rationalSubgroup F G) g).out = q * g := by
  have h : LeftCosetSpace.mk (rationalSubgroup F G)
      (LeftCosetSpace.mk (rationalSubgroup F G) g).out =
        LeftCosetSpace.mk (rationalSubgroup F G) g := Quotient.out_eq _
  rw [LeftCosetSpace.mk_eq_mk_iff] at h
  exact ⟨(g * (LeftCosetSpace.mk (rationalSubgroup F G) g).out⁻¹)⁻¹,
    (rationalSubgroup F G).inv_mem h, by group⟩

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- The Mœglin–Waldspurger height of a matrix embedding is continuous on `G(𝔸)`. -/
theorem continuous_adelicSourceNorm {N : ℕ} (rho : MatrixRepresentation G (Fin N)) :
    Continuous (RepresentationGrowth.adelicSourceNorm F G rho) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    refine continuous_of_const fun x y => ?_
    simp only [RepresentationGrowth.adelicSourceNorm]
    congr 1
    exact Subsingleton.elim _ _
  · have hpos : (0 : ℝ) < (N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult) := by
      have : (0 : ℝ) < N := by exact_mod_cast hN
      positivity
    have heq : RepresentationGrowth.adelicSourceNorm F G rho = fun g =>
        ((N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult))⁻¹ *
          RepresentationGrowth.adelicHeight F G rho g := by
      funext g
      rw [RepresentationGrowth.adelicHeight_eq_scalar_mul_sourceNorm,
        inv_mul_cancel_left₀ hpos.ne']
    rw [heq]
    exact continuous_const.mul (RepresentationGrowth.continuous_adelicHeight F G rho hN)

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
theorem one_le_adelicLogHeight {N : ℕ} (rho : MatrixRepresentation G (Fin N))
    (x : AdelicGroupPoints F G) : 1 ≤ adelicLogHeight F G rho x := by
  have := Real.log_nonneg (le_max_left 1 (RepresentationGrowth.adelicSourceNorm F G rho x))
  unfold adelicLogHeight
  linarith

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
theorem one_le_rationalLogHeight {N : ℕ} (rho : MatrixRepresentation G (Fin N))
    (y : RationalQuotient F G) : 1 ≤ rationalLogHeight F G rho y := by
  unfold rationalLogHeight
  have := Real.log_nonneg (le_max_left 1 (⨅ q : rationalSubgroup F G,
    RepresentationGrowth.adelicSourceNorm F G rho ((q : AdelicGroupPoints F G) * y.out)))
  linarith

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- `σ_{[G]}(G(F) x) ≤ σ(x)`: the infimum over the coset is at most the value at `x`. -/
theorem rationalLogHeight_mk_le {N : ℕ} (rho : MatrixRepresentation G (Fin N))
    (x : AdelicGroupPoints F G) :
    rationalLogHeight F G rho (LeftCosetSpace.mk (rationalSubgroup F G) x) ≤
      adelicLogHeight F G rho x := by
  obtain ⟨q, hq, hout⟩ := out_mk_eq_rational_mul (F := F) (G := G) x
  unfold rationalLogHeight adelicLogHeight
  rw [hout]
  set S := ⨅ r : rationalSubgroup F G,
    RepresentationGrowth.adelicSourceNorm F G rho ((r : AdelicGroupPoints F G) * (q * x))
  have hmax : max 1 S ≤ max 1 (RepresentationGrowth.adelicSourceNorm F G rho x) := by
    by_cases hb : BddBelow (Set.range fun r : rationalSubgroup F G =>
        RepresentationGrowth.adelicSourceNorm F G rho ((r : AdelicGroupPoints F G) * (q * x)))
    · refine max_le_max le_rfl ((ciInf_le hb ⟨q⁻¹, (rationalSubgroup F G).inv_mem hq⟩).trans_eq ?_)
      change RepresentationGrowth.adelicSourceNorm F G rho (q⁻¹ * (q * x)) = _
      rw [inv_mul_cancel_left]
    · have hS : S = 0 := Real.iInf_of_not_bddBelow hb
      rw [hS]
      exact max_le (le_max_left _ _) (zero_le_one.trans (le_max_left _ _))
  have h1 : 0 < max 1 S := lt_max_of_lt_left one_pos
  linarith [Real.log_le_log h1 hmax]

omit [IsAffineHom G.X.hom] in
/-- `σ_{[G]}` is measurable on `[G]`: its pullback to `G(𝔸)` is `1 + log max(1, inf_q ‖q g‖)`,
a countable infimum of continuous functions. -/
theorem measurable_rationalLogHeight {N : ℕ} (rho : MatrixRepresentation G (Fin N)) :
    Measurable (rationalLogHeight F G rho) := by
  have : Countable (rationalSubgroup F G) :=
    LeftCosetSpace.countable_of_isDiscrete _ (isDiscrete_rationalSubgroup F G)
  have hfun : ∀ g : AdelicGroupPoints F G,
      rationalLogHeight F G rho (LeftCosetSpace.mk (rationalSubgroup F G) g) =
        1 + Real.log (max 1 (⨅ r : rationalSubgroup F G,
          RepresentationGrowth.adelicSourceNorm F G rho ((r : AdelicGroupPoints F G) * g))) := by
    intro g
    obtain ⟨q, hq, hout⟩ := out_mk_eq_rational_mul (F := F) (G := G) g
    have hinf : (⨅ r : rationalSubgroup F G, RepresentationGrowth.adelicSourceNorm F G rho
        ((r : AdelicGroupPoints F G) * (q * g))) = ⨅ r : rationalSubgroup F G,
          RepresentationGrowth.adelicSourceNorm F G rho ((r : AdelicGroupPoints F G) * g) := by
      refine (Equiv.mulRight (⟨q, hq⟩ : rationalSubgroup F G)).iInf_congr fun r => ?_
      simp only [Equiv.coe_mulRight, Subgroup.coe_mul, mul_assoc]
    unfold rationalLogHeight
    rw [hout, hinf]
  have hm : Measurable (fun g : AdelicGroupPoints F G => 1 + Real.log (max 1
      (⨅ r : rationalSubgroup F G,
        RepresentationGrowth.adelicSourceNorm F G rho ((r : AdelicGroupPoints F G) * g)))) := by
    have hinf : Measurable (fun g : AdelicGroupPoints F G => ⨅ r : rationalSubgroup F G,
        RepresentationGrowth.adelicSourceNorm F G rho ((r : AdelicGroupPoints F G) * g)) :=
      Measurable.iInf fun r =>
        ((continuous_adelicSourceNorm rho).comp (continuous_const.mul continuous_id)).measurable
    exact measurable_const.add (measurable_const.max hinf).log
  have hcomp : Measurable ((rationalLogHeight F G rho) ∘
      (LeftCosetSpace.mk (rationalSubgroup F G))) := by
    have : (rationalLogHeight F G rho) ∘ (LeftCosetSpace.mk (rationalSubgroup F G)) =
        fun g : AdelicGroupPoints F G => 1 + Real.log (max 1
          (⨅ r : rationalSubgroup F G,
            RepresentationGrowth.adelicSourceNorm F G rho ((r : AdelicGroupPoints F G) * g))) :=
      funext hfun
    rw [this]
    exact hm
  exact measurable_from_quotient.mpr hcomp

/-- The pointwise estimate behind the reduction. -/
theorem sq_div_le_of_siegel_bound {θ sG s δ B : ℝ} {m e : ℕ} (hθ : 0 ≤ θ) (hsG : 1 ≤ sG)
    (hsGs : sG ≤ s) (hδ : 0 ≤ δ) (hB : θ ≤ B * Real.sqrt δ / s ^ (m + e)) :
    (θ * sG ^ m) ^ 2 / (B ^ 2 + 1) ≤ δ / s ^ e := by
  have hs : 1 ≤ s := hsG.trans hsGs
  have hs0 : 0 < s := by linarith
  have hspos : 0 < s ^ (m + e) := pow_pos hs0 _
  have h1 : θ * s ^ (m + e) ≤ B * Real.sqrt δ := by rwa [le_div_iff₀ hspos] at hB
  have hsG0 : 0 ≤ sG := by linarith
  have h2 : θ * sG ^ m * s ^ e ≤ B * Real.sqrt δ := by
    calc θ * sG ^ m * s ^ e ≤ θ * s ^ m * s ^ e := by gcongr
      _ = θ * s ^ (m + e) := by rw [pow_add]; ring
      _ ≤ B * Real.sqrt δ := h1
  have h3 : 0 ≤ θ * sG ^ m * s ^ e := by positivity
  have h4 : (θ * sG ^ m * s ^ e) ^ 2 ≤ B ^ 2 * δ := by
    calc (θ * sG ^ m * s ^ e) ^ 2 ≤ (B * Real.sqrt δ) ^ 2 := pow_le_pow_left₀ h3 h2 2
      _ = B ^ 2 * δ := by rw [mul_pow, Real.sq_sqrt hδ]
  have h5 : (θ * sG ^ m) ^ 2 * s ^ e ≤ B ^ 2 * δ := by
    have hse : s ^ e ≤ (s ^ e) ^ 2 := le_self_pow₀ (one_le_pow₀ hs) two_ne_zero
    have : (θ * sG ^ m) ^ 2 * s ^ e ≤ (θ * sG ^ m * s ^ e) ^ 2 := by
      rw [mul_pow (θ * sG ^ m) (s ^ e)]
      exact mul_le_mul_of_nonneg_left hse (sq_nonneg _)
    linarith
  have hse0 : 0 < s ^ e := pow_pos hs0 e
  rw [div_le_div_iff₀ (by positivity) hse0]
  nlinarith [h5, hδ, sq_nonneg B]

end Proof

/-- **Reduction.** `WavePacketSiegelDecayStatement` and `SiegelDominatedIntegrabilityStatement`
imply `WavePacketRapidDecayStatement`. -/
theorem wavePacketRapidDecay_of_siegel (hdecay : WavePacketSiegelDecayStatement)
    (hint : SiegelDominatedIntegrabilityStatement) : WavePacketRapidDecayStatement := by
  intro F _ _ G _ _ _ hred K N d rho hsmooth hcalc hKmax hrho hP₀ μG Θ hΘ m
  obtain ⟨hcont, hinv, hbound⟩ := hdecay F G hred K rho hsmooth hcalc hKmax hrho hP₀ Θ hΘ
  obtain ⟨T, i, ν, T₀, j, hS, C, t, Ω, e, hΩ, hfin⟩ := hint F G hred rho hrho
  obtain ⟨B, hB⟩ := hbound T i ν T₀ j hS C t Ω hΩ (m + e)
  have hmkout : ∀ y : RationalQuotient F G,
      LeftCosetSpace.mk (rationalSubgroup F G) y.out = y := fun y => Quotient.out_eq y
  -- measurability on the quotient
  have hΘmeas : Measurable (fun y : RationalQuotient F G => Θ y.out) := by
    have hcomp : (fun y : RationalQuotient F G => Θ y.out) ∘
        (LeftCosetSpace.mk (rationalSubgroup F G)) = Θ := by
      funext g
      obtain ⟨q, hq, hout⟩ := out_mk_eq_rational_mul (F := F) (G := G) g
      change Θ (LeftCosetSpace.mk (rationalSubgroup F G) g).out = Θ g
      rw [hout, hinv q hq]
    have hm : Measurable ((fun y : RationalQuotient F G => Θ y.out) ∘
        (LeftCosetSpace.mk (rationalSubgroup F G))) := by
      rw [hcomp]
      exact hcont.measurable
    exact measurable_from_quotient.mpr hm
  have hmeas : AEStronglyMeasurable (fun y : RationalQuotient F G =>
      Θ y.out * (rationalLogHeight F G rho y : ℂ) ^ m) μG :=
    (hΘmeas.mul ((Complex.measurable_ofReal.comp
      (measurable_rationalLogHeight rho)).pow_const m)).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hmeas).mpr ⟨hmeas.norm.pow 2, ?_⟩
  -- the dominated invariant function
  set f : AdelicGroupPoints F G → ℝ≥0∞ := fun g => ENNReal.ofReal
    ((‖Θ g‖ * rationalLogHeight F G rho (LeftCosetSpace.mk (rationalSubgroup F G) g) ^ m) ^ 2 /
      (B ^ 2 + 1)) with hf
  have hfinv : ∀ q ∈ rationalSubgroup F G, ∀ g : AdelicGroupPoints F G, f (q * g) = f g := by
    intro q hq g
    simp only [hf, hinv q hq g, LeftCosetSpace.mk_subgroup_mul (rationalSubgroup F G) ⟨q, hq⟩ g]
  have hfdom : ∀ (a : PositiveRealTorus.intrinsicSubgroup F T₀) (x : AdelicGroupPoints F G),
      IsSiegelPoint F G T i ν T₀ j C t Ω a x →
        f x ≤ ENNReal.ofReal
          (siegelModulus F G T i ν T₀ j a / adelicLogHeight F G rho x ^ e) := by
    intro a x hx
    refine ENNReal.ofReal_le_ofReal (sq_div_le_of_siegel_bound (norm_nonneg _)
      (one_le_rationalLogHeight rho _) (rationalLogHeight_mk_le rho x) ?_ (hB a x hx))
    unfold siegelModulus
    exact finprod_nonneg fun β => finprod_nonneg fun _ => pow_nonneg (NNReal.coe_nonneg _) _
  have hfmeas : Measurable f := by
    have hσ : Measurable fun g : AdelicGroupPoints F G =>
        rationalLogHeight F G rho (LeftCosetSpace.mk (rationalSubgroup F G) g) :=
      (measurable_rationalLogHeight rho).comp (LeftCosetSpace.measurable_mk _)
    exact ENNReal.measurable_ofReal.comp
      (((hcont.measurable.norm.mul (hσ.pow_const m)).pow_const 2).div_const _)
  have hlint := hfin f hfmeas hfinv hfdom
  have heq : ∀ y : RationalQuotient F G,
      ‖‖Θ y.out * (rationalLogHeight F G rho y : ℂ) ^ m‖ ^ 2‖ₑ =
        ENNReal.ofReal (B ^ 2 + 1) * f y.out := by
    intro y
    have hpos : (0 : ℝ) < rationalLogHeight F G rho y :=
      lt_of_lt_of_le one_pos (one_le_rationalLogHeight rho y)
    have hnorm : ‖Θ y.out * (rationalLogHeight F G rho y : ℂ) ^ m‖ =
        ‖Θ y.out‖ * rationalLogHeight F G rho y ^ m := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    have hB1 : (0 : ℝ) < B ^ 2 + 1 := by positivity
    rw [Real.enorm_of_nonneg (by positivity), hf]
    simp only [hmkout]
    rw [← ENNReal.ofReal_mul hB1.le, hnorm, mul_div_cancel₀ _ hB1.ne']
  unfold HasFiniteIntegral
  simp_rw [heq]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hlint

end Langlands.Global
