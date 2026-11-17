import Langlands.HarmonicAnalysis.HarishChandraSchwartz.XiCompactModularComparison
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SphericalTranslation
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeights

/-! # Comparison of `Ξ` for two compact open subgroups

Waldspurger 2003, II.1, defines `Ξ` from one fixed compact open subgroup `K` with `G = P₀ K`.
The source does not state how `Ξ` depends on `K`; this module derives the comparison for the
Library's generic `xi`: for two compact open subgroups `K`, `K'` with `G = P K = P K'` and a
positive character `δ` of `P` trivial on `P ∩ K` and on `P ∩ K'`, there is `C` with
`Ξ_K(g) ≤ C Ξ_{K'}(g)` for all `g`, so that `Ξ_K` and `Ξ_{K'}` are equivalent weights
(`WeightEquivalent`). Consequently the Schwartz space built from `Ξ` and a
height `σ` does not depend on the choice of `K`. The last section specializes both facts to
the actual rational points.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Measure TopologicalSpace
open scoped NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.HarishChandraSchwartz

universe u

section Uniform

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A uniform translation bound for a function `Ξ ≥ 0` that is left invariant under an open
subgroup `H` holds uniformly for left translations by the points of a compact set `C`:
there is `c` with `Ξ(x g) ≤ c Ξ(g)` for all `x ∈ C` and `g ∈ G`. -/
theorem UniformTranslationBound.exists_uniform_left {Ξ : G → ℝ}
    (h : UniformTranslationBound Ξ) (hΞ : ∀ g, 0 ≤ Ξ g) {H : Subgroup G}
    (hH : IsOpen (H : Set G)) (hinv : ∀ k ∈ H, ∀ g, Ξ (k * g) = Ξ g)
    {C : Set G} (hC : IsCompact C) :
    ∃ c : ℝ, ∀ x ∈ C, ∀ g, Ξ (x * g) ≤ c * Ξ g := by
  choose c hc using fun l : G => h l 1
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun l : G => {x : G | x * l⁻¹ ∈ H})
    (fun l => hH.preimage (continuous_id.mul continuous_const))
    (fun x _ => Set.mem_iUnion.mpr ⟨x, by simp [H.one_mem]⟩)
  refine ⟨∑ l ∈ t, |c l|, fun x hx g => ?_⟩
  obtain ⟨l, hlt, hl⟩ := Set.mem_iUnion₂.mp (ht hx)
  have hxl : x * l⁻¹ ∈ H := hl
  have e : x * g = (x * l⁻¹) * (l * g * 1) := by group
  rw [e, hinv _ hxl]
  calc Ξ (l * g * 1) ≤ c l * Ξ g := hc l g
    _ ≤ |c l| * Ξ g := mul_le_mul_of_nonneg_right (le_abs_self _) (hΞ g)
    _ ≤ (∑ l ∈ t, |c l|) * Ξ g := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun l _ => abs_nonneg (c l)) hlt) (hΞ g)

end Uniform

section Comparability

variable {G : Type u}

/-- `Ξ` is **dominated** by `Ξ'`: there is a constant `C` with `Ξ(g) ≤ C Ξ'(g)` for all `g`. -/
def WeightDominated (Ξ Ξ' : G → ℝ) : Prop :=
  ∃ C : ℝ, ∀ g, Ξ g ≤ C * Ξ' g

/-- `Ξ` and `Ξ'` are **equivalent weights**: each is dominated by the other, that is, there are
constants `C`, `C'` with `Ξ(g) ≤ C Ξ'(g)` and `Ξ'(g) ≤ C' Ξ(g)` for all `g`. -/
def WeightEquivalent (Ξ Ξ' : G → ℝ) : Prop :=
  WeightDominated Ξ Ξ' ∧ WeightDominated Ξ' Ξ

theorem WeightEquivalent.symm {Ξ Ξ' : G → ℝ} (h : WeightEquivalent Ξ Ξ') :
    WeightEquivalent Ξ' Ξ :=
  ⟨h.2, h.1⟩

end Comparability

section Compare

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {P K K' : Subgroup G} {hPK : IsIwasawaPair P K} {hPK' : IsIwasawaPair P K'}
  {δ : P →* ℝ≥0ˣ}

/-- The Iwasawa weights `φ_K(p k) = δ(p)^{1/2}` for two compact open subgroups are comparable:
`φ_K ≤ c φ_{K'}`, where `c` bounds `φ_K` on the compact set `K'`. Indeed, writing
`g = q κ'` with `q ∈ P` and `κ' ∈ K'`, one has `φ_K(g) = δ(q)^{1/2} φ_K(κ') = φ_{K'}(g) φ_K(κ')`. -/
theorem exists_iwasawaWeight_le_mul (hδ : ∀ p : P, (p : G) ∈ K → δ p = 1)
    (hδ' : ∀ p : P, (p : G) ∈ K' → δ p = 1) (hK : IsOpen (K : Set G))
    (hK'c : IsCompact (K' : Set G)) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ g, iwasawaWeight hPK δ g ≤ c * iwasawaWeight hPK' δ g := by
  obtain ⟨c, hc⟩ := hK'c.bddAbove_image (continuous_iwasawaWeight (hPK := hPK) hδ hK).continuousOn
  have hc0 : 0 ≤ c := le_trans (iwasawaWeight_nonneg 1) (hc ⟨1, K'.one_mem, rfl⟩)
  refine ⟨c, hc0, fun g => ?_⟩
  obtain ⟨q, hq, κ, hκ, rfl⟩ := hPK' g
  have h1 : iwasawaWeight hPK δ (q * κ) =
      NNReal.sqrt (δ ⟨q, hq⟩ : ℝ≥0) * iwasawaWeight hPK δ κ :=
    iwasawaWeight_mul_left (hPK := hPK) hδ ⟨q, hq⟩ κ
  have h2 : iwasawaWeight hPK' δ (q * κ) = NNReal.sqrt (δ ⟨q, hq⟩ : ℝ≥0) :=
    iwasawaWeight_mul (hPK := hPK') hδ' hq hκ
  rw [h1, h2, mul_comm c]
  exact mul_le_mul_of_nonneg_left (hc ⟨κ, hκ, rfl⟩) (NNReal.coe_nonneg _)

variable [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [CompactSpace K] [CompactSpace K']

/-- **Comparison of `Ξ` for two compact open subgroups** (derived, not stated in Waldspurger
II.1): if `G = P K = P K'`
with `K`, `K'` compact open and `δ` trivial on `P ∩ K` and `P ∩ K'`, there is `C` with
`Ξ_K(g) ≤ C Ξ_{K'}(g)` for all `g ∈ G`.

Proof: with `c₀ = ∫_{K'} φ_K > 0`, Fubini on `K' × K` and left invariance of the Haar
measure of `K` give `c₀ Ξ_K(g) = ∫_K ∫_{K'} φ_K(k' k g) dk' dk`; the inner integral is at most
`c Ξ_{K'}(k g)` by the comparison of the weights, and `Ξ_{K'}(k g) ≤ C₂ Ξ_{K'}(g)` uniformly
for `k` in the compact set `K` by Lemma II.1.2. -/
theorem exists_xi_le_mul (hδ : ∀ p : P, (p : G) ∈ K → δ p = 1)
    (hδ' : ∀ p : P, (p : G) ∈ K' → δ p = 1) (hK : IsOpen (K : Set G))
    (hK' : IsOpen (K' : Set G)) :
    ∃ C : ℝ, ∀ g, xi hPK δ g ≤ C * xi hPK' δ g := by
  have : SecondCountableTopology K :=
    TopologicalSpace.Subtype.secondCountableTopology (K : Set G)
  have : SecondCountableTopology K' :=
    TopologicalSpace.Subtype.secondCountableTopology (K' : Set G)
  set μK := normalizedHaar K
  set μK' := normalizedHaar K'
  set w := iwasawaWeight hPK δ with hw_def
  set w' := iwasawaWeight hPK' δ with hw'_def
  have hw : Continuous w := continuous_iwasawaWeight hδ hK
  have hw' : Continuous w' := continuous_iwasawaWeight hδ' hK'
  have hKc : IsCompact (K : Set G) := isCompact_iff_compactSpace.mpr ‹_›
  have hK'c : IsCompact (K' : Set G) := isCompact_iff_compactSpace.mpr ‹_›
  obtain ⟨c, hc0, hc⟩ :=
    exists_iwasawaWeight_le_mul (hPK := hPK) (hPK' := hPK') hδ hδ' hK hK'c
  obtain ⟨C₂, hC₂⟩ := (xi_uniformTranslationBound (hPK := hPK') hδ' hK').exists_uniform_left
    (fun g => (xi_pos hδ' hK' g).le) hK' (fun k hk g => xi_mul_left hk g) hKc
  set c₀ := ∫ k' : K', w (k' : G) ∂μK'
  have hc₀ : 0 < c₀ := by
    rw [integral_pos_iff_support_of_nonneg (fun k => iwasawaWeight_nonneg _)
      ((hw.comp continuous_subtype_val).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))]
    have hsupp : Function.support (fun k : K' => w (k : G)) = Set.univ :=
      Set.eq_univ_of_forall fun k => (iwasawaWeight_pos _).ne'
    rw [hsupp, measure_univ]
    exact one_pos
  refine ⟨c * C₂ / c₀, fun g => ?_⟩
  set F : K → K' → ℝ := fun k k' => w ((k' : G) * ((k : G) * g)) with hF
  have hFc : Continuous (Function.uncurry F) :=
    hw.comp ((continuous_subtype_val.comp continuous_snd).mul
      ((continuous_subtype_val.comp continuous_fst).mul continuous_const))
  have hFi : Integrable (Function.uncurry F) (μK.prod μK') :=
    hFc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hswap := integral_integral_swap hFi
  -- the integral over `K` for fixed `k' ∈ K'`
  have hinner : ∀ k' : K', ∫ k : K, F k k' ∂μK = w (k' : G) * xi hPK δ g := by
    intro k'
    obtain ⟨q, hq, κ, hκ, hfac⟩ := hPK (k' : G)
    have hpt : ∀ k : K,
        F k k' = NNReal.sqrt (δ ⟨q, hq⟩ : ℝ≥0) * w ((κ : G) * ((k : G) * g)) := by
      intro k
      simp only [hF]
      rw [hfac, mul_assoc]
      exact iwasawaWeight_mul_left hδ ⟨q, hq⟩ _
    have hinv := integral_mul_left_eq_self (μ := μK) (fun k : K => w ((k : G) * g)) ⟨κ, hκ⟩
    simp only [Subgroup.coe_mul, mul_assoc] at hinv
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul, hinv]
    have hq' : w (k' : G) = NNReal.sqrt (δ ⟨q, hq⟩ : ℝ≥0) := by
      rw [hfac]
      exact iwasawaWeight_mul hδ hq hκ
    rw [hq']
    rfl
  -- the integral over `K'` for fixed `k ∈ K`
  have hbound : ∀ k : K, ∫ k' : K', F k k' ∂μK' ≤ c * C₂ * xi hPK' δ g := by
    intro k
    have hi1 : Integrable (fun k' : K' => F k k') μK' :=
      (hw.comp (continuous_subtype_val.mul continuous_const)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hi2 : Integrable (fun k' : K' => c * w' ((k' : G) * ((k : G) * g))) μK' :=
      ((hw'.comp (continuous_subtype_val.mul continuous_const)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)).const_mul c
    calc ∫ k' : K', F k k' ∂μK' ≤ ∫ k' : K', c * w' ((k' : G) * ((k : G) * g)) ∂μK' :=
          integral_mono hi1 hi2 (fun k' => hc _)
      _ = c * xi hPK' δ ((k : G) * g) := by
          rw [integral_const_mul]
          rfl
      _ ≤ c * (C₂ * xi hPK' δ g) := mul_le_mul_of_nonneg_left (hC₂ k k.2 g) hc0
      _ = c * C₂ * xi hPK' δ g := by ring
  have key : c₀ * xi hPK δ g ≤ c * C₂ * xi hPK' δ g := by
    calc c₀ * xi hPK δ g = ∫ k' : K', w (k' : G) * xi hPK δ g ∂μK' := by
          rw [integral_mul_const]
      _ = ∫ k' : K', ∫ k : K, F k k' ∂μK ∂μK' :=
          integral_congr_ae (Filter.Eventually.of_forall fun k' => (hinner k').symm)
      _ = ∫ k : K, ∫ k' : K', F k k' ∂μK' ∂μK := hswap.symm
      _ ≤ ∫ _k : K, c * C₂ * xi hPK' δ g ∂μK :=
          integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun k => integral_nonneg fun k' =>
              iwasawaWeight_nonneg _)
            (integrable_const _) (Filter.Eventually.of_forall hbound)
      _ = c * C₂ * xi hPK' δ g := by simp
  rw [div_mul_eq_mul_div, le_div_iff₀ hc₀]
  linarith

/-- `Ξ_K` and `Ξ_{K'}` are equivalent weights (`exists_xi_le_mul` in both directions). -/
theorem xi_weightEquivalent (hδ : ∀ p : P, (p : G) ∈ K → δ p = 1)
    (hδ' : ∀ p : P, (p : G) ∈ K' → δ p = 1) (hK : IsOpen (K : Set G))
    (hK' : IsOpen (K' : Set G)) :
    WeightEquivalent (xi hPK δ) (xi hPK' δ) :=
  ⟨exists_xi_le_mul hδ hδ' hK hK', exists_xi_le_mul hδ' hδ hK' hK⟩

end Compare

section Weights

variable {G : Type u} {Ξ Ξ' σ : G → ℝ}

/-- If `Ξ ≤ C Ξ'` with `Ξ, Ξ' > 0`, the weights of the seminorms satisfy
`Ξ'(g)⁻¹ (1 + σ(g))^r ≤ C Ξ(g)⁻¹ (1 + σ(g))^r`. -/
theorem weight_le_ofReal_mul_weight (hΞ : ∀ g, 0 < Ξ g) (hΞ' : ∀ g, 0 < Ξ' g)
    (hσ : ∀ g, 0 ≤ σ g) {C : ℝ} (hC : ∀ g, Ξ g ≤ C * Ξ' g) (r : ℝ) (g : G) :
    weight Ξ' σ r g ≤ ENNReal.ofReal C * weight Ξ σ r g := by
  have h₁ := hΞ g
  have h₂ := hΞ' g
  have hC0 : 0 ≤ C := by
    by_contra hneg
    have : C * Ξ' g < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) h₂
    linarith [hC g]
  have hb : 0 ≤ (1 + σ g) ^ r := Real.rpow_nonneg (by linarith [hσ g]) r
  have hinv : (Ξ' g)⁻¹ ≤ C * (Ξ g)⁻¹ := by
    calc (Ξ' g)⁻¹ = Ξ g * ((Ξ g)⁻¹ * (Ξ' g)⁻¹) := by field_simp
      _ ≤ (C * Ξ' g) * ((Ξ g)⁻¹ * (Ξ' g)⁻¹) :=
          mul_le_mul_of_nonneg_right (hC g) (by positivity)
      _ = C * (Ξ g)⁻¹ := by field_simp
  unfold weight
  rw [← ENNReal.ofReal_mul hC0]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (Ξ' g)⁻¹ * (1 + σ g) ^ r ≤ (C * (Ξ g)⁻¹) * (1 + σ g) ^ r :=
        mul_le_mul_of_nonneg_right hinv hb
    _ = C * ((Ξ g)⁻¹ * (1 + σ g) ^ r) := by ring

/-- If `Ξ ≤ C Ξ'` with `Ξ, Ξ' > 0`, then `ν'_r(f) ≤ C ν_r(f)` for the seminorms defined with
`Ξ'` and `Ξ`. -/
theorem nu_le_ofReal_mul_nu (hΞ : ∀ g, 0 < Ξ g) (hΞ' : ∀ g, 0 < Ξ' g)
    (hσ : ∀ g, 0 ≤ σ g) {C : ℝ} (hC : ∀ g, Ξ g ≤ C * Ξ' g) (r : ℝ) (f : G → ℂ) :
    nu Ξ' σ r f ≤ ENNReal.ofReal C * nu Ξ σ r f := by
  refine iSup_le fun g => ?_
  calc ‖f g‖ₑ * weight Ξ' σ r g ≤ ‖f g‖ₑ * (ENNReal.ofReal C * weight Ξ σ r g) := by
        gcongr
        exact weight_le_ofReal_mul_weight hΞ hΞ' hσ hC r g
    _ = ENNReal.ofReal C * (‖f g‖ₑ * weight Ξ σ r g) := by ring
    _ ≤ ENNReal.ofReal C * nu Ξ σ r f := by
        gcongr
        exact enorm_mul_weight_le_nu f g

variable [Group G]

/-- If `Ξ ≤ C Ξ'`, every level space for `Ξ` is contained in the level space for `Ξ'`. -/
theorem levelSubmodule_le_of_le_mul (hΞ : ∀ g, 0 < Ξ g) (hΞ' : ∀ g, 0 < Ξ' g)
    (hσ : ∀ g, 0 ≤ σ g) {C : ℝ} (hC : ∀ g, Ξ g ≤ C * Ξ' g) (H : Subgroup G) :
    levelSubmodule Ξ σ H ≤ levelSubmodule Ξ' σ H := fun f hf =>
  ⟨hf.1, fun r => lt_of_le_of_lt (nu_le_ofReal_mul_nu hΞ hΞ' hσ hC r f)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hf.2 r))⟩

variable [TopologicalSpace G]

/-- If `Ξ ≤ C Ξ'`, the Schwartz space for `Ξ` is contained in the Schwartz space for `Ξ'`. -/
theorem schwartzSubmodule_le_of_le_mul (hΞ : ∀ g, 0 < Ξ g) (hΞ' : ∀ g, 0 < Ξ' g)
    (hσ : ∀ g, 0 ≤ σ g) {C : ℝ} (hC : ∀ g, Ξ g ≤ C * Ξ' g) :
    schwartzSubmodule Ξ σ ≤ schwartzSubmodule Ξ' σ :=
  iSup_mono fun K => levelSubmodule_le_of_le_mul hΞ hΞ' hσ hC K.toSubgroup

/-- Two-sided comparability of `Ξ` and `Ξ'` gives equal Schwartz spaces. -/
theorem schwartzSubmodule_eq_of_le_mul (hΞ : ∀ g, 0 < Ξ g) (hΞ' : ∀ g, 0 < Ξ' g)
    (hσ : ∀ g, 0 ≤ σ g) {C C' : ℝ} (hC : ∀ g, Ξ g ≤ C * Ξ' g)
    (hC' : ∀ g, Ξ' g ≤ C' * Ξ g) :
    schwartzSubmodule Ξ σ = schwartzSubmodule Ξ' σ :=
  le_antisymm (schwartzSubmodule_le_of_le_mul hΞ hΞ' hσ hC)
    (schwartzSubmodule_le_of_le_mul hΞ' hΞ hσ hC')

/-- Equivalent positive weights give the same Schwartz space. -/
theorem schwartzSubmodule_eq_of_weightEquivalent (hΞ : ∀ g, 0 < Ξ g) (hΞ' : ∀ g, 0 < Ξ' g)
    (hσ : ∀ g, 0 ≤ σ g) (h : WeightEquivalent Ξ Ξ') :
    schwartzSubmodule Ξ σ = schwartzSubmodule Ξ' σ := by
  obtain ⟨⟨C, hC⟩, ⟨C', hC'⟩⟩ := h
  exact schwartzSubmodule_eq_of_le_mul hΞ hΞ' hσ hC hC'

end Weights

section Rational

open scoped CategoryTheory.MonObj

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

local instance xiCompareSecondCountable : SecondCountableTopology (rationalPoints G) :=
  rationalPoint_secondCountableTopology F G

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {K K' : Subgroup (rationalPoints G)}
  (hKo : IsOpen (K : Set (rationalPoints G))) (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
  (hK'o : IsOpen (K' : Set (rationalPoints G))) (hK'c : IsCompact (K' : Set (rationalPoints G)))
  (hPK' : IsIwasawaPair (standardParabolicPoints i ν ∅) K')

include hKo hK'o in
/-- **Comparison of the actual `Ξ` for two compact open subgroups**: if `K`, `K'` are compact
open subgroups of `G(F)` with `G(F) = P₀(F) K = P₀(F) K'`, there is `C` with
`Ξ_K(g) ≤ C Ξ_{K'}(g)` for all `g ∈ G(F)`. -/
theorem exists_rationalXi_le_mul :
    ∃ C : ℝ, ∀ g, rationalXi hKc hPK g ≤ C * rationalXi hK'c hPK' g := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have : CompactSpace K' := isCompact_iff_compactSpace.mp hK'c
  exact exists_xi_le_mul (fun p hp => rationalMinimalModulus_eq_one i ν hKo hKc p hp)
    (fun p hp => rationalMinimalModulus_eq_one i ν hK'o hK'c p hp) hKo hK'o

include hKo hK'o in
/-- The actual `Ξ_K` and `Ξ_{K'}` are equivalent weights. -/
theorem rationalXi_weightEquivalent :
    WeightEquivalent (rationalXi hKc hPK) (rationalXi hK'c hPK') :=
  ⟨exists_rationalXi_le_mul hKo hKc hPK hK'o hK'c hPK',
    exists_rationalXi_le_mul hK'o hK'c hPK' hKo hKc hPK⟩

include hKo hK'o in
/-- **The actual Schwartz space does not depend on the compact open subgroup**: for compact
open `K`, `K'` with `G(F) = P₀(F) K = P₀(F) K'` and every matrix representation `ρ`, the
Schwartz spaces `C(G)` for `Ξ_K` and `Ξ_{K'}` (with the same height `σ = rationalHeight ρ`)
are the same subspace of the functions on `G(F)`. -/
theorem rationalSchwartzSubmodule_eq {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (ρ : MatrixRepresentation G n) :
    schwartzSubmodule (rationalXi hKc hPK) (rationalHeight (F := F) ρ) =
      schwartzSubmodule (rationalXi hK'c hPK') (rationalHeight (F := F) ρ) := by
  obtain ⟨C, hC⟩ := exists_rationalXi_le_mul hKo hKc hPK hK'o hK'c hPK'
  obtain ⟨C', hC'⟩ := exists_rationalXi_le_mul hK'o hK'c hPK' hKo hKc hPK
  exact schwartzSubmodule_eq_of_le_mul (rationalXi_pos hKo hKc hPK)
    (rationalXi_pos hK'o hK'c hPK') (rationalHeight_nonneg ρ) hC hC'

end Rational

end Langlands.HarishChandraSchwartz
