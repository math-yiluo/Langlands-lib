import Langlands.Global.AdelicWeakConstantTermLeviTemperedReduction
import Langlands.Global.AdelicNormOneSiegelIntegrability
import Langlands.Global.AdelicSiegelNormMinimalityAssembly
import Langlands.Global.AdelicSiegelDiagonalHeightBound
import Langlands.Global.AdelicRationalQuotientSummableLogHeightProof

/-! # Integrability of Siegel-dominated functions on the norm-one quotient

This module proves `Langlands.Global.NormOneSiegelDominatedIntegrabilityStatement`. The Siegel
data are those of the norm-one chart bound `exists_normOneSiegelIntegralBound`, with `Ω` its
finite set of right translates. Two height comparisons at the points `n m a k w` of that chart
turn the hypothesis `f ≤ δ(a) σ^d` into the hypothesis of the chart bound for
`f σ_{[G]}^{-(d + d₀)}`: the logarithmic height is at most a constant times the quotient height
(norm minimality), and the simple-root logarithmic size of `a` is at most a constant times the
logarithmic height. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ENNReal NNReal

set_option autoImplicit false

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints PositiveRealTorus

section Comparison

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T} {T₀ : CommGroupScheme (Spec (CommRingCat.of F))}
  {j : T₀ ⟶ T}

omit [IsAffine G.X.left] in
/-- **Logarithmic height against quotient height on a Siegel chart** (Mœglin–Waldspurger I.2.2
(vii)). For a point `s w` with `s` in a weak Siegel product and `w` in a finite set `W`,
`σ(s w) ≤ K σ_{[G]}(G(F) s w)`. -/
theorem exists_adelicLogHeight_le_mul_rationalLogHeight (hG : IsConnectedReductive G)
    (hsetup : IsSiegelAlgebraicSetup F G T i ν T₀ j) {N : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N)
    (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
    (t : ℝ≥0ˣ) {W : Set (AdelicGroupPoints F G)} (hW : W.Finite) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ s ∈ weakSiegelProduct F G T i ν (canonicalStandardFactors F G T i ν) C T₀ j t,
      ∀ w ∈ W, adelicLogHeight F G rho (s * w) ≤
        K * rationalLogHeight F G rho (LeftCosetSpace.mk (rationalSubgroup F G) (s * w)) := by
  have hT₀ : IsSplitTorus T₀.toGrp := by
    obtain ⟨_, _, _, _, ht₀, _⟩ := hsetup.2.2.2.2.2.2.2.1
    exact ht₀.1.1
  obtain ⟨c, hc, hdiag⟩ := exists_adelicHeight_map_le_rational_mul F G rho hN T₀ hT₀
    (CommGroupScheme.groupHom j ≫ i)
  obtain ⟨c', hc'⟩ := exists_adelicHeight_le_mul_rational_of_diagonal F G T i ν T₀ j hG hsetup
    rho hN C t hc hdiag
  set H := RepresentationGrowth.adelicHeight F G rho
  have h0 : ∀ g, 0 ≤ H g := fun g =>
    zero_le_one.trans (RepresentationGrowth.one_le_adelicHeight F G rho hN g)
  obtain ⟨BW, hBW⟩ := (hW.image (fun w => H w * H w⁻¹)).bddAbove
  set c'' := max c' 1
  set L := c'' * max BW 1
  have hL : 1 ≤ L := one_le_mul_of_one_le_of_one_le (le_max_right _ _) (le_max_right _ _)
  have hL0 : 0 ≤ Real.log L := Real.log_nonneg hL
  refine ⟨1 + Real.log L, by linarith, fun s hs w hw => ?_⟩
  have hX : ∀ q ∈ rationalSubgroup F G, H (s * w) ≤
      L * H (q * (LeftCosetSpace.mk (rationalSubgroup F G) (s * w)).out) := by
    intro q hq
    obtain ⟨r, hr, hout⟩ := out_mk_eq_rational_mul (F := F) (G := G) (s * w)
    obtain ⟨q₀, hq₀⟩ := (rationalSubgroup F G).mul_mem hq hr
    have hY : q * (LeftCosetSpace.mk (rationalSubgroup F G) (s * w)).out =
        rational F G q₀ * s * w := by
      rw [hout, hq₀]
      simp only [mul_assoc]
    rw [hY]
    have hs' : H s ≤ c'' * H (rational F G q₀ * s) :=
      (hc' s hs q₀).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (h0 _))
    have hqs : H (rational F G q₀ * s) ≤ H (rational F G q₀ * s * w) * H w⁻¹ := by
      have := RepresentationGrowth.adelicHeight_mul_le F G rho hN (rational F G q₀ * s * w) w⁻¹
      rwa [mul_inv_cancel_right] at this
    have hww : H w * H w⁻¹ ≤ max BW 1 := (hBW ⟨w, hw, rfl⟩).trans (le_max_left _ _)
    have hc0 : 0 ≤ c'' := zero_le_one.trans (le_max_right _ _)
    calc H (s * w) ≤ H s * H w := RepresentationGrowth.adelicHeight_mul_le F G rho hN s w
      _ ≤ c'' * H (rational F G q₀ * s) * H w := by gcongr; exact h0 _
      _ ≤ c'' * (H (rational F G q₀ * s * w) * H w⁻¹) * H w := by gcongr; exact h0 _
      _ = c'' * (H w * H w⁻¹) * H (rational F G q₀ * s * w) := by ring
      _ ≤ c'' * max BW 1 * H (rational F G q₀ * s * w) := by
          gcongr
          exact h0 _
  have hσ := adelicLogHeight_sub_log_le_rationalLogHeight rho hN hL hX
  have hτ := one_le_rationalLogHeight rho (LeftCosetSpace.mk (rationalSubgroup F G) (s * w))
  nlinarith

/-- **Simple-root logarithms against the logarithmic height on a Siegel chart.** For `a` in the
weak simple-root chamber and a point `X = n m a k w` of the Siegel chart with `w` in a finite
set, `1 + ∑_{α ∈ Δ} |log |α(a)|| ≤ K σ(X)`. -/
theorem exists_siegelRootLogSize_le_mul_adelicLogHeight
    (hsetup : IsSiegelAlgebraicSetup F G T i ν T₀ j) {N : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
    (t : ℝ≥0ˣ) {W : Set (AdelicGroupPoints F G)} (hW : W.Finite) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ a ∈ weakSimpleRootChamber F T₀ T j G i ν t,
      ∀ n ∈ C.omegaN, ∀ m ∈ C.omegaM, ∀ k ∈ C.compactSubgroup, ∀ w ∈ W,
        siegelRootLogSize i ν j a ≤ K * adelicLogHeight F G rho
          (map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) n *
            map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m *
              positiveMap F G T i T₀ j a * k * w) := by
  classical
  obtain ⟨hTmax, -, -, -, -, -, -, -, Z₀, zc, hzsplit, -⟩ := id hsetup
  have hzc : IsCentral (CommGroupScheme.groupHom zc ≫ i) := hzsplit.1.2
  have hZ : IsSplitTorus Z₀.toGrp := hzsplit.1.1.1
  let : Fintype (simpleRelativeRoots i ν) := (hTmax.1.1.finite_simpleRelativeRoots i ν).fintype
  set Lsc := Real.log ((N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult))
  have hLsc : 0 ≤ Lsc := by
    apply Real.log_nonneg
    exact one_le_pow₀ (by exact_mod_cast hN)
  obtain ⟨Bh, hBh1, hBh⟩ := exists_adelicHeight_siegelTorusMap_le zc hzc rho hN C hW
  have hroot : ∀ α : simpleRelativeRoots i ν, ∃ c : ℝ, 0 ≤ c ∧
      ∀ a ∈ weakSimpleRootChamber F T₀ T j G i ν t,
      ∀ n ∈ C.omegaN, ∀ m ∈ C.omegaM, ∀ k ∈ C.compactSubgroup, ∀ w ∈ W,
        |characterLog F T₀.toGrp a.val (j ≫ (α : characterLattice T))| ≤ c * adelicLogHeight F G rho
          (map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) n *
            map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m *
              positiveMap F G T i T₀ j a * k * w) := by
    intro α
    have hα : (α : characterLattice T) ∈ relativeRoots i :=
      positiveRelativeRoots_subset_relativeRoots i ν (simpleRelativeRoots_subset_positive i ν α.2)
    obtain ⟨Cα, hCα, eα, hb⟩ := exists_rootNorm_le zc hzc rho hN hrho hsetup hZ hα
    set C' := Cα * Bh ^ eα
    have hC' : 1 ≤ C' := one_le_mul_of_one_le_of_one_le hCα (one_le_pow₀ hBh1)
    set c₀ := |Real.log ((t : ℝ≥0) : ℝ)| + Real.log C' + eα * Lsc
    have hc₀ : 0 ≤ c₀ := by
      have := Real.log_nonneg hC'
      positivity
    refine ⟨c₀ + eα, by positivity, ?_⟩
    intro a ha n hn m hm k hk w hw
    set X := map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) n *
      map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m *
        positiveMap F G T i T₀ j a * k * w with hXdef
    let p : intrinsicSubgroup F Z₀ × intrinsicSubgroup F T₀ := (1, a)
    have hp : siegelTorusMap (j := j) zc hzc p = positiveMap F G T i T₀ j a := by
      rw [siegelTorusMap_apply]
      simp only [p, map_one, one_mul]
    have hXp : map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) n *
        map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m *
          siegelTorusMap (j := j) zc hzc p * k * w = X := by
      rw [hp]
    set r : ℝ≥0 := (normCharacter F T₀ (j ≫ (α : characterLattice T)) a : ℝ≥0)
    have htr : ((t : ℝ≥0) : ℝ) ≤ (r : ℝ) :=
      NNReal.coe_le_coe.mpr (Units.val_le_val.mpr (ha (α : characterLattice T) α.2))
    have ht0 : (0 : ℝ) < ((t : ℝ≥0) : ℝ) :=
      NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
    have hhX := RepresentationGrowth.one_le_adelicHeight F G rho hN X
    have hra : (r : ℝ) ≤ C' * RepresentationGrowth.adelicHeight F G rho X ^ eα := by
      have h1 := hb p
      have h2 := hBh p n hn m hm k hk w hw
      rw [hXp] at h2
      have h0a : 0 ≤ RepresentationGrowth.adelicHeight F G rho (siegelTorusMap (j := j) zc hzc p) :=
        zero_le_one.trans (RepresentationGrowth.one_le_adelicHeight F G rho hN _)
      calc (r : ℝ) ≤ Cα * RepresentationGrowth.adelicHeight F G rho
            (siegelTorusMap (j := j) zc hzc p) ^ eα := h1
        _ ≤ Cα * (Bh * RepresentationGrowth.adelicHeight F G rho X) ^ eα := by gcongr
        _ = C' * RepresentationGrowth.adelicHeight F G rho X ^ eα := by
            rw [mul_pow]
            ring
    have hlog := abs_log_le_of_mem_Icc ht0 htr hC' hhX eα hra
    have hσ := log_adelicHeight_le rho hN X
    have hσ1 := one_le_adelicLogHeight rho X
    change |Real.log (r : ℝ)| ≤ _
    have he0 : (0 : ℝ) ≤ eα := Nat.cast_nonneg _
    have : (eα : ℝ) * Real.log (RepresentationGrowth.adelicHeight F G rho X) ≤
        eα * (Lsc + adelicLogHeight F G rho X) := mul_le_mul_of_nonneg_left hσ he0
    nlinarith
  choose c hc hcb using hroot
  refine ⟨1 + ∑ α, c α, ?_, ?_⟩
  · have := Finset.sum_nonneg fun α (_ : α ∈ Finset.univ) => hc α
    linarith
  intro a ha n hn m hm k hk w hw
  set X := map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) n *
    map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m *
      positiveMap F G T i T₀ j a * k * w
  have hσ1 := one_le_adelicLogHeight rho X
  have hsum : ∑ α : simpleRelativeRoots i ν,
      |characterLog F T₀.toGrp a.val (j ≫ (α : characterLattice T))| ≤
      (∑ α, c α) * adelicLogHeight F G rho X := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun α _ => hcb α a ha n hn m hm k hk w hw
  change 1 + ∑ᶠ α : simpleRelativeRoots i ν,
      |characterLog F T₀.toGrp a.val (j ≫ (α : characterLattice T))| ≤ _
  rw [finsum_eq_sum_of_fintype]
  nlinarith

end Comparison

/-- An elementary estimate: if `σ ≤ K₁ τ` and `ρ ≤ K₂ σ` with all quantities at least one, then
`δ σ^d τ^{-(d + d₀)} ≤ K₁^{d + d₀} K₂^{d₀} δ ρ^{-d₀}` for `δ ≥ 0`. -/
theorem mul_pow_mul_inv_pow_le {δ σ τ ρ K₁ K₂ : ℝ} (d d₀ : ℕ) (hδ : 0 ≤ δ) (hσ : 1 ≤ σ)
    (hτ : 1 ≤ τ) (hρ : 1 ≤ ρ) (hK₁ : 1 ≤ K₁) (hK₂ : 1 ≤ K₂) (h₁ : σ ≤ K₁ * τ)
    (h₂ : ρ ≤ K₂ * σ) :
    δ * σ ^ d * (τ ^ (d + d₀))⁻¹ ≤ K₁ ^ (d + d₀) * K₂ ^ d₀ * δ * (ρ⁻¹) ^ d₀ := by
  have hσ0 : 0 < σ := one_pos.trans_le hσ
  have hτ0 : 0 < τ := one_pos.trans_le hτ
  have hρ0 : 0 < ρ := one_pos.trans_le hρ
  have hK₁0 : 0 < K₁ := one_pos.trans_le hK₁
  have hK₂0 : 0 < K₂ := one_pos.trans_le hK₂
  -- `τ^{-n} ≤ K₁^n σ^{-n}`
  have hA : (τ ^ (d + d₀))⁻¹ ≤ K₁ ^ (d + d₀) * (σ ^ (d + d₀))⁻¹ := by
    have hp : σ ^ (d + d₀) ≤ K₁ ^ (d + d₀) * τ ^ (d + d₀) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ hσ0.le h₁ _
    rw [inv_le_comm₀ (by positivity) (by positivity), mul_inv, inv_inv]
    calc (K₁ ^ (d + d₀))⁻¹ * σ ^ (d + d₀) ≤ (K₁ ^ (d + d₀))⁻¹ * (K₁ ^ (d + d₀) * τ ^ (d + d₀)) :=
          mul_le_mul_of_nonneg_left hp (by positivity)
      _ = τ ^ (d + d₀) := by
          rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  -- `σ^d σ^{-(d + d₀)} = (σ⁻¹)^{d₀}`
  have hB : σ ^ d * (σ ^ (d + d₀))⁻¹ = (σ⁻¹) ^ d₀ := by
    rw [pow_add, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul, inv_pow]
  -- `σ⁻¹ ≤ K₂ ρ⁻¹`
  have hC : σ⁻¹ ≤ K₂ * ρ⁻¹ := by
    rw [inv_le_comm₀ hσ0 (by positivity), mul_inv, inv_inv]
    calc K₂⁻¹ * ρ ≤ K₂⁻¹ * (K₂ * σ) := mul_le_mul_of_nonneg_left h₂ (by positivity)
      _ = σ := by rw [← mul_assoc, inv_mul_cancel₀ hK₂0.ne', one_mul]
  have hD : (σ⁻¹) ^ d₀ ≤ K₂ ^ d₀ * (ρ⁻¹) ^ d₀ := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hC _
  calc δ * σ ^ d * (τ ^ (d + d₀))⁻¹ ≤ δ * σ ^ d * (K₁ ^ (d + d₀) * (σ ^ (d + d₀))⁻¹) :=
        mul_le_mul_of_nonneg_left hA (by positivity)
    _ = K₁ ^ (d + d₀) * δ * (σ ^ d * (σ ^ (d + d₀))⁻¹) := by ring
    _ = K₁ ^ (d + d₀) * δ * (σ⁻¹) ^ d₀ := by rw [hB]
    _ ≤ K₁ ^ (d + d₀) * δ * (K₂ ^ d₀ * (ρ⁻¹) ^ d₀) :=
        mul_le_mul_of_nonneg_left hD (by positivity)
    _ = K₁ ^ (d + d₀) * K₂ ^ d₀ * δ * (ρ⁻¹) ^ d₀ := by ring

section Main

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- The image of a norm-one class in `G(F) \ G(𝔸)` is the class of its representative. -/
theorem normOneQuotientInclusion_eq_mk_out (y : NormOneRationalQuotient F G) :
    normOneQuotientInclusion F G y =
      LeftCosetSpace.mk (rationalSubgroup F G) ((Quotient.out y : normOneSubgroup F G) :
        AdelicGroupPoints F G) := by
  conv_lhs => rw [← Quotient.out_eq y]
  rfl

/-- **Main case, `N > 0`.** -/
theorem normOneSiegelDominatedIntegrability_of_pos (hG : IsConnectedReductive G) {N : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
      (ν : cocharacterLattice T) (T₀ : CommGroupScheme (Spec (CommRingCat.of F)))
      (j : T₀ ⟶ T), IsSiegelAlgebraicSetup F G T i ν T₀ j ∧
    ∃ (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
      (t : ℝ≥0ˣ) (Ω : Set (AdelicGroupPoints F G)), IsCompact Ω ∧
      ∀ d : ℕ, ∃ (n : ℕ) (B : ℝ≥0),
        ∀ f : AdelicGroupPoints F G → ℝ≥0∞, Measurable f →
          (∀ q ∈ rationalSubgroup F G, ∀ g : AdelicGroupPoints F G, f (q * g) = f g) →
          (∀ (a : PositiveRealTorus.intrinsicSubgroup F T₀) (x : AdelicGroupPoints F G),
            IsSiegelPoint F G T i ν T₀ j C t Ω a x → x ∈ normOneSubgroup F G →
              f x ≤ ENNReal.ofReal
                (siegelModulus F G T i ν T₀ j a * adelicLogHeight F G rho x ^ d)) →
          ∫⁻ y : NormOneRationalQuotient F G,
              f ((Quotient.out y : normOneSubgroup F G) : AdelicGroupPoints F G) *
                ENNReal.ofReal ((rationalLogHeight F G rho (normOneQuotientInclusion F G y) ^ n)⁻¹)
            ∂(normOneRationalQuotientHaarMeasure F G) ≤ B := by
  classical
  obtain ⟨T, i, ν, T₀, j, hS⟩ := siegelAlgebraicSetupExistence_of_structural
    genericMinimalParabolic derivedMaximalSplitTorus derivedCentralSplitTorusProduct F G hG
  obtain ⟨C, t, W, d₀, L, hW, hW1, hL, hbd⟩ := exists_normOneSiegelIntegralBound i ν j hG hS
  obtain ⟨K₁, hK₁, hK₁b⟩ :=
    exists_adelicLogHeight_le_mul_rationalLogHeight hG hS rho hN C t hW
  obtain ⟨K₂, hK₂, hK₂b⟩ :=
    exists_siegelRootLogSize_le_mul_adelicLogHeight hS rho hN hrho C t hW
  refine ⟨T, i, ν, T₀, j, hS, C, t, W, hW.isCompact, fun d => ?_⟩
  set B' : ℝ≥0∞ := ENNReal.ofReal (K₁ ^ (d + d₀) * K₂ ^ d₀)
  have hBL : B' * L ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hL.ne
  refine ⟨d + d₀, (B' * L).toNNReal, fun f hf hinv hbound => ?_⟩
  set τ : AdelicGroupPoints F G → ℝ := fun x =>
    rationalLogHeight F G rho (LeftCosetSpace.mk (rationalSubgroup F G) x)
  let g : AdelicGroupPoints F G → ℝ≥0∞ := fun x =>
    f x * ENNReal.ofReal ((τ x ^ (d + d₀))⁻¹)
  have hτm : Measurable τ :=
    (measurable_rationalLogHeight rho).comp (LeftCosetSpace.measurable_mk _)
  have hg : Measurable g :=
    hf.mul (ENNReal.measurable_ofReal.comp (hτm.pow_const _).inv)
  have hginv : ∀ q ∈ rationalSubgroup F G, ∀ x : AdelicGroupPoints F G, g (q * x) = g x := by
    intro q hq x
    have hmk : LeftCosetSpace.mk (rationalSubgroup F G) (q * x) =
        LeftCosetSpace.mk (rationalSubgroup F G) x :=
      LeftCosetSpace.mk_subgroup_mul (rationalSubgroup F G) ⟨q, hq⟩ x
    simp only [g, τ, hmk, hinv q hq x]
  have hpt : ∀ a ∈ weakSimpleRootChamber F T₀ T j G i ν t, ∀ n ∈ C.omegaN, ∀ m ∈ C.omegaM,
      ∀ k ∈ C.compactSubgroup, ∀ w ∈ W,
        g (map F _ G (Standard.unipotentHom i ν ∅) n * map F _ G (Standard.leviHom i ν ∅) m *
          positiveMap F G T i T₀ j a * k * w) ≤
            B' * (siegelModulusNN (i := i) (ν := ν) (j := j) a : ℝ≥0∞) *
              ENNReal.ofReal ((siegelRootLogSize i ν j a)⁻¹ ^ d₀) := by
    intro a ha n hn m hm k hk w hw
    set s := map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) n *
      map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m *
        positiveMap F G T i T₀ j a * k with hsdef
    have hs : s ∈ weakSiegelProduct F G T i ν (canonicalStandardFactors F G T i ν) C T₀ j t :=
      (mem_productSet_iff F G T i ν (canonicalStandardFactors F G T i ν) C T₀ j _ _).mpr
        ⟨n, hn, m, hm, a, ha, k, hk, rfl⟩
    have hX1 : s * w ∈ normOneSubgroup F G :=
      (normOneSubgroup F G).mul_mem (hS.weakSiegelProduct_subset_normOne F G T i ν T₀ j C t hs)
        (hW1 hw)
    have hsp : IsSiegelPoint F G T i ν T₀ j C t W a (s * w) :=
      ⟨1, Subgroup.one_mem _, n, hn, m, hm, ha, k, hk, w, hw, by rw [one_mul]⟩
    have hfx := hbound a (s * w) hsp hX1
    have h₁ := hK₁b s hs w hw
    have h₂ := hK₂b a ha n hn m hm k hk w hw
    have hσ1 := one_le_adelicLogHeight rho (s * w)
    have hτ1 : 1 ≤ τ (s * w) := one_le_rationalLogHeight rho _
    have hρ1 := one_le_siegelRootLogSize i ν j a
    have hδ : 0 ≤ siegelModulus F G T i ν T₀ j a := by
      rw [← coe_siegelModulusNN]
      exact NNReal.coe_nonneg _
    have hreal := mul_pow_mul_inv_pow_le d d₀ hδ hσ1 hτ1 hρ1 hK₁ hK₂ h₁ h₂
    change f (s * w) * ENNReal.ofReal ((τ (s * w) ^ (d + d₀))⁻¹) ≤ _
    calc f (s * w) * ENNReal.ofReal ((τ (s * w) ^ (d + d₀))⁻¹)
        ≤ ENNReal.ofReal (siegelModulus F G T i ν T₀ j a * adelicLogHeight F G rho (s * w) ^ d) *
            ENNReal.ofReal ((τ (s * w) ^ (d + d₀))⁻¹) := by gcongr
      _ = ENNReal.ofReal (siegelModulus F G T i ν T₀ j a * adelicLogHeight F G rho (s * w) ^ d *
            (τ (s * w) ^ (d + d₀))⁻¹) := (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (K₁ ^ (d + d₀) * K₂ ^ d₀ * siegelModulus F G T i ν T₀ j a *
            (siegelRootLogSize i ν j a)⁻¹ ^ d₀) := ENNReal.ofReal_le_ofReal hreal
      _ = B' * (siegelModulusNN (i := i) (ν := ν) (j := j) a : ℝ≥0∞) *
            ENNReal.ofReal ((siegelRootLogSize i ν j a)⁻¹ ^ d₀) := by
          have hK0 : 0 ≤ K₁ ^ (d + d₀) * K₂ ^ d₀ := by positivity
          rw [ENNReal.ofReal_mul (mul_nonneg hK0 hδ), ENNReal.ofReal_mul hK0, ← coe_siegelModulusNN,
            ENNReal.ofReal_coe_nnreal]
  have hint := hbd g hg hginv B' hpt
  rw [ENNReal.coe_toNNReal hBL]
  refine le_of_eq_of_le ?_ hint
  refine lintegral_congr fun y => ?_
  simp only [g, τ, normOneQuotientInclusion_eq_mk_out]

/-- **Degenerate case, `N = 0`.** A closed embedding into `GL_0` forces `G(𝔸)` to be trivial;
then `[G]¹` is a point of finite measure and the integrand is bounded by its value at the
identity, a Siegel point. -/
theorem normOneSiegelDominatedIntegrability_of_zero (hG : IsConnectedReductive G)
    (rho : MatrixRepresentation G (Fin 0)) (hrho : IsClosedSubgroup rho) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
      (ν : cocharacterLattice T) (T₀ : CommGroupScheme (Spec (CommRingCat.of F)))
      (j : T₀ ⟶ T), IsSiegelAlgebraicSetup F G T i ν T₀ j ∧
    ∃ (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
      (t : ℝ≥0ˣ) (Ω : Set (AdelicGroupPoints F G)), IsCompact Ω ∧
      ∀ d : ℕ, ∃ (n : ℕ) (B : ℝ≥0),
        ∀ f : AdelicGroupPoints F G → ℝ≥0∞, Measurable f →
          (∀ q ∈ rationalSubgroup F G, ∀ g : AdelicGroupPoints F G, f (q * g) = f g) →
          (∀ (a : PositiveRealTorus.intrinsicSubgroup F T₀) (x : AdelicGroupPoints F G),
            IsSiegelPoint F G T i ν T₀ j C t Ω a x → x ∈ normOneSubgroup F G →
              f x ≤ ENNReal.ofReal
                (siegelModulus F G T i ν T₀ j a * adelicLogHeight F G rho x ^ d)) →
          ∫⁻ y : NormOneRationalQuotient F G,
              f ((Quotient.out y : normOneSubgroup F G) : AdelicGroupPoints F G) *
                ENNReal.ofReal ((rationalLogHeight F G rho (normOneQuotientInclusion F G y) ^ n)⁻¹)
            ∂(normOneRationalQuotientHaarMeasure F G) ≤ B := by
  classical
  have : Subsingleton (AdelicGL F 0) :=
    ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
  have hsub : Subsingleton (AdelicGroupPoints F G) :=
    (RepresentationGrowth.isClosedEmbedding_adelicMatrix F G rho hrho).injective.subsingleton
  obtain ⟨T, i, ν, T₀, j, hS⟩ := siegelAlgebraicSetupExistence_of_structural
    genericMinimalParabolic derivedMaximalSplitTorus derivedCentralSplitTorusProduct F G hG
  let C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅) :=
    ⟨{1}, {1}, isCompact_singleton, isCompact_singleton, ⊥, by
      rw [Subgroup.coe_bot]
      exact isCompact_singleton⟩
  let : IsFiniteMeasure (normOneRationalQuotientHaarMeasure F G) :=
    isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_connectedReductive F G hG
  refine ⟨T, i, ν, T₀, j, hS, C, 1, {1}, isCompact_singleton, fun d => ?_⟩
  set b : ℝ≥0∞ := ENNReal.ofReal (siegelModulus F G T i ν T₀ j 1 *
    adelicLogHeight F G rho 1 ^ d)
  have hb : b * normOneRationalQuotientHaarMeasure F G Set.univ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  refine ⟨0, (b * normOneRationalQuotientHaarMeasure F G Set.univ).toNNReal,
    fun f hf hinv hbound => ?_⟩
  have hchamber : (1 : PositiveRealTorus.intrinsicSubgroup F T₀) ∈
      PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν 1 := by
    intro χ _
    change (1 : ℝ≥0ˣ) ≤ PositiveRealTorus.normCharacter F T₀ (j ≫ χ)
      ((1 : PositiveRealTorus.intrinsicSubgroup F T₀) : Lie.AffinePoints T₀.toGrp (Adeles F))
    rw [OneMemClass.coe_one, map_one]
  have h1 : f 1 ≤ b := hbound 1 1 ⟨1, Subgroup.one_mem _, 1, Set.mem_singleton _, 1,
    Set.mem_singleton _, hchamber, 1, Subgroup.one_mem _, 1, Set.mem_singleton _,
    Subsingleton.elim _ _⟩ (Subgroup.one_mem _)
  rw [ENNReal.coe_toNNReal hb]
  calc ∫⁻ y : NormOneRationalQuotient F G,
          f ((Quotient.out y : normOneSubgroup F G) : AdelicGroupPoints F G) *
            ENNReal.ofReal ((rationalLogHeight F G rho (normOneQuotientInclusion F G y) ^ 0)⁻¹)
          ∂(normOneRationalQuotientHaarMeasure F G)
        = ∫⁻ _y : NormOneRationalQuotient F G, f 1 ∂(normOneRationalQuotientHaarMeasure F G) := by
          refine lintegral_congr fun y => ?_
          rw [pow_zero, inv_one, ENNReal.ofReal_one, mul_one]
          exact congrArg f (Subsingleton.elim _ _)
      _ = f 1 * normOneRationalQuotientHaarMeasure F G Set.univ := lintegral_const _
      _ ≤ b * normOneRationalQuotientHaarMeasure F G Set.univ := by gcongr

end Main

end Langlands.Global.AdelicSiegelFactors

namespace Langlands.Global

/-- **Integrability of Siegel-dominated functions on the norm-one quotient, with the quotient
height as weight** (Delorme 2023, Proposition 3.5 (i) ⇒ (ii) with (2.5), (2.7)–(2.8), Lemma 2.1
and (2.10); Mœglin–Waldspurger I.2.2 (vii)). -/
theorem normOneSiegelDominatedIntegrability : NormOneSiegelDominatedIntegrabilityStatement := by
  intro F _ _ G _ _ _ hG N rho hrho
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact AdelicSiegelFactors.normOneSiegelDominatedIntegrability_of_zero hG rho hrho
  · exact AdelicSiegelFactors.normOneSiegelDominatedIntegrability_of_pos hG rho hN hrho

end Langlands.Global
