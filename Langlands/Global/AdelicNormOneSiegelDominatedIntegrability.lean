import Langlands.Global.AdelicSiegelDominatedIntegrabilityProof
import Langlands.Global.AdelicFullRationalQuotientProduct
import Langlands.Global.AdelicPrincipalQuotientProduct
import Langlands.Global.AdelicSiegelNormOne
import Langlands.Global.LeftCosetUnfoldingBound

/-! # Integrability of Siegel-dominated functions on the norm-one quotient

The norm-one form of `SiegelDominatedIntegrabilityStatement`: there are Siegel data and `d` such
that every measurable left `G(F)`-invariant `f ≥ 0` with `f(x) ≤ δ(a) σ(x)^{-d}` at the norm-one
points `x` of the Siegel set has finite integral over `G(F) \ G(𝔸)^1`. It follows from the proved
`siegelDominatedIntegrability` on `G(F) \ G(𝔸)` and the measure-preserving product decomposition
`A_G × G(F) \ G(𝔸)^1 ≅ G(F) \ G(𝔸)` (`PositiveRealTorus.measurePreserving_rationalQuotientDecomposition`). -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  AdelicSiegelFactors

/-- **Integrability of Siegel-dominated functions on the norm-one quotient** (the norm-one form
of `SiegelDominatedIntegrabilityStatement`, derived from Lapid 2013, §2, (2), (3) and (5), quoted
as Delorme 2023, (2.5)). For every number field `F`, connected reductive `G` and closed matrix
embedding `rho`, there are an algebraic Siegel setup, compact factors `C`, a threshold `t`, a
compact set `Ω` and `d : ℕ` such that every measurable left `G(F)`-invariant
`f : G(𝔸) → [0, ∞]` with `f(x) ≤ δ(a) / σ(x)^d` at every norm-one point `x` of the Siegel set
`A_G · Ω_N Ω_M A_{T₀}(t) K · Ω` with torus coordinate `a` has finite integral over
`G(F) \ G(𝔸)^1` for the norm-one quotient Haar measure, evaluated at the chosen
representatives. -/
def NormOneSiegelDecayIntegrabilityStatement : Prop :=
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
          IsSiegelPoint F G T i ν T₀ j C t Ω a x → x ∈ normOneSubgroup F G →
            f x ≤ ENNReal.ofReal
              (siegelModulus F G T i ν T₀ j a / adelicLogHeight F G rho x ^ d)) →
        ∫⁻ y : NormOneRationalQuotient F G,
            f ((Quotient.out y : normOneSubgroup F G) : AdelicGroupPoints F G)
          ∂(normOneRationalQuotientHaarMeasure F G) < ∞

section Proof

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}

/-- The logarithmic height is continuous. -/
theorem continuous_adelicLogHeight [IsAffineHom G.X.hom] [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] {N : ℕ} (rho : MatrixRepresentation G (Fin N)) :
    Continuous (adelicLogHeight F G rho) := by
  unfold adelicLogHeight
  exact continuous_const.add ((continuous_const.max (continuous_adelicSourceNorm rho)).log
    fun x => (lt_of_lt_of_le one_pos (le_max_left _ _)).ne')

/-- The logarithmic height is subadditive up to a constant: `σ(x y) ≤ σ(x) + σ(y) + L`. This is
the submultiplicativity `adelicHeight_mul_le` of the height after taking logarithms. -/
theorem exists_adelicLogHeight_mul_le_add [IsAffineHom G.X.hom] [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] {N : ℕ} (rho : MatrixRepresentation G (Fin N)) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : AdelicGroupPoints F G,
      adelicLogHeight F G rho (x * y) ≤
        adelicLogHeight F G rho x + adelicLogHeight F G rho y + L := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    refine ⟨0, le_rfl, fun x y => ?_⟩
    have h : adelicLogHeight F G rho (x * y) = adelicLogHeight F G rho y := by
      unfold adelicLogHeight RepresentationGrowth.adelicSourceNorm
      congr 3
    have := one_le_adelicLogHeight rho x
    linarith
  · set c : ℝ := (N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult) with hc
    have hc1 : 1 ≤ c := one_le_pow₀ (by exact_mod_cast hN)
    have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
    refine ⟨Real.log c, Real.log_nonneg hc1, fun x y => ?_⟩
    set S := RepresentationGrowth.adelicSourceNorm F G rho with hS
    have hH : ∀ g, RepresentationGrowth.adelicHeight F G rho g = c * S g := fun g =>
      RepresentationGrowth.adelicHeight_eq_scalar_mul_sourceNorm F G rho g
    have hmul := RepresentationGrowth.adelicHeight_mul_le F G rho hN x y
    rw [hH, hH, hH] at hmul
    have hSx := (RepresentationGrowth.adelicSourceNorm_pos F G rho hN x).le
    have hSy := (RepresentationGrowth.adelicSourceNorm_pos F G rho hN y).le
    have hSxy : S (x * y) ≤ c * (S x * S y) := by
      have : c * S (x * y) ≤ c * (c * (S x * S y)) := by nlinarith
      exact le_of_mul_le_mul_left this hc0
    have hmax : max 1 (S (x * y)) ≤ c * (max 1 (S x) * max 1 (S y)) := by
      have h1 : 1 ≤ max 1 (S x) := le_max_left _ _
      have h2 : 1 ≤ max 1 (S y) := le_max_left _ _
      have h3 : S x ≤ max 1 (S x) := le_max_right _ _
      have h4 : S y ≤ max 1 (S y) := le_max_right _ _
      refine max_le ?_ ?_
      · exact one_le_mul_of_one_le_of_one_le hc1 (one_le_mul_of_one_le_of_one_le h1 h2)
      · calc S (x * y) ≤ c * (S x * S y) := hSxy
          _ ≤ c * (max 1 (S x) * max 1 (S y)) := by gcongr
    have hpos : ∀ s : ℝ, 0 < max 1 s := fun s => lt_of_lt_of_le one_pos (le_max_left _ _)
    have hlog := Real.log_le_log (hpos _) hmax
    rw [Real.log_mul hc0.ne' (mul_pos (hpos _) (hpos _)).ne',
      Real.log_mul (hpos _).ne' (hpos _).ne'] at hlog
    unfold adelicLogHeight
    have h0 := Real.log_nonneg (le_max_left 1 (S x))
    linarith

/-- If `σ(x) ≤ S₀`, then `σ(x y) ≤ (S₀ + L + 1) σ(y)` for the constant `L` of
`exists_adelicLogHeight_mul_le_add`. -/
theorem adelicLogHeight_mul_le_of_le [IsAffineHom G.X.hom] [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] {N : ℕ} (rho : MatrixRepresentation G (Fin N)) {L S₀ : ℝ}
    (hL0 : 0 ≤ L) (hL : ∀ x y : AdelicGroupPoints F G,
      adelicLogHeight F G rho (x * y) ≤
        adelicLogHeight F G rho x + adelicLogHeight F G rho y + L)
    {x : AdelicGroupPoints F G} (hx : adelicLogHeight F G rho x ≤ S₀)
    (y : AdelicGroupPoints F G) :
    adelicLogHeight F G rho (x * y) ≤ (S₀ + L + 1) * adelicLogHeight F G rho y := by
  have hy := one_le_adelicLogHeight rho y
  have hx1 := one_le_adelicLogHeight rho x
  have h := hL x y
  nlinarith

end Proof

/-- **Integrability on the norm-one quotient.** The proof applies `siegelDominatedIntegrability`
to `x ↦ c 1_U(a(x)) f(n(x))`, where `x = a(x) n(x)` is the decomposition of `G(𝔸)` into the
positive points of the canonical central split torus and `G(𝔸)^1`, and `U` is a bounded open
neighbourhood of `1`; it then integrates out the central coordinate. -/
theorem normOneSiegelDecayIntegrability : NormOneSiegelDecayIntegrabilityStatement := by
  intro F _ _ G _ _ _ hG N rho hrho
  obtain ⟨T, i, ν, T₀, j, hset, C, t, Ω, d, hΩ, hint⟩ :=
    siegelDominatedIntegrability F G hG rho hrho
  -- the canonical central split torus and the norm-one decomposition
  have hs' := RestrictionSplitCentre.isSplitComponent_canonicalComponent F G
  have hi' : Function.Injective
      (characterRestrict (RestrictionSplitCentre.canonicalComponent F G)) :=
    RestrictionSplitCentre.canonical_characterRestrict_injective F G centralSplitTorusCharacter hG
  have := RestrictionSplitCentre.canonical_finiteIndex F G hG
  obtain ⟨I, hI, ⟨e⟩⟩ := hs'.1.1.1
  have : Fintype I := Fintype.ofFinite I
  have hc : IsCentral (RestrictionSplitCentre.canonicalComponent F G) := hs'.1.2
  let T' := RestrictionSplitCentre.canonicalTorus F G
  let i' := RestrictionSplitCentre.canonicalComponent F G
  let π := PositiveRealTorus.normOneProjection F G T' i' hi' I e hc
  let pf := PositiveRealTorus.positiveFactor F G T' i' hi' I e
  let pp := PositiveRealTorus.positivePointMap F G T' i'
  have hπcont : Continuous (fun w : AdelicGroupPoints F G => (π w : AdelicGroupPoints F G)) :=
    continuous_subtype_val.comp π.continuous
  refine ⟨T, i, ν, T₀, j, hset, C, t, (fun w => (π w : AdelicGroupPoints F G)) '' Ω, d,
    hΩ.image hπcont, ?_⟩
  intro f hf hfinv hfdom
  -- a bounded open neighbourhood of `1` in the positive central torus
  obtain ⟨L, hL0, hL⟩ := exists_adelicLogHeight_mul_le_add (F := F) (G := G) rho
  set S₀ : ℝ := adelicLogHeight F G rho 1 + 1 with hS₀
  set U : Set (PositiveRealTorus.intrinsicSubgroup F T') :=
    {a | adelicLogHeight F G rho (pp a) < S₀} with hU
  have hUopen : IsOpen U :=
    isOpen_lt ((continuous_adelicLogHeight rho).comp pp.continuous) continuous_const
  have h1U : (1 : PositiveRealTorus.intrinsicSubgroup F T') ∈ U := by
    change adelicLogHeight F G rho (pp 1) < S₀
    rw [map_one, hS₀]
    linarith
  set K₀ : ℝ := S₀ + L + 1 with hK₀
  have hS₀1 : 1 ≤ S₀ := by
    have := one_le_adelicLogHeight rho (1 : AdelicGroupPoints F G)
    linarith
  have hK₀pos : 0 < K₀ := by linarith
  set c : ℝ := (K₀ ^ d)⁻¹ with hcdef
  have hcpos : 0 < c := inv_pos.mpr (pow_pos hK₀pos d)
  -- the dominated function on `G(𝔸)`
  set F₁ : AdelicGroupPoints F G → ℝ≥0∞ := fun x =>
    U.indicator (fun _ => ENNReal.ofReal c) (pf x) * f (π x : AdelicGroupPoints F G) with hF₁
  have hUmeas : MeasurableSet U := hUopen.measurableSet
  have hF₁meas : Measurable F₁ :=
    ((measurable_const.indicator hUmeas).comp pf.continuous.measurable).mul
      (hf.comp hπcont.measurable)
  have hpfq : ∀ q ∈ rationalSubgroup F G, ∀ g : AdelicGroupPoints F G, pf (q * g) = pf g := by
    intro q hq g
    rw [map_mul]
    have : pf q = 1 := PositiveRealTorus.positiveFactor_normOne F G T' i' hi' I e
      ⟨q, rationalSubgroup_le_normOneSubgroup F G hq⟩
    rw [this, one_mul]
  have hπq : ∀ q ∈ rationalSubgroup F G, ∀ g : AdelicGroupPoints F G,
      (π (q * g) : AdelicGroupPoints F G) = q * π g := by
    intro q hq g
    rw [map_mul]
    have : π q = ⟨q, rationalSubgroup_le_normOneSubgroup F G hq⟩ :=
      PositiveRealTorus.normOneProjection_normOne F G T' i' hi' I e hc
        ⟨q, rationalSubgroup_le_normOneSubgroup F G hq⟩
    rw [this]
    rfl
  have hF₁inv : ∀ q ∈ rationalSubgroup F G, ∀ g : AdelicGroupPoints F G,
      F₁ (q * g) = F₁ g := by
    intro q hq g
    simp only [hF₁, hpfq q hq g, hπq q hq g, hfinv q hq]
  have hδnn : ∀ a : PositiveRealTorus.intrinsicSubgroup F T₀,
      0 ≤ siegelModulus F G T i ν T₀ j a := by
    intro a
    unfold siegelModulus
    exact finprod_nonneg fun β => finprod_nonneg fun _ => pow_nonneg (NNReal.coe_nonneg _) _
  have hF₁dom : ∀ (a : PositiveRealTorus.intrinsicSubgroup F T₀) (x : AdelicGroupPoints F G),
      IsSiegelPoint F G T i ν T₀ j C t Ω a x →
        F₁ x ≤ ENNReal.ofReal
          (siegelModulus F G T i ν T₀ j a / adelicLogHeight F G rho x ^ d) := by
    intro a x hx
    obtain ⟨z, hz, n, hn, m, hm, ha, k, hk, w, hw, rfl⟩ := hx
    set y := map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) n *
      map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m *
        positiveMap F G T i T₀ j a * k with hydef
    have hy : y ∈ normOneSubgroup F G :=
      hset.productSet_subset_normOne F G T i ν T₀ j C {a}
        ((mem_productSet_iff F G T i ν (canonicalStandardFactors F G T i ν) C T₀ j {a} y).mpr
          ⟨n, hn, m, hm, a, rfl, k, hk, rfl⟩)
    have hz' : z ∈ PositiveRealTorus.imageSubgroup F T' G i' := by
      rw [← RestrictionSplitCentre.canonicalSubgroup_eq_imageSubgroup F G]
      exact hz
    obtain ⟨t', ht', hzt⟩ := hz'
    have hzpp : z = pp ⟨t', ht'⟩ := hzt.symm
    have hπx : (π (z * y * w) : AdelicGroupPoints F G) = y * π w := by
      rw [map_mul, map_mul, hzpp,
        PositiveRealTorus.normOneProjection_positivePointMap F G T' i' hi' I e hc,
        show π y = ⟨y, hy⟩ from
          PositiveRealTorus.normOneProjection_normOne F G T' i' hi' I e hc ⟨y, hy⟩, one_mul]
      rfl
    by_cases hU' : pf (z * y * w) ∈ U
    · have hval : F₁ (z * y * w) = ENNReal.ofReal c * f (π (z * y * w) : AdelicGroupPoints F G) := by
        simp only [hF₁, Set.indicator_of_mem hU']
      rw [hval]
      -- the norm-one projection is a norm-one Siegel point
      have hsieg : IsSiegelPoint F G T i ν T₀ j C t
          ((fun w => (π w : AdelicGroupPoints F G)) '' Ω) a
          (π (z * y * w) : AdelicGroupPoints F G) := by
        refine ⟨1, (RestrictionSplitCentre.canonicalSubgroup F G).one_mem, n, hn, m, hm, ha, k, hk,
          π w, ⟨w, hw, rfl⟩, ?_⟩
        rw [hπx, one_mul]
      have hfb := hfdom a _ hsieg (π (z * y * w)).property
      -- heights
      have hdec : pp (pf (z * y * w)) * (π (z * y * w) : AdelicGroupPoints F G) = z * y * w :=
        PositiveRealTorus.positivePointMap_mul_normOneFactor F G T' i' hi' I e (z * y * w)
      have hσ : adelicLogHeight F G rho (z * y * w) ≤
          K₀ * adelicLogHeight F G rho (π (z * y * w) : AdelicGroupPoints F G) := by
        have h := adelicLogHeight_mul_le_of_le rho hL0 hL (le_of_lt hU')
          (π (z * y * w) : AdelicGroupPoints F G)
        rwa [hdec] at h
      set s := adelicLogHeight F G rho (π (z * y * w) : AdelicGroupPoints F G) with hs
      set sx := adelicLogHeight F G rho (z * y * w) with hsx
      have hs1 : 1 ≤ s := one_le_adelicLogHeight rho _
      have hsx1 : 1 ≤ sx := one_le_adelicLogHeight rho _
      have hδ := hδnn a
      calc ENNReal.ofReal c * f (π (z * y * w) : AdelicGroupPoints F G)
          ≤ ENNReal.ofReal c * ENNReal.ofReal (siegelModulus F G T i ν T₀ j a / s ^ d) :=
            by gcongr
        _ = ENNReal.ofReal (c * (siegelModulus F G T i ν T₀ j a / s ^ d)) :=
            (ENNReal.ofReal_mul hcpos.le).symm
        _ ≤ ENNReal.ofReal (siegelModulus F G T i ν T₀ j a / sx ^ d) := by
            apply ENNReal.ofReal_le_ofReal
            have hspos : 0 < s ^ d := pow_pos (by linarith) d
            have hsxpos : 0 < sx ^ d := pow_pos (by linarith) d
            have hpow : sx ^ d ≤ K₀ ^ d * s ^ d := by
              rw [← mul_pow]
              exact pow_le_pow_left₀ (by linarith) hσ d
            rw [hcdef, ← div_eq_inv_mul, div_div, div_le_div_iff₀ (by positivity) hsxpos]
            exact mul_le_mul_of_nonneg_left hpow hδ |>.trans_eq (by ring)
    · have hval : F₁ (z * y * w) = 0 := by
        simp only [hF₁, Set.indicator_of_notMem hU', zero_mul]
      rw [hval]
      exact bot_le
  have hlint := hint F₁ hF₁meas hF₁inv hF₁dom
  -- integrate out the central coordinate
  let μA := PositiveRealTorus.normalizedPositiveHaarMeasure F G T' i' hi' I e hc
  have : SigmaFinite μA :=
    PositiveRealTorus.normalizedPositiveHaarMeasure_sigmaFinite F G T' i' hi' I e hc
  have : IsFiniteMeasure (normOneRationalQuotientHaarMeasure F G) :=
    isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_connectedReductive F G hG
  have hQ := PositiveRealTorus.measurePreserving_rationalQuotientDecomposition F G T' i' hi' I e hc
  set Q := PositiveRealTorus.rationalQuotientDecomposition F G T' i' hi' I e hc with hQdef
  have hg : Measurable (fun y : RationalQuotient F G => F₁ y.out) :=
    LeftCosetSpace.measurable_comp_out _ hF₁meas hF₁inv
  have hcomp := hQ.lintegral_comp hg
  have hfq : Measurable (fun q : NormOneRationalQuotient F G =>
      f ((Quotient.out q : normOneSubgroup F G) : AdelicGroupPoints F G)) := by
    refine LeftCosetSpace.measurable_comp_out (rationalNormOneSubgroup F G)
      (f := fun n : normOneSubgroup F G => f (n : AdelicGroupPoints F G))
      (hf.comp measurable_subtype_coe) ?_
    intro r hr g
    have hr' : (r : AdelicGroupPoints F G) ∈ rationalSubgroup F G := by
      obtain ⟨q, hq⟩ := hr
      exact ⟨q, congrArg Subtype.val hq⟩
    exact hfinv _ hr' _
  have hpt : ∀ p : PositiveRealTorus.intrinsicSubgroup F T' × NormOneRationalQuotient F G,
      F₁ (Q p).out = U.indicator (fun _ => ENNReal.ofReal c) p.1 *
        f ((Quotient.out p.2 : normOneSubgroup F G) : AdelicGroupPoints F G) := by
    rintro ⟨a, q⟩
    have hq : q = LeftCosetSpace.mk (rationalNormOneSubgroup F G) (Quotient.out q) :=
      (Quotient.out_eq q).symm
    have hQa : Q (a, q) = LeftCosetSpace.mk (rationalSubgroup F G)
        (pp a * ((Quotient.out q : normOneSubgroup F G) : AdelicGroupPoints F G)) := by
      conv_lhs => rw [hq]
      exact PositiveRealTorus.rationalQuotientDecomposition_mk F G T' i' hi' I e hc a _
    rw [hQa, LeftCosetSpace.apply_out_mk _ hF₁inv]
    simp only [hF₁]
    rw [PositiveRealTorus.positiveFactor_mul_normOne F G T' i' hi' I e a (Quotient.out q),
      map_mul, PositiveRealTorus.normOneProjection_positivePointMap F G T' i' hi' I e hc,
      PositiveRealTorus.normOneProjection_normOne F G T' i' hi' I e hc, one_mul]
  have hprod : ∫⁻ p, F₁ (Q p).out ∂(μA.prod (normOneRationalQuotientHaarMeasure F G)) =
      (ENNReal.ofReal c * μA U) *
        ∫⁻ q : NormOneRationalQuotient F G,
          f ((Quotient.out q : normOneSubgroup F G) : AdelicGroupPoints F G)
          ∂(normOneRationalQuotientHaarMeasure F G) := by
    simp_rw [hpt]
    rw [lintegral_prod_mul ((measurable_const.indicator hUmeas).aemeasurable) hfq.aemeasurable,
      lintegral_indicator_const hUmeas]
  have hμU : μA U ≠ 0 := by
    have := PositiveRealTorus.normalizedPositiveHaarMeasure_isHaarMeasure F G T' i' hi' I e hc
    exact hUopen.measure_ne_zero μA ⟨1, h1U⟩
  have hX : ENNReal.ofReal c * μA U ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.mpr hcpos).ne' hμU
  have hfin : (ENNReal.ofReal c * μA U) *
      ∫⁻ q : NormOneRationalQuotient F G,
        f ((Quotient.out q : normOneSubgroup F G) : AdelicGroupPoints F G)
        ∂(normOneRationalQuotientHaarMeasure F G) < ∞ := by
    rw [← hprod, hcomp]
    exact hlint
  rcases ENNReal.mul_lt_top_iff.mp hfin with h | h | h
  · exact h.2
  · exact absurd h hX
  · rw [h]
    exact ENNReal.zero_lt_top

end Langlands.Global
