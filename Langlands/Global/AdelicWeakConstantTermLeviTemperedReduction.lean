import Langlands.Global.AdelicWeakConstantTermLeviEstimates
import Langlands.Global.AdelicLeadingCuspidalPairing
import Langlands.Global.InducedInnerProductSesquilinearProof

/-! # Weighted temperedness of weak constant terms from Siegel estimates on the Levi

Delorme 2023, Lemma 3.8 (ii) with Proposition 3.5 (i) ⇒ (ii) for the Levi subgroup, split into
two propositions on Siegel sets of the Levi `M = M_J` of a standard parabolic `P = P_J`:

* `WeakConstantTermLeviSiegelBoundStatement` (Delorme, Lemma 3.8 (ii), with Definition 3.3 and
  Lemma 3.2): a weak constant term `ψ = Φ_P^w` of a log-square-integrable automorphic form is
  bounded at `m w`, for norm-one points `m` of a Siegel set of `M` and `w` in a compact subset
  of `G(𝔸)`, by a constant times `δ_M(a)^{1/2} σ_M(m)^e`;
* `NormOneSiegelDominatedIntegrabilityStatement` (Delorme, (2.5), (2.7)–(2.8), Lemma 2.1 and
  (2.10), the integration step of Proposition 3.5 (i) ⇒ (ii)): on the norm-one quotient
  `G(F) \ G(𝔸)¹` of a connected reductive group, functions dominated by `δ(a) σ^d` on a Siegel
  set have uniformly bounded integrals against `σ_{[G]}^{-n}` for some `n`.

The theorem `weakConstantTermLeviTempered_of_siegel` derives
`WeakConstantTermLeviTemperedStatement` from the two, applying the second to the Levi `M` with
the restriction of `rho`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Filter MeasureTheory
open scoped CategoryTheory.MonObj ENNReal NNReal

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  AdelicSiegelFactors

/-- **Integrability of Siegel-dominated functions on the norm-one quotient, with the quotient
height as weight** (Delorme 2023, Proposition 3.5 (i) ⇒ (ii) with (2.5), (2.7)–(2.8), Lemma 2.1
and (2.10), on `[G]¹ = G(F) \ G(𝔸)¹`). For a connected reductive `G` over a number field and a
closed matrix embedding `rho`, there are an algebraic Siegel setup, compact factors `C`, a
threshold `t` and a compact set `Ω` such that for every `d` there are `n` and `B` with the
following property: every measurable left `G(F)`-invariant `f : G(𝔸) → [0, ∞]` with
`f(x) ≤ δ(a) σ(x)^d` at every norm-one point `x` of the Siegel set
`A_G · Ω_N Ω_M A_{T₀}(t) K · Ω` with torus coordinate `a` satisfies
`∫_{[G]¹} f(y) σ_{[G]}(y)^{-n} dy ≤ B`, for the quotient Haar measure of `[G]¹`. Here
`σ(x) = adelicLogHeight F G rho x` and `σ_{[G]} = rationalLogHeight F G rho`. -/
def NormOneSiegelDominatedIntegrabilityStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ {N : ℕ} (rho : MatrixRepresentation G (Fin N)), IsClosedSubgroup rho →
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
            ∂(normOneRationalQuotientHaarMeasure F G) ≤ B

/-- **Siegel bound for the weak constant term on the Levi** (Delorme 2023, Lemma 3.8 (ii), with
Definition 3.3 and condition c) of Lemma 3.2, on norm-one Siegel sets of the Levi subgroup). For a
log-square-integrable automorphic form `Φ` and a weak constant term `ψ = Φ_P^w` along
`P = P_J = M U`, and for every algebraic Siegel setup of `M`, compact factors, threshold, compact
set `Ω ⊆ M(𝔸)` and compact set `Ω' ⊆ G(𝔸)`, there are `e` and `B` with
`|ψ(m w)| ≤ B δ_M(a)^{1/2} σ_M(m)^e` for every norm-one point `m` of the Siegel set of `M` with
torus coordinate `a` and every `w ∈ Ω'`. Here `m` acts through the Levi embedding
`M → P → G`, `δ_M = siegelModulus` of the setup of `M`, and
`σ_M = adelicLogHeight` of `M` for the restriction of `rho` to `M`. -/
def WeakConstantTermLeviSiegelBoundStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
    IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ 𝓕 : StandardParabolicFamily F G, IsIwasawaCompact (𝓕.p 𝓕.bot) K →
    ∀ Φ : AdelicGroupPoints F G → ℂ,
    IsLogSquareIntegrableAutomorphicForm F G K rho hsmooth hcalc Φ →
    ∀ (J : StandardIndex F G 𝓕.i 𝓕.ν) (ψ : AdelicGroupPoints F G → ℂ),
    𝓕.IsWeakConstantTerm hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J Φ ψ →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ 𝓕.M J)
      (ν : cocharacterLattice T) (T₀ : CommGroupScheme (Spec (CommRingCat.of F)))
      (j : T₀ ⟶ T), IsSiegelAlgebraicSetup F (𝓕.M J) T i ν T₀ j →
    ∀ (C : CompactFactors F (𝓕.M J) (Standard.unipotentScheme i ν ∅)
        (Standard.leviScheme i ν ∅))
      (t : ℝ≥0ˣ) (Ω : Set (AdelicGroupPoints F (𝓕.M J))), IsCompact Ω →
    ∀ Ω' : Set (AdelicGroupPoints F G), IsCompact Ω' →
    ∃ (e : ℕ) (B : ℝ), ∀ (a : PositiveRealTorus.intrinsicSubgroup F T₀)
      (m : AdelicGroupPoints F (𝓕.M J)),
      IsSiegelPoint F (𝓕.M J) T i ν T₀ j C t Ω a m → m ∈ normOneSubgroup F (𝓕.M J) →
      ∀ w ∈ Ω',
        ‖ψ (map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J) m * w)‖ ≤
          B * Real.sqrt (siegelModulus F (𝓕.M J) T i ν T₀ j a) *
            adelicLogHeight F (𝓕.M J) (rho.restrict (𝓕.l J ≫ 𝓕.p J)) m ^ e

/-- The Siegel bound for the weak constant term on the Levi and the integrability of
Siegel-dominated functions on the norm-one Levi quotient imply the weighted temperedness of the
weak constant term on `K × M(F) \ M(𝔸)¹`. -/
theorem weakConstantTermLeviTempered_of_siegel
    (hT : WeakConstantTermLeviSiegelBoundStatement)
    (hI : NormOneSiegelDominatedIntegrabilityStatement) :
    WeakConstantTermLeviTemperedStatement := by
  intro F _ _ G _ _ _ hred K N d rho hsmooth hcalc hKmax hrho 𝓕 hK Φ hΦ J ψ hψ x hx
  have hM : IsConnectedReductive (𝓕.M J) := (𝓕.isCompatible J).levi.isConnectedReductive
  have hρM : IsClosedSubgroup (rho.restrict (𝓕.l J ≫ 𝓕.p J)) := by
    have h1 : IsClosedImmersion (𝓕.l J).hom.hom.left := (𝓕.isCompatible J).levi.isClosedSubgroup
    have h2 : IsClosedImmersion (𝓕.p J).hom.hom.left :=
      (𝓕.isCompatible J).parabolic.isClosedSubgroup
    have h3 : IsClosedImmersion rho.hom.hom.left := hrho
    change IsClosedImmersion ((𝓕.l J ≫ 𝓕.p J) ≫ rho).hom.hom.left
    simp only [Grp.comp_hom_hom, Over.comp_left]
    infer_instance
  obtain ⟨T, i, ν, T₀, j, hsetup, C, t, Ω, hΩ, hint⟩ := hI F (𝓕.M J) hM _ hρM
  -- the weak constant term is continuous and invariant under `U(𝔸) M(F)`
  obtain ⟨s, c, hdec, hψeq⟩ := hψ
  obtain ⟨S, hSs, hψfun⟩ : ∃ S : Finset (ComplexCharacterParameter F (𝓕.P J)), S ⊆ s ∧
      ψ = fun g => ∑ lam ∈ S, c lam g :=
    open Classical in
    ⟨s.filter (fun lam => parameterRealPart F (𝓕.P J) lam = 0), Finset.filter_subset _ _, by
      rw [hψeq]
      funext g
      simp only [StandardParabolicFamily.unitaryExponentSum, Finset.sum_apply]⟩
  have hψc : Continuous ψ := by
    rw [hψfun]
    exact continuous_finsetSum _ fun lam hlam => (hdec.automorphic lam (hSs hlam)).2.1.1
  have hψinv : ∀ g₀ ∈ parabolicQuotientSubgroup F (𝓕.p J) (𝓕.iU J) (𝓕.l J),
      ∀ g, ψ (g₀ * g) = ψ g := by
    intro g₀ hg₀ g
    rw [hψfun]
    exact Finset.sum_congr rfl fun lam hlam => (hdec.automorphic lam (hSs hlam)).1 g₀ hg₀ g
  -- notation
  set iM := map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J) with hiM
  set y : AdelicGroupPoints F G := map F (𝓕.P J) G (𝓕.p J) x with hy
  have hcomm (m : AdelicGroupPoints F (𝓕.M J)) : y * iM m = iM m * y :=
    (𝓕.commute_positiveSplitComponent_levi J ⟨x, hx⟩ m).eq
  -- invariance under the rational points of the Levi
  have hrat (r : RationalGroupPoints F (𝓕.M J)) (m : AdelicGroupPoints F (𝓕.M J))
      (g : AdelicGroupPoints F G) :
      ψ (y * iM (rational F (𝓕.M J) r * m) * g) = ψ (y * iM m * g) := by
    have hmem : iM (rational F (𝓕.M J) r) ∈
        parabolicQuotientSubgroup F (𝓕.p J) (𝓕.iU J) (𝓕.l J) :=
      Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨r, rfl⟩)
    rw [map_mul, ← mul_assoc, hcomm, mul_assoc, mul_assoc, hψinv _ hmem, ← mul_assoc]
  -- the Siegel data and the two estimates
  have hKc : IsCompact (K : Set (AdelicGroupPoints F G)) := hK.isCompact
  let Ω' : Set (AdelicGroupPoints F G) := (fun k => y * k) '' (K : Set (AdelicGroupPoints F G))
  have hΩ' : IsCompact Ω' := hKc.image (continuous_const.mul continuous_id)
  obtain ⟨e, B, hB⟩ := hT F G hred K rho hsmooth hcalc hKmax hrho 𝓕 hK Φ hΦ J ψ
    ⟨s, c, hdec, hψeq⟩ T i ν T₀ j hsetup C t Ω hΩ Ω' hΩ'
  obtain ⟨n, C₀, hC₀⟩ := hint (2 * e)
  refine ⟨n, ?_⟩
  -- the weight
  set σM : NormOneRationalQuotient F (𝓕.M J) → ℝ := fun q =>
    rationalLogHeight F (𝓕.M J) (rho.restrict (𝓕.l J ≫ 𝓕.p J))
      (normOneQuotientInclusion F (𝓕.M J) q) with hσM
  have hσ1 (q : NormOneRationalQuotient F (𝓕.M J)) : 1 ≤ σM q := one_le_rationalLogHeight _ _
  have hσmeas : Measurable σM :=
    (measurable_rationalLogHeight _).comp
      (continuous_normOneQuotientInclusion F (𝓕.M J)).measurable
  -- the numerator is continuous on `K × [M]¹`
  let f₀ : K × normOneSubgroup F (𝓕.M J) → ℂ := fun z =>
    ψ (y * iM (z.2 : AdelicGroupPoints F (𝓕.M J)) * (z.1 : AdelicGroupPoints F G))
  have hf₀c : Continuous f₀ :=
    hψc.comp ((continuous_const.mul ((map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)).continuous.comp
      (continuous_subtype_val.comp continuous_snd))).mul
        (continuous_subtype_val.comp continuous_fst))
  have hf₀inv : ∀ k, ∀ g₀ ∈ rationalNormOneSubgroup F (𝓕.M J), ∀ m,
      f₀ (k, g₀ * m) = f₀ (k, m) := by
    rintro k g₀ ⟨r, rfl⟩ m
    simp only [f₀, Subgroup.coe_mul, rationalNormOne_val]
    exact hrat r m k
  have hnum : Continuous (fun z : K × NormOneRationalQuotient F (𝓕.M J) => f₀ (z.1, z.2.out)) :=
    InducedInnerProductSesquilinear.continuous_prod_out _ f₀ hf₀c hf₀inv
  -- the integrand
  let h : K × NormOneRationalQuotient F (𝓕.M J) → ℂ := fun z =>
    f₀ (z.1, z.2.out) / ((σM z.2 : ℝ) : ℂ) ^ n
  change MemLp h 2 ((compactHaarProbability F G K hKc).prod
    (normOneRationalQuotientHaarMeasure F (𝓕.M J)))
  set μK := compactHaarProbability F G K hKc with hμK
  set μM := normOneRationalQuotientHaarMeasure F (𝓕.M J) with hμM
  have hmeas : AEStronglyMeasurable h (μK.prod μM) :=
    hnum.aestronglyMeasurable.div₀
      ((Complex.measurable_ofReal.comp (hσmeas.comp measurable_snd)).pow_const n).aestronglyMeasurable
  -- a positive constant for the Levi Siegel bound
  set B' : ℝ := max B 1 with hB'
  have hB'pos : 0 < B' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hinner : ∀ k : K,
      ∫⁻ q, ENNReal.ofReal (‖h (k, q)‖ ^ 2) ∂μM ≤ ENNReal.ofReal (B' ^ 2) * C₀ := by
    intro k
    let fk : AdelicGroupPoints F (𝓕.M J) → ℝ≥0∞ := fun m =>
      ENNReal.ofReal (‖ψ (y * iM m * (k : AdelicGroupPoints F G))‖ ^ 2 / B' ^ 2)
    have hfk_meas : Measurable fk := by
      apply ENNReal.measurable_ofReal.comp
      apply Continuous.measurable
      exact ((hψc.comp ((continuous_const.mul
        (map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)).continuous).mul continuous_const)).norm.pow 2).div_const _
    have hfk_inv : ∀ q ∈ rationalSubgroup F (𝓕.M J), ∀ g, fk (q * g) = fk g := by
      rintro q ⟨r, rfl⟩ g
      simp only [fk, hrat r g k]
    have hfk_bound : ∀ (a : PositiveRealTorus.intrinsicSubgroup F T₀)
        (m : AdelicGroupPoints F (𝓕.M J)), IsSiegelPoint F (𝓕.M J) T i ν T₀ j C t Ω a m →
        m ∈ normOneSubgroup F (𝓕.M J) →
        fk m ≤ ENNReal.ofReal (siegelModulus F (𝓕.M J) T i ν T₀ j a *
          adelicLogHeight F (𝓕.M J) (rho.restrict (𝓕.l J ≫ 𝓕.p J)) m ^ (2 * e)) := by
      intro a m hpt hm
      have h1 := hB a m hpt hm (y * k) ⟨k, k.2, rfl⟩
      rw [← mul_assoc, ← hcomm] at h1
      apply ENNReal.ofReal_le_ofReal
      have hδ : 0 ≤ siegelModulus F (𝓕.M J) T i ν T₀ j a :=
        finprod_nonneg fun β => finprod_nonneg fun _ => pow_nonneg (NNReal.coe_nonneg _) _
      have hσ0 : 0 ≤ adelicLogHeight F (𝓕.M J) (rho.restrict (𝓕.l J ≫ 𝓕.p J)) m :=
        zero_le_one.trans (one_le_adelicLogHeight _ _)
      have hX : 0 ≤ Real.sqrt (siegelModulus F (𝓕.M J) T i ν T₀ j a) *
          adelicLogHeight F (𝓕.M J) (rho.restrict (𝓕.l J ≫ 𝓕.p J)) m ^ e :=
        mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hσ0 _)
      have h2 : ‖ψ (y * iM m * (k : AdelicGroupPoints F G))‖ ≤
          B' * (Real.sqrt (siegelModulus F (𝓕.M J) T i ν T₀ j a) *
            adelicLogHeight F (𝓕.M J) (rho.restrict (𝓕.l J ≫ 𝓕.p J)) m ^ e) := by
        calc ‖ψ (y * iM m * (k : AdelicGroupPoints F G))‖
            ≤ B * Real.sqrt (siegelModulus F (𝓕.M J) T i ν T₀ j a) *
                adelicLogHeight F (𝓕.M J) (rho.restrict (𝓕.l J ≫ 𝓕.p J)) m ^ e := h1
          _ = B * (Real.sqrt (siegelModulus F (𝓕.M J) T i ν T₀ j a) *
                adelicLogHeight F (𝓕.M J) (rho.restrict (𝓕.l J ≫ 𝓕.p J)) m ^ e) := by ring
          _ ≤ B' * (Real.sqrt (siegelModulus F (𝓕.M J) T i ν T₀ j a) *
                adelicLogHeight F (𝓕.M J) (rho.restrict (𝓕.l J ≫ 𝓕.p J)) m ^ e) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hX
      rw [div_le_iff₀ (by positivity)]
      calc ‖ψ (y * iM m * (k : AdelicGroupPoints F G))‖ ^ 2
          ≤ (B' * (Real.sqrt (siegelModulus F (𝓕.M J) T i ν T₀ j a) *
              adelicLogHeight F (𝓕.M J) (rho.restrict (𝓕.l J ≫ 𝓕.p J)) m ^ e)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h2 2
        _ = siegelModulus F (𝓕.M J) T i ν T₀ j a *
              adelicLogHeight F (𝓕.M J) (rho.restrict (𝓕.l J ≫ 𝓕.p J)) m ^ (2 * e) * B' ^ 2 := by
            rw [mul_pow, mul_pow, Real.sq_sqrt hδ, ← pow_mul]
            ring
    have hk := hC₀ fk hfk_meas hfk_inv hfk_bound
    calc ∫⁻ q, ENNReal.ofReal (‖h (k, q)‖ ^ 2) ∂μM
        ≤ ∫⁻ q, ENNReal.ofReal (B' ^ 2) *
            (fk ((Quotient.out q : normOneSubgroup F (𝓕.M J)) : AdelicGroupPoints F (𝓕.M J)) *
              ENNReal.ofReal ((σM q ^ n)⁻¹)) ∂μM := by
          apply lintegral_mono
          intro q
          have hS : 1 ≤ σM q ^ n := one_le_pow₀ (hσ1 q)
          have hSpos : 0 < σM q ^ n := lt_of_lt_of_le one_pos hS
          show ENNReal.ofReal (‖h (k, q)‖ ^ 2) ≤ ENNReal.ofReal (B' ^ 2) *
            (ENNReal.ofReal (‖ψ (y * iM ((Quotient.out q : normOneSubgroup F (𝓕.M J)) :
                AdelicGroupPoints F (𝓕.M J)) * (k : AdelicGroupPoints F G))‖ ^ 2 / B' ^ 2) *
              ENNReal.ofReal ((σM q ^ n)⁻¹))
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          have hnorm : ‖h (k, q)‖ =
              ‖ψ (y * iM ((Quotient.out q : normOneSubgroup F (𝓕.M J)) :
                AdelicGroupPoints F (𝓕.M J)) * (k : AdelicGroupPoints F G))‖ / σM q ^ n := by
            simp only [h, f₀, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (zero_le_one.trans (hσ1 q))]
          have hB'2 : B' ^ 2 ≠ 0 := pow_ne_zero 2 hB'pos.ne'
          have hcancel : ∀ A : ℝ, B' ^ 2 * (A / B' ^ 2 * (σM q ^ n)⁻¹) = A / σM q ^ n := by
            intro A
            field_simp
          rw [hnorm, div_pow, hcancel]
          exact div_le_div_of_nonneg_left (sq_nonneg _) hSpos (by nlinarith)
      _ = ENNReal.ofReal (B' ^ 2) *
            ∫⁻ q, fk ((Quotient.out q : normOneSubgroup F (𝓕.M J)) :
                AdelicGroupPoints F (𝓕.M J)) * ENNReal.ofReal ((σM q ^ n)⁻¹) ∂μM :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (B' ^ 2) * C₀ := by gcongr
  have hlint : ∫⁻ z, ENNReal.ofReal (‖h z‖ ^ 2) ∂(μK.prod μM) < ∞ := by
    calc ∫⁻ z, ENNReal.ofReal (‖h z‖ ^ 2) ∂(μK.prod μM)
        ≤ ∫⁻ k, ∫⁻ q, ENNReal.ofReal (‖h (k, q)‖ ^ 2) ∂μM ∂μK := lintegral_prod_le _
      _ ≤ ∫⁻ _k, ENNReal.ofReal (B' ^ 2) * C₀ ∂μK := lintegral_mono hinner
      _ = ENNReal.ofReal (B' ^ 2) * C₀ := by rw [lintegral_const, measure_univ, mul_one]
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.coe_lt_top
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  refine ⟨hmeas.norm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z => sq_nonneg _)]
  exact hlint

end Langlands.Global
