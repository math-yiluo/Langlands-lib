import Langlands.Global.AdelicLogSquareIntegrableSiegelDerivativeBounds
import Langlands.Global.AdelicWavePacketSiegelDecayReduction
import Langlands.Global.AdelicRelativeCuspidalConstantTerm
import Langlands.Global.ArthurTruncationAverage

/-! # Siegel chamber growth under constant-term averaging -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Filter
open scoped CategoryTheory.MonObj NNReal Pointwise

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme Automorphic.GroupSchemeFunctions AdelicGroupPoints AdelicSiegelFactors AdelicSubgroupPoints
open RepresentationGrowth

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)
  {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} (j : T₀ ⟶ fam.T)
  {N : ℕ} (rho : MatrixRepresentation G (Fin N))

local notation "A" => AdelicGroupPoints F G
local notation "Torus" => PositiveRealTorus.intrinsicSubgroup F T₀
local notation "aG" => positiveMap F G fam.T fam.i T₀ j
local notation "chamber" => PositiveRealTorus.weakSimpleRootChamber F T₀ fam.T j G fam.i fam.ν
local notation "δ" => siegelModulus F G fam.T fam.i fam.ν T₀ j
local notation "H" => adelicHeight F G rho
local notation "rad(" J ")" => SubgroupFunctor.range (fam.iU J ≫ fam.p J)

/-- The square root of the Siegel modulus times a power of `1 + log H(a)` bounds the
function on a positive chamber times any compact family of right factors. -/
def HasSiegelChamberGrowth (f : A → ℂ) : Prop :=
  ∀ (t : ℝ≥0ˣ) (Ω : Set A), IsCompact Ω →
    ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (a : Torus), a ∈ chamber t → ∀ w ∈ Ω,
      ‖f (aG a * w)‖ ≤ C * Real.sqrt (δ a) * (1 + Real.log (H (aG a))) ^ m

/-- Probability averaging of a left rational-invariant function along a standard unipotent
radical preserves the logarithmic Siegel chamber bound. -/
theorem hasSiegelChamberGrowth_constantTerm
    (hsetup : IsSiegelAlgebraicSetup F G fam.T fam.i fam.ν T₀ j) (hρ : IsClosedSubgroup rho)
    (J : StandardIndex F G fam.i fam.ν) {f : A → ℂ}
    (hf : fam.HasSiegelChamberGrowth j rho f)
    (hInv : ∀ q ∈ AdelicGroupPoints.rationalSubgroup F G, ∀ g, f (q * g) = f g) :
    fam.HasSiegelChamberGrowth j rho (fam.constantTerm J f) := by
  intro t Ω hΩ
  let U₀ := Standard.unipotentScheme fam.i fam.ν ∅
  let i₀ := Standard.unipotentHom fam.i fam.ν ∅
  have h₀ := Standard.isClosedSubgroup_unipotentHom fam.i fam.ν ∅
  have : IsAffine U₀.X.left := isAffine_left_of_isClosedSubgroup F i₀ h₀
  let V := adelicPoints F G (rad(J))
  let Γ := AdelicSubgroupPoints.rationalSubgroup F G (rad(J))
  let Q := RationalQuotient F G (rad(J))
  let : IsClosed (V : Set A) := isClosed_adelicPoints_range F G (fam.iU J ≫ fam.p J)
  let : CompactSpace Q := fam.compactSpace_radicalRationalQuotient J
  let mQ := normalizedRationalQuotientHaarMeasure F G (rad(J))
  let : IsProbabilityMeasure mQ := normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G (rad(J))
  obtain ⟨E, hE, hRep⟩ := ArthurTruncation.exists_compact_radical_representatives (F := F) (rad(J))
  have hle : V ≤ standardUnipotentImage F G fam.T fam.i fam.ν := by
    rw [AdelicSiegelFactors.standardUnipotentImage_eq]
    change (rad(J)).carrier _ ≤ (standardUnipotent fam.i fam.ν ∅).carrier _
    rw [fam.range_radical_eq_standardUnipotent J]
    exact (((standardParabolicOrder F G fam.connectedReductive fam.T fam.i fam.maximalSplit fam.ν
      fam.generic).1 ∅ J.val (Set.empty_subset _) J.property).2 (Set.empty_subset _)).2 _
  let e := rangeEquiv F i₀ (isClosedEmbedding_map_of_isClosedSubgroup F i₀ h₀).isEmbedding
  let b (u : V) : AdelicGroupPoints F U₀ := e.symm (Subgroup.inclusion hle u)
  have hb : Continuous b := e.symm.continuous.comp (continuous_subtype_val.subtype_mk _)
  have he (u : V) : map F U₀ G i₀ (b u) = u.val := by
    exact map_rangeEquiv_symm F i₀ _ (Subgroup.inclusion hle u)
  obtain ⟨E', hE', hConj⟩ := exists_isCompact_conj_unipotent fam.connectedReductive hsetup rho hρ
    (b '' E) (hE.image hb) t
  obtain ⟨m, C, hC, hBound⟩ := hf t (E' * Ω) (hE'.mul hΩ)
  refine ⟨m, C, hC, fun a ha w hw => ?_⟩
  let x := aG a * w
  let integrand : Q → ℂ := fun q => f ((Quotient.out q : V).val * x)
  let l : Q → ℂ := LeftCosetSpace.lift Γ (fun u : V => f (u.val * x)) (fun r u => by
    obtain ⟨r₀, hr₀⟩ := (mem_rationalSubgroup_range_iff (fam.iU J ≫ fam.p J) r.val).mp r.property
    change map F (fam.U J) G (fam.iU J ≫ fam.p J) (rational F (fam.U J) r₀) = r.val.val at hr₀
    change f ((r.val.val * u.val) * x) = f (u.val * x)
    rw [mul_assoc, ← hr₀]
    exact hInv _ (rationalImage_le_rationalSubgroup _ ⟨r₀, rfl⟩) _)
  change ‖∫ q, integrand q ∂mQ‖ ≤ _
  refine (norm_integral_le_of_norm_le_const
    (C := C * Real.sqrt (δ a) * (1 + Real.log (H (aG a))) ^ m)
    (Eventually.of_forall fun q => ?_)).trans_eq (by simp)
  obtain ⟨u, hu, hq⟩ := hRep q
  have hiq : integrand q = f (u.val * x) := by
    change l (LeftCosetSpace.mk Γ (Quotient.out q)) = l (LeftCosetSpace.mk Γ u)
    exact congrArg l ((Quotient.out_eq q).trans hq.symm)
  have hm : (aG a)⁻¹ * u.val * aG a ∈ E' := by
    have h := hConj (b u) ⟨u, hu, rfl⟩ a ha
    rwa [he u] at h
  rw [hiq]
  have hx : u.val * x = aG a * (((aG a)⁻¹ * u.val * aG a) * w) := by
    dsimp only [x]
    group
  rw [hx]
  exact hBound a ha _ (Set.mul_mem_mul hm hw)

/-- The derivative Siegel bound specializes to the logarithmic chamber bound on the
form itself. Compact right factors change the logarithmic height by a bounded amount. -/
theorem hasSiegelChamberGrowth_of_logSquareIntegrable
    (hSiegel : LogSquareIntegrableSiegelDerivativeBoundsStatement)
    (hsetup : IsSiegelAlgebraicSetup F G fam.T fam.i fam.ν T₀ j)
    (hN : 0 < N) (hρ : IsClosedSubgroup rho)
    {K : Subgroup A} (hK : IsMaximalCompactSubgroup F G K) (hIwa : IsIwasawaCompact (fam.p fam.bot) K)
    {d : ℕ} {hsmooth : SmoothOfRelativeDimension d G.X.hom}
    {hcalc : AdelicDifferentialCommutator F G hsmooth} {f : A → ℂ}
    (hf : IsLogSquareIntegrableAutomorphicForm F G K rho hsmooth hcalc f) :
    fam.HasSiegelChamberGrowth j rho f := by
  intro t Ω hΩ
  let c : CompactFactors F G (Standard.unipotentScheme fam.i fam.ν ∅)
      (Standard.leviScheme fam.i fam.ν ∅) :=
    ⟨{1}, {1}, isCompact_singleton, isCompact_singleton, ⊥,
      by simpa only [Subgroup.coe_bot] using (isCompact_singleton (x := (1 : A)))⟩
  obtain ⟨m, hD⟩ := hSiegel F G fam.connectedReductive K rho hsmooth hcalc hK hρ fam hIwa f hf
    fam.T fam.i fam.ν T₀ j hsetup c t Ω hΩ
  obtain ⟨C, hC, hBound⟩ := hD []
  obtain ⟨B₀, hB₀⟩ := (hΩ.image (continuous_adelicHeight F G rho hN)).bddAbove
  let B := max 1 B₀
  have h1B : 1 ≤ B := le_max_left _ _
  have hB (w : A) (hw : w ∈ Ω) : H w ≤ B := (hB₀ ⟨w, hw, rfl⟩).trans (le_max_right _ _)
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg h1B
  have hH (x : A) : 1 ≤ H x := one_le_adelicHeight F G rho hN x
  have hNH : 1 ≤ (N : ℝ) := by
    exact_mod_cast hN
  have hle (x : A) : adelicLogHeight F G rho x ≤ 1 + Real.log (H x) := by
    unfold adelicLogHeight
    apply add_le_add_right
    apply Real.log_le_log (zero_lt_one.trans_le (le_max_left _ _))
    apply max_le (hH x)
    rw [adelicHeight_eq_scalar_mul_sourceNorm]
    exact le_mul_of_one_le_left (adelicSourceNorm_pos F G rho hN x).le (one_le_pow₀ hNH)
  refine ⟨m, C * (1 + Real.log B) ^ m, mul_nonneg hC (pow_nonneg (by linarith) _), ?_⟩
  intro a ha w hw
  have hpoint : IsSiegelPoint F G fam.T fam.i fam.ν T₀ j c t Ω a (aG a * w) :=
    ⟨1, one_mem _, 1, Set.mem_singleton _, 1, Set.mem_singleton _, ha,
      1, one_mem _, w, hw, by simp⟩
  have hsig : adelicLogHeight F G rho (aG a * w) ≤
      (1 + Real.log B) * (1 + Real.log (H (aG a))) := by
    have hmul : H (aG a * w) ≤ H (aG a) * B :=
      (adelicHeight_mul_le F G rho hN _ _).trans
        (mul_le_mul_of_nonneg_left (hB w hw) (zero_le_one.trans (hH _)))
    have hlog := Real.log_le_log (zero_lt_one.trans_le (hH (aG a * w))) hmul
    rw [Real.log_mul (zero_lt_one.trans_le (hH _)).ne' (zero_lt_one.trans_le h1B).ne'] at hlog
    have hnonneg := mul_nonneg hlogB (Real.log_nonneg (hH (aG a)))
    linarith [hle (aG a * w)]
  calc
    ‖f (aG a * w)‖ ≤ C * Real.sqrt (δ a) * adelicLogHeight F G rho (aG a * w) ^ m := by
      simpa only [adelicIteratedDirectionalValue_nil] using hBound a _ hpoint
    _ ≤ C * Real.sqrt (δ a) * ((1 + Real.log B) * (1 + Real.log (H (aG a)))) ^ m :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀
        (zero_le_one.trans (one_le_adelicLogHeight rho _)) hsig _)
        (mul_nonneg hC (Real.sqrt_nonneg _))
    _ = _ := by rw [mul_pow]; ring

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

open GroupScheme Automorphic.GroupSchemeFunctions AdelicGroupPoints AdelicSiegelFactors

/-- The logarithmic Siegel estimate implies the same chamber growth rate for the
ordinary constant terms of the original weighted square-integrable form. -/
def AdelicSiegelConstantTermGrowthStatement : Prop :=
  LogSquareIntegrableSiegelDerivativeBoundsStatement →
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    ∀ (fam : StandardParabolicFamily F G)
      (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ fam.T),
      IsSiegelAlgebraicSetup F G fam.T fam.i fam.ν T₀ j →
    ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N)),
      0 < N → IsClosedSubgroup rho →
    ∀ (K : Subgroup (AdelicGroupPoints F G)),
      IsMaximalCompactSubgroup F G K → IsIwasawaCompact (fam.p fam.bot) K →
    ∀ (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth) (f : AdelicGroupPoints F G → ℂ),
      IsLogSquareIntegrableAutomorphicForm F G K rho hsmooth hcalc f →
    ∀ J : StandardIndex F G fam.i fam.ν,
      fam.HasSiegelChamberGrowth j rho (fam.constantTerm J f)

theorem adelicSiegelConstantTermGrowth : AdelicSiegelConstantTermGrowthStatement := by
  intro hSiegel F _ _ G _ _ _ fam T₀ j hsetup N d rho hN hρ K hK hIwa hsmooth hcalc f hf J
  exact fam.hasSiegelChamberGrowth_constantTerm j rho hsetup hρ J
    (fam.hasSiegelChamberGrowth_of_logSquareIntegrable j rho hSiegel hsetup hN hρ hK hIwa hf) hf.1.1

end Langlands.Global
