import Langlands.Global.AdelicSiegelConstantTermGrowth
import Langlands.Global.AdelicSiegelOrbitGrowth
import Langlands.Global.AdelicConstantTermDirectionalGrowth
import Langlands.Global.AdelicConstantTermComposition
import Langlands.Global.AdelicParabolicConstantTermAutomorphy
import Langlands.Global.AdelicParabolicConstantTermGrowth
import Langlands.Global.AdelicSiegelWeightedAverage
import Langlands.Global.AdelicLeadingCuspidalInjectivityReduction
import Langlands.Automorphic.GroupSchemeManifoldSmooth
import Langlands.AlgebraicGeometry.SmoothConnectedRelativeDimensionProof

/-! # Siegel root decay with a vanishing maximal constant term -/

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Manifold ContDiff NNReal

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme AdelicGroupPoints InfiniteAdelicGroupPoints AdelicSiegelFactors PositiveRealTorus
  Automorphic.GroupSchemeFunctions RepresentationGrowth

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)
  {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} (j : T₀ ⟶ fam.T)
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)

local notation "A" => AdelicGroupPoints F G
local notation "G∞" => InfiniteAdelicGroupPoints F G
local notation "Gf" => FiniteAdelicGroupPoints F G
local notation "W" => smoothModel F d
local notation "IG" => 𝓘(ℝ, W)
local notation "IC" => 𝓘(ℝ, ℂ)
local notation "aG" => positiveMap F G fam.T fam.i T₀ j
local notation "chamber" => weakSimpleRootChamber F T₀ fam.T j G fam.i fam.ν
local notation "Torus" => intrinsicSubgroup F T₀
local notation "δ" => siegelModulus F G fam.T fam.i fam.ν T₀ j
local notation "H" => adelicHeight F G rho
local notation "D" => adelicDirectionalValue hsmooth

/-- On a chamber times compact right factors, the weighted derivative bound
gives the same Siegel bound with the height evaluated on the torus coordinate. -/
theorem hasSiegelChamberGrowth_iteratedDirectionalValue
    (hSiegel : LogSquareIntegrableSiegelDerivativeBoundsStatement)
    (hsetup : IsSiegelAlgebraicSetup F G fam.T fam.i fam.ν T₀ j)
    (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    {K : Subgroup A} (hK : IsMaximalCompactSubgroup F G K) (hIwa : IsIwasawaCompact (fam.p fam.bot) K)
    {hcalc : AdelicDifferentialCommutator F G hsmooth} {f : A → ℂ}
    (hf : IsLogSquareIntegrableAutomorphicForm F G K rho hsmooth hcalc f)
    (s : List W) :
    fam.HasSiegelChamberGrowth j rho (adelicIteratedDirectionalValue hsmooth s f) := by
  intro t Ω hΩ
  let c : CompactFactors F G (Standard.unipotentScheme fam.i fam.ν ∅)
      (Standard.leviScheme fam.i fam.ν ∅) :=
    ⟨{1}, {1}, isCompact_singleton, isCompact_singleton, ⊥,
      by simpa only [Subgroup.coe_bot] using (isCompact_singleton (x := (1 : A)))⟩
  obtain ⟨m, hD⟩ := hSiegel F G fam.connectedReductive K rho hsmooth hcalc hK hrho fam hIwa f hf
    fam.T fam.i fam.ν T₀ j hsetup c t Ω hΩ
  obtain ⟨C, hC, hBound⟩ := hD s
  obtain ⟨L, hL⟩ := (hΩ.image (continuous_adelicHeight F G rho hN)).bddAbove
  let L₀ := max 1 L
  have hL₀ : 1 ≤ L₀ := le_max_left _ _
  have hlogL : 0 ≤ Real.log L₀ := Real.log_nonneg hL₀
  have hH (x : A) : 1 ≤ H x := one_le_adelicHeight F G rho hN x
  have hNH : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hσ (x : A) : adelicLogHeight F G rho x ≤ 1 + Real.log (H x) := by
    unfold adelicLogHeight
    apply add_le_add_right
    apply Real.log_le_log (zero_lt_one.trans_le (le_max_left _ _))
    apply max_le (hH x)
    rw [adelicHeight_eq_scalar_mul_sourceNorm]
    exact le_mul_of_one_le_left (adelicSourceNorm_pos F G rho hN x).le (one_le_pow₀ hNH)
  refine ⟨m, C * (1 + Real.log L₀) ^ m, mul_nonneg hC (pow_nonneg (by linarith) _), ?_⟩
  intro a ha w hw
  have hpoint : IsSiegelPoint F G fam.T fam.i fam.ν T₀ j c t Ω a (aG a * w) :=
    ⟨1, one_mem _, 1, Set.mem_singleton _, 1, Set.mem_singleton _, ha,
      1, one_mem _, w, hw, by simp⟩
  have hHw : H w ≤ L₀ := (hL ⟨w, hw, rfl⟩).trans (le_max_right _ _)
  have hHa : 0 < H (aG a) := zero_lt_one.trans_le (hH _)
  have hmul := (adelicHeight_mul_le F G rho hN (aG a) w).trans
    (mul_le_mul_of_nonneg_left hHw hHa.le)
  have hlog := Real.log_le_log (zero_lt_one.trans_le (hH _)) hmul
  rw [Real.log_mul hHa.ne' (zero_lt_one.trans_le hL₀).ne'] at hlog
  have hBoundLog : adelicLogHeight F G rho (aG a * w) ≤
      (1 + Real.log L₀) * (1 + Real.log (H (aG a))) := by
    nlinarith [hσ (aG a * w), mul_nonneg hlogL (Real.log_nonneg (hH (aG a)))]
  calc
    ‖adelicIteratedDirectionalValue hsmooth s f (aG a * w)‖ ≤
        C * Real.sqrt (δ a) * adelicLogHeight F G rho (aG a * w) ^ m :=
      hBound a _ hpoint
    _ ≤ C * Real.sqrt (δ a) * ((1 + Real.log L₀) * (1 + Real.log (H (aG a)))) ^ m :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (zero_le_one.trans (one_le_adelicLogHeight rho _)) hBoundLog _)
        (mul_nonneg hC (Real.sqrt_nonneg _))
    _ = _ := by rw [mul_pow]; ring

/-- One right-orbit derivative gains one inverse power of the distinguished
archimedean root scalar when the maximal constant term vanishes. -/
theorem exists_siegelRootDecay_of_maximalConstantTerm_eq_zero
    (hsetup : IsSiegelAlgebraicSetup F G fam.T fam.i fam.ν T₀ j) (hN : 0 < N)
    (α : simpleRelativeRoots fam.i fam.ν) {f : A → ℂ}
    (hf : IsAdelicSmoothFunction F G f)
    (hInv : ∀ (u : RationalGroupPoints F (fam.U (fam.omitSimpleRoot α.val))) x,
      f (map F (fam.U (fam.omitSimpleRoot α.val)) G
        (fam.iU (fam.omitSimpleRoot α.val) ≫ fam.p (fam.omitSimpleRoot α.val)) (rational F _ u) * x) = f x)
    (hZero : fam.constantTerm (fam.omitSimpleRoot α.val) f = 0)
    (hGrowth : ∀ X : W, fam.HasSiegelChamberGrowth j rho (D X f))
    (t : ℝ≥0ˣ) (Ω : Set A) (hΩ : IsCompact Ω) :
    ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (a : Torus), a ∈ chamber t → ∀ w ∈ Ω,
      ‖f (aG a * w)‖ ≤
        C * Real.sqrt (δ a) * (1 + Real.log (H (aG a))) ^ m * relativeCharacterDecay j α.val a := by
  classical
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let M := fam.omitSimpleRoot α.val
  let p := fam.iU M ≫ fam.p M
  have hp : IsClosedSubgroup p :=
    (fam.isUnipotentRadical M).1.isClosedSubgroup.comp (fam.isCompatible M).parabolic.isClosedSubgroup
  let : IsClosedImmersion p.hom.hom.left := hp
  let : IsAffine (fam.U M).X.left := isAffine_left_of_isClosedSubgroup F p hp
  obtain ⟨dU, hU⟩ := Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension
    (fam.U M).X.left _ (fam.U M).X.hom (fam.isUnipotentRadical M).1.smooth
    (fam.isUnipotentRadical M).1.connectedSpace
  have hT₀ : IsSplitTorus T₀.toGrp := by
    obtain ⟨_, _, _, _, _, _, _, ⟨_, _, _, _, hT₀, _⟩, _⟩ := hsetup
    exact hT₀.isSplitSubtorus.1
  obtain ⟨L, hLo, hL⟩ := hf.2.2
  let Yf := finite F G '' Ω
  obtain ⟨Ω', hΩ', _hSub, C₀, hC₀, hDecay⟩ := adelicMaximalUnipotentDecay hsmooth
    (dU := dU) fam.i fam.ν j p fam.connectedReductive fam.maximalSplit fam.generic hU
    (fam.isUnipotentRadical M).1.connectedSpace (fam.isUnipotentRadical M).1.isUnipotent
    α.val α.property (fam.range_radical_eq_standardUnipotent M) {1} isCompact_singleton
    (by simp)
    Yf (hΩ.image (finite F G).continuous) L hLo t 1 Ω hΩ
  let I := Fin (Module.finrank ℝ W)
  let basis := Module.finBasis ℝ W
  choose m C hC hBound using fun k : I => hGrowth (basis k) t Ω' hΩ'
  let degree := Finset.univ.sup m
  let B := ∑ k, C k
  have hB : 0 ≤ B := Finset.sum_nonneg (fun k _ => hC k)
  refine ⟨degree, C₀ * B, mul_nonneg hC₀ hB, fun a ha w hw => ?_⟩
  let S := 1 + Real.log (H (aG a))
  have hS : 1 ≤ S := le_add_of_nonneg_right (Real.log_nonneg (one_le_adelicHeight F G rho hN _))
  have hM := hDecay 1 (Set.mem_singleton _) a ha w hw
    (by simpa only [one_mul, map_mul, finite_positiveMap F G fam.T fam.i T₀ j hT₀ a, one_mul]
        using (Set.mem_image_of_mem (finite F G) hw : finite F G w ∈ Yf))
    f hf.1 (fun b => (isPlotSmooth_iff_contMDiff F G hsmooth _).mp (hf.2.1 b))
    hInv hL hZero (B * Real.sqrt (δ a) * S ^ degree)
    (mul_nonneg (mul_nonneg hB (Real.sqrt_nonneg _)) (pow_nonneg (zero_le_one.trans hS) _))
    (fun w' hw' _ s hs => ?_)
  · simp only [one_mul, pow_one] at hM
    change ‖f (aG a * w)‖ ≤ C₀ * B * Real.sqrt (δ a) * S ^ degree * relativeCharacterDecay j α.val a
    exact hM.trans_eq (by ring)
  · obtain ⟨k, rfl⟩ := List.length_eq_one_iff.mp hs
    simp only [one_mul, List.map_cons, List.map_nil, adelicIteratedDirectionalValue_cons,
      adelicIteratedDirectionalValue_nil]
    refine (hBound k a ha w' hw').trans ?_
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun k _ => hC k) (Finset.mem_univ k)) (Real.sqrt_nonneg _))
      (pow_le_pow_right₀ hS (Finset.le_sup (f := m) (Finset.mem_univ k)))
      (pow_nonneg (zero_le_one.trans hS) _) (mul_nonneg hB (Real.sqrt_nonneg _))

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
private theorem directionalValue_sub {f g : A → ℂ}
    (hf : IsAdelicSmoothFunction F G f) (hg : IsAdelicSmoothFunction F G g) (X : W) :
    D X (f - g) = D X f - D X g := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  funext x
  let ψ₁ (y : G∞) := f (x * ofInfinite F G y)
  let ψ₂ (y : G∞) := g (x * ofInfinite F G y)
  have hs {h : A → ℂ} (hh : IsAdelicSmoothFunction F G h) :
      ContMDiff IG IC ∞ (fun y : G∞ => h (x * ofInfinite F G y)) := by
    conv in x * ofInfinite F G _ => rw [← pair_projections F G x, ofInfinite_eq_pair, pair_mul, mul_one]
    have h₁ := (isPlotSmooth_iff_contMDiff F G hsmooth _).mp (hh.2.1 (finite F G x))
    exact h₁.comp (contMDiff_const.mul contMDiff_id)
  change mvfderiv IG (ψ₁ - ψ₂) 1 X = (mvfderiv IG ψ₁ 1 - mvfderiv IG ψ₂ 1) X
  rw [mvfderiv_sub ((hs hf).mdifferentiableAt (by simp)) ((hs hg).mdifferentiableAt (by simp))]

/-- Under the weighted derivative bound, the difference of the input from its maximal
ordinary constant term has the corresponding one-root gain. -/
theorem exists_siegelRootDecay_weightedRemainder
    (hSiegel : LogSquareIntegrableSiegelDerivativeBoundsStatement)
    (hsetup : IsSiegelAlgebraicSetup F G fam.T fam.i fam.ν T₀ j) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    {K : Subgroup A} (hK : IsMaximalCompactSubgroup F G K) (hIwa : IsIwasawaCompact (fam.p fam.bot) K)
    {hcalc : AdelicDifferentialCommutator F G hsmooth} {f : A → ℂ}
    (hf : IsLogSquareIntegrableAutomorphicForm F G K rho hsmooth hcalc f)
    (α : simpleRelativeRoots fam.i fam.ν)
    (hAut : fam.IsAutomorphicOn hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho
      (fam.omitSimpleRoot α.val) (fam.constantTerm (fam.omitSimpleRoot α.val) f))
    (t : ℝ≥0ˣ) (Ω : Set A) (hΩ : IsCompact Ω) :
    ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (a : Torus), a ∈ chamber t → ∀ w ∈ Ω,
      ‖(f - fam.constantTerm (fam.omitSimpleRoot α.val) f) (aG a * w)‖ ≤
        C * Real.sqrt (δ a) * (1 + Real.log (H (aG a))) ^ m * relativeCharacterDecay j α.val a := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let M := fam.omitSimpleRoot α.val
  let p := fam.iU M ≫ fam.p M
  have hp : IsClosedSubgroup p :=
    (fam.isUnipotentRadical M).1.isClosedSubgroup.comp (fam.isCompatible M).parabolic.isClosedSubgroup
  let : IsClosedImmersion p.hom.hom.left := hp
  let : IsAffine (fam.U M).X.left := isAffine_left_of_isClosedSubgroup F p hp
  let g := fam.constantTerm M f
  have hfS : IsAdelicSmoothFunction F G f := hf.1.2.1
  have hgS : IsAdelicSmoothFunction F G g := hAut.2.1
  have hgR := fam.isLeftInvariantUnder_rationalImage_of_le (Q := M) le_rfl hAut.1
  obtain ⟨L, hLo, hL⟩ := hfS.2.2
  obtain ⟨L', hLo', hL'⟩ := hgS.2.2
  have hSmooth : IsAdelicSmoothFunction F G (f - g) := by
    refine ⟨hfS.1.sub hgS.1, fun b =>
      (InfinitePlotSmoothFunctions F G).sub_mem (hfS.2.1 b) (hgS.2.1 b),
      L ⊓ L', hLo.inter hLo', fun l hl x => ?_⟩
    exact congrArg₂ (· - ·) (hL l hl.1 x) (hL' l hl.2 x)
  have hR (u : RationalGroupPoints F (fam.U M)) (x : A) :
      f (map F (fam.U M) G p (rational F _ u) * x) = f x :=
    hf.1.1 _ (rationalImage_le_rationalSubgroup p ((mem_rationalImage_iff p _).mpr ⟨u, rfl⟩)) x
  have hRg (u : RationalGroupPoints F (fam.U M)) (x : A) :
      g (map F (fam.U M) G p (rational F _ u) * x) = g x :=
    hgR _ (rationalImage_comp_le _ _ ((mem_rationalImage_iff p _).mpr ⟨u, rfl⟩)) x
  refine fam.exists_siegelRootDecay_of_maximalConstantTerm_eq_zero j rho hsmooth
    hsetup hN α hSmooth (fun u x => congrArg₂ (· - ·) (hR u x) (hRg u x)) ?_ ?_ t Ω hΩ
  · let fC : ContinuousRationalFunctions F G := ⟨⟨f, fun u x => hf.1.1 _ ⟨u, rfl⟩ x⟩, hfS.1⟩
    have hc : fam.constantTerm M g = g := by
      have hi : fam.interIndex M M = M := Subtype.ext (Set.inter_self _)
      exact (fam.constantTerm_constantTerm M M fC).trans (by rw [hi]; rfl)
    have hTop : fam.IsAutomorphicOn hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho fam.top f :=
      (fam.isWeakConstantTerm_top hf).isAutomorphicOn
    rw [fam.constantTerm_sub_of_integrable
      (fam.integrable_constantTermIntegrand_of_le fam.top M (fam.le_top M) hfS.1 hTop.1)
      (fam.integrable_constantTermIntegrand_of_le M M le_rfl hgS.1 hAut.1), hc, sub_self]
  · intro X
    have hD : fam.HasSiegelChamberGrowth j rho (D X f) := by
      simpa only [adelicIteratedDirectionalValue_cons, adelicIteratedDirectionalValue_nil] using
        fam.hasSiegelChamberGrowth_iteratedDirectionalValue j rho hsmooth hSiegel hsetup hN hrho hK hIwa hf [X]
    have hInvD (q : A) (hq : q ∈ rationalSubgroup F G) (x : A) : D X f (q * x) = D X f x := by
      have he : (fun y : G∞ => f ((q * x) * ofInfinite F G y)) =
          fun y => f (x * ofInfinite F G y) := by
        funext y
        exact (congrArg f (mul_assoc q x _)).trans (hf.1.1 q hq _)
      unfold adelicDirectionalValue
      rw [he]
    have hCTD := fam.hasSiegelChamberGrowth_constantTerm j rho hsetup hrho M hD hInvD
    have hCom (x : A) : D X g x = fam.constantTerm M (D X f) x := by
      have hDiff := adelicUnipotentConstantTermDifferentiation p hsmooth
        (fam.isUnipotentRadical M).1.smooth (fam.isUnipotentRadical M).1.connectedSpace
        (fam.isUnipotentRadical M).1.isUnipotent L hLo f hfS.1
        (fun b => (isPlotSmooth_iff_contMDiff F G hsmooth _).mp (hfS.2.1 b)) hR hL
      have h := (hDiff.2 (finite F G x)).2 X (infinite F G x)
      rw [← adelicDirectionalValue_pair] at h
      change D X (subgroupConstantTerm F p f) x = subgroupConstantTerm F p (D X f) x
      simpa only [pair_projections] using h
    rw [directionalValue_sub hsmooth hfS hgS X, funext hCom]
    exact (fam.siegelChamberGrowthSubmodule j rho hN).sub_mem hD hCTD

variable (J : StandardIndex F G fam.i fam.ν)

/-- Ordinary constant-term composition and split-component shifts transfer the maximal
remainder estimate of the weighted input to the weak-term orbit in the Levi. -/
theorem hasWeightedSiegelChamberGrowth_relativeRemainder
    (hSiegel : LogSquareIntegrableSiegelDerivativeBoundsStatement)
    (hsetup : IsSiegelAlgebraicSetup F G fam.T fam.i fam.ν T₀ j) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    {K : Subgroup A} (hK : IsMaximalCompactSubgroup F G K) (hIwa : IsIwasawaCompact (fam.p fam.bot) K)
    {hcalc : AdelicDifferentialCommutator F G hsmooth} {f w : A → ℂ}
    (hf : IsLogSquareIntegrableAutomorphicForm F G K rho hsmooth hcalc f)
    (hJ : fam.IsAutomorphicOn hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J (fam.constantTerm J f))
    (hw : w ∈ fam.splitComponentOrbitSpan J (fam.constantTerm J f))
    (α : J.val)
    (hM : fam.IsAutomorphicOn hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho
      (fam.omitSimpleRoot α.val) (fam.constantTerm (fam.omitSimpleRoot α.val) f)) :
    fam.HasWeightedSiegelChamberGrowth j rho
      (fun a => Real.sqrt (δ a) * relativeCharacterDecay j α.val a)
      (w - fam.constantTerm (fam.removeSimpleRoot J α.val) w) := by
  let Kinf := K.comap (ofInfinite F G).toMonoidHom
  let M := fam.omitSimpleRoot α.val
  let Q := fam.removeSimpleRoot J α.val
  let g := fam.constantTerm M f
  let B (a : Torus) := Real.sqrt (δ a) * relativeCharacterDecay j α.val a
  have hQJ : Q ≤ J := (fam.removeSimpleRoot_lt J α.property).le
  have hfg : ∀ u ∈ rationalImage F (fam.iU J ≫ fam.p J), ∀ x, (f - g) (u * x) = (f - g) x := by
    intro u hu x
    have hM₀ := fam.isLeftInvariantUnder_rationalImage_of_le
      (show fam.bot ≤ M from Set.empty_subset _) hM.1
    exact congrArg₂ (· - ·) (hf.1.1 u (rationalImage_le_rationalSubgroup _ hu) x)
      (hM₀ u (fam.radical_rationalImage_le_minimalParabolic J hu) x)
  have hAverage : fam.HasWeightedSiegelChamberGrowth j rho B (fam.constantTerm J (f - g)) := by
    intro t Ω hΩ
    obtain ⟨Ω', hΩ', hBound⟩ :=
      fam.exists_compact_siegelRightFactors_constantTerm j rho hsetup hrho J t Ω hΩ
    obtain ⟨m, C, hC, hDecay⟩ := fam.exists_siegelRootDecay_weightedRemainder j rho hsmooth
      hSiegel hsetup hN hrho hK hIwa hf ⟨α.val, J.property α.property⟩ hM t Ω' hΩ'
    use m, C, hC
    apply hBound (f - g) hfg (fun a => C * B a * (1 + Real.log (H (aG a))) ^ m)
    intro a ha x hx
    exact (hDecay a ha x hx).trans_eq (by dsimp only [B]; ring)
  obtain ⟨shift, hShift⟩ := (fam.mem_splitComponentOrbitSpan_iff_exists_shift J _ w).mp hw
  have hfC : Continuous f := hf.1.2.1.1
  let fC : ContinuousRationalFunctions F G := ⟨⟨f, fun u x => hf.1.1 _ ⟨u, rfl⟩ x⟩, hfC⟩
  have hComp : fam.constantTerm J g = fam.constantTerm Q f := fam.constantTerm_constantTerm J M fC
  have hNested : fam.constantTerm Q (fam.constantTerm J f) = fam.constantTerm Q f := by
    have hI : fam.interIndex Q J = Q := Subtype.ext (Set.inter_eq_left.mpr hQJ)
    exact (fam.constantTerm_constantTerm Q J fC).trans (by rw [hI]; rfl)
  have hTop : fam.IsAutomorphicOn hsmooth Kinf rho fam.top f :=
    (fam.isWeakConstantTerm_top hf).isAutomorphicOn
  have hIntF := fam.integrable_constantTermIntegrand_of_le fam.top J (fam.le_top J) hfC hTop.1
  let p := fam.iU J ≫ fam.p J
  have hp : IsClosedSubgroup p :=
    (fam.isUnipotentRadical J).1.isClosedSubgroup.comp (fam.isCompatible J).parabolic.isClosedSubgroup
  let : IsClosedImmersion p.hom.hom.left := hp
  let : IsAffine (fam.U J).X.left := isAffine_left_of_isClosedSubgroup F p hp
  have hIntG : fam.HasIntegrableConstantTerm J g :=
    integrable_subgroupConstantTermIntegrand p (fam.isUnipotentRadical J).1.smooth
      (fam.isUnipotentRadical J).1.connectedSpace (fam.isUnipotentRadical J).1.isUnipotent hM.2.1.1
      (fun u hu => fam.isLeftInvariantUnder_rationalImage_of_le
        (show fam.bot ≤ M from Set.empty_subset _) hM.1 u
        (fam.radical_rationalImage_le_minimalParabolic J hu))
  have hEqual : w - fam.constantTerm Q w = fam.shiftAlgHom J shift (fam.constantTerm J (f - g)) := by
    rw [← hShift, fam.constantTerm_shiftAlgHom hQJ
        (fam.mem_radicalIntegrableSubmodule_of_automorphicOn hsmooth Kinf rho hQJ le_rfl hJ),
      ← map_sub, hNested, fam.constantTerm_sub_of_integrable hIntF hIntG, hComp]
  change fam.HasWeightedSiegelChamberGrowth j rho B (w - fam.constantTerm Q w)
  rw [hEqual]
  exact fam.hasWeightedSiegelChamberGrowth_shiftAlgHom j rho hN J
    (fun a => mul_nonneg (Real.sqrt_nonneg _) (relativeCharacterDecay_pos j α.val a).le) hAverage shift

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

open GroupScheme AdelicGroupPoints AdelicSiegelFactors PositiveRealTorus Automorphic.GroupSchemeFunctions

/-- A one-root gain for the maximal remainder transfers to the difference of
an ordinary constant-term orbit vector and its next smaller constant term. -/
def AdelicSiegelMaximalRemainderStatement : Prop :=
  LogSquareIntegrableSiegelDerivativeBoundsStatement →
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G)
    (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ fam.T),
    IsSiegelAlgebraicSetup F G fam.T fam.i fam.ν T₀ j →
    ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N)), 0 < N → IsClosedSubgroup rho →
    ∀ (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hsmooth)
      (K : Subgroup (AdelicGroupPoints F G)),
    IsMaximalCompactSubgroup F G K → IsIwasawaCompact (fam.p fam.bot) K →
    ∀ (f : AdelicGroupPoints F G → ℂ), IsLogSquareIntegrableAutomorphicForm F G K rho hsmooth hcalc f →
    let Kinf := K.comap (ofInfinite F G).toMonoidHom
    ∀ (J : StandardIndex F G fam.i fam.ν),
    fam.IsAutomorphicOn hsmooth Kinf rho J (fam.constantTerm J f) →
    ∀ (w : AdelicGroupPoints F G → ℂ), w ∈ fam.splitComponentOrbitSpan J (fam.constantTerm J f) →
    ∀ α : J.val,
    fam.IsAutomorphicOn hsmooth Kinf rho (fam.omitSimpleRoot α.val)
      (fam.constantTerm (fam.omitSimpleRoot α.val) f) →
    fam.HasWeightedSiegelChamberGrowth j rho
      (fun a => Real.sqrt (siegelModulus F G fam.T fam.i fam.ν T₀ j a) *
        relativeCharacterDecay j α.val a)
      (w - fam.constantTerm (fam.removeSimpleRoot J α.val) w)

theorem adelicSiegelMaximalRemainder : AdelicSiegelMaximalRemainderStatement := by
  intro hSiegel F _ _ G _ _ _ fam T₀ j hsetup N d rho hN hrho hsmooth hcalc K hK hIwa f hf Kinf
    J hAut w hw α hM
  exact fam.hasWeightedSiegelChamberGrowth_relativeRemainder j rho hsmooth J
    hSiegel hsetup hN hrho hK hIwa hf hAut hw α hM

end Langlands.Global
