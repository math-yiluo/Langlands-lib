import Langlands.Global.AdelicSymmetricWavePacketTranslation
import Langlands.Global.AdelicSymmetricConvolutionFamilies
import Langlands.Global.AdelicNormalizedConvolutionFiniteSpan
import Langlands.Global.AdelicImaginaryEisensteinConvolution
import Langlands.Global.AdelicEisensteinImaginaryContinuation
import Langlands.Global.AdelicInducedRestrictionMemLp
import Langlands.Global.AdelicWavePacketRationalInvariance

/-! # Compactly supported integration of finite wave-packet sums -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

section Integrals

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local notation "Ad" => AdelicGroupPoints F G

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
private theorem continuous_packetIntegral {n k : ℕ} (ν : Measure (Fin n → ℝ))
    [IsFiniteMeasureOnCompacts ν] {c : Fin k → (Fin n → ℝ) → ℂ}
    {E : Fin k → (Fin n → ℝ) → Ad → ℂ}
    (hc : ∀ j, Continuous (c j)) (hcs : ∀ j, HasCompactSupport (c j))
    (hE : ∀ j, Continuous (Function.uncurry (E j))) :
    Continuous (fun g => ∫ x, ∑ j, c j x * E j x g ∂ν) := by
  rw [← continuousOn_univ]
  apply continuousOn_integral_of_compact_support («μ» := ν)
    (k := ⋃ j, tsupport (c j)) (isCompact_iUnion fun j => (hcs j).isCompact)
  · apply Continuous.continuousOn
    refine continuous_finsetSum _ fun j _ => ((hc j).comp continuous_snd).mul ?_
    exact (hE j).comp continuous_swap
  · intro g x _ hx
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (mem_iUnion.mpr ⟨j, h⟩)), zero_mul]

private theorem rightConvolution_packetIntegral {n k : ℕ} (ν : Measure (Fin n → ℝ))
    [IsFiniteMeasureOnCompacts ν] {kernel : Ad → ℂ} (hk : Continuous kernel)
    (hks : HasCompactSupport kernel) {c : Fin k → (Fin n → ℝ) → ℂ}
    {E : Fin k → (Fin n → ℝ) → Ad → ℂ}
    (hc : ∀ j, Continuous (c j)) (hcs : ∀ j, HasCompactSupport (c j))
    (hE : ∀ j, Continuous (Function.uncurry (E j))) (g : Ad) :
    rightConvolution F G kernel (fun g => ∫ x, ∑ j, c j x * E j x g ∂ν) g =
      ∫ x, ∑ j, c j x * rightConvolution F G kernel (E j x) g ∂ν := by
  let f (h : Ad) (x : Fin n → ℝ) := kernel h * ∑ j, c j x * E j x (g * h)
  have hfc : Continuous (Function.uncurry f) := by
    refine (hk.comp continuous_fst).mul (continuous_finsetSum _ fun j _ => ?_)
    exact ((hc j).comp continuous_snd).mul
      ((hE j).comp (continuous_snd.prodMk (continuous_const.mul continuous_fst)))
  have hfs : HasCompactSupport (Function.uncurry f) := by
    refine HasCompactSupport.intro (hks.isCompact.prod (isCompact_iUnion fun j => (hcs j).isCompact))
      (fun z hz => ?_)
    change kernel z.1 * ∑ j, c j z.2 * E j z.2 (g * z.1) = 0
    by_cases hs : z.1 ∈ tsupport kernel
    · rw [Finset.sum_eq_zero fun j _ => ?_, mul_zero]
      rw [image_eq_zero_of_notMem_tsupport (fun hj => hz ⟨hs, mem_iUnion.mpr ⟨j, hj⟩⟩), zero_mul]
    · rw [image_eq_zero_of_notMem_tsupport hs, zero_mul]
  calc
    _ = ∫ h, ∫ x, f h x ∂ν ∂Measure.haar := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun h => (integral_const_mul _ _).symm
    _ = ∫ x, ∫ h, f h x ∂Measure.haar ∂ν := integral_integral_swap_of_hasCompactSupport hfc hfs
    _ = _ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      change (∫ h, kernel h * ∑ j, c j x * E j x (g * h) ∂Measure.haar) = _
      simp only [Finset.mul_sum, mul_left_comm (kernel _)]
      rw [integral_finsetSum]
      · exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
      · intro j _
        have hcj : Continuous (fun h => c j x * (kernel h * E j x (g * h))) :=
          continuous_const.mul (hk.mul ((hE j).comp (continuous_const.prodMk (continuous_const.mul continuous_id))))
        exact hcj.integrable_of_hasCompactSupport hks.mul_right.mul_left

end Integrals

section Families

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {I : Type} [Fintype I] {P : I → GroupScheme (Spec (CommRingCat.of F))} {n nP : I → ℕ}
  (e : ∀ i, (Fin (n i) → ℝ) ≃ₗ[ℝ] RealCharacterParameter F (P i))
  {k : I → ℕ} (c : ∀ i, Fin (k i) → (Fin (n i) → ℝ) → ℂ)
  (E : ∀ i, Fin (k i) → ComplexCharacterParameter F (P i) → AdelicGroupPoints F G → ℂ)

local notation "Imag" => (fun i x => imaginaryParameter F (P i) (e i x))

private theorem isFiniteMeasureOnCompacts_spectral (n : ℕ) :
    IsFiniteMeasureOnCompacts (spectralMeasure n) := by
  unfold spectralMeasure
  refine IsFiniteMeasureOnCompacts.smul _ (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 ?_))
  exact (ENNReal.ofReal_pos.2 (by positivity)).ne'

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- A finite packet sum is continuous when the continuations are jointly continuous on the
imaginary parameter coordinates and the scalar coefficients are continuous with compact support. -/
theorem continuous_wavePacketSumOnGroup
    (hc : ∀ i j, Continuous (c i j)) (hcs : ∀ i j, HasCompactSupport (c i j))
    (hE : ∀ i j, Continuous (Function.uncurry fun x => E i j (Imag i x))) :
    Continuous (wavePacketSumOnGroup e nP c E) := by
  refine continuous_finsetSum _ fun i _ => continuous_const.mul ?_
  let := isFiniteMeasureOnCompacts_spectral (n i)
  exact continuous_packetIntegral (spectralMeasure (n i)) (hc i) (hcs i) (hE i)

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- Left rational invariance of the Eisenstein values on the imaginary axis descends the whole
weighted packet sum to the rational quotient. -/
theorem wavePacketSumOnGroup_leftRationalInvariant
    (hE : ∀ i j x, IsLeftInvariantUnder F G (rationalSubgroup F G) (E i j (Imag i x))) :
    IsLeftInvariantUnder F G (rationalSubgroup F G) (wavePacketSumOnGroup e nP c E) := by
  intro d hd g
  unfold wavePacketSumOnGroup
  refine Finset.sum_congr rfl fun i _ => congrArg (((nP i : ℂ))⁻¹ * ·) ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact Finset.sum_congr rfl fun j _ => congrArg (c i j x * ·) (hE i j x d hd g)

/-- Convolution of the whole weighted packet sum passes through each spectral integral. -/
theorem rightConvolution_wavePacketSumOnGroup
    {kernel : AdelicGroupPoints F G → ℂ} (hk : Continuous kernel) (hks : HasCompactSupport kernel)
    (hc : ∀ i j, Continuous (c i j)) (hcs : ∀ i j, HasCompactSupport (c i j))
    (hE : ∀ i j, Continuous (Function.uncurry fun x => E i j (Imag i x))) (g : AdelicGroupPoints F G) :
    rightConvolution F G kernel (wavePacketSumOnGroup e nP c E) g =
      ∑ i, ((nP i : ℂ))⁻¹ * ∫ x, ∑ j, c i j x * rightConvolution F G kernel (E i j (Imag i x)) g
        ∂(spectralMeasure (n i)) := by
  let v (i : I) (z : AdelicGroupPoints F G) :=
    ∫ x, ∑ j, c i j x * E i j (Imag i x) z ∂(spectralMeasure (n i))
  have hvc (i : I) : Continuous (v i) := by
    let := isFiniteMeasureOnCompacts_spectral (n i)
    exact continuous_packetIntegral (spectralMeasure (n i)) (hc i) (hcs i) (hE i)
  change (∫ h, kernel h * ∑ i, ((nP i : ℂ))⁻¹ * v i (g * h) ∂Measure.haar) = _
  simp only [Finset.mul_sum, mul_left_comm (kernel _)]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul]
    apply congrArg (((nP i : ℂ))⁻¹ * ·)
    let := isFiniteMeasureOnCompacts_spectral (n i)
    exact rightConvolution_packetIntegral (spectralMeasure (n i)) hk hks (hc i) (hcs i) (hE i) g
  · intro i _
    have hvk : Continuous (fun h => ((nP i : ℂ))⁻¹ * (kernel h * v i (g * h))) :=
      continuous_const.mul (hk.mul ((hvc i).comp (continuous_const.mul continuous_id)))
    exact hvk.integrable_of_hasCompactSupport hks.mul_right.mul_left

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
private theorem wavePacketSumOnGroup_scale (α : ℂ) (g : AdelicGroupPoints F G) :
    α * wavePacketSumOnGroup e nP c E g =
      wavePacketSumOnGroup e nP (fun i j x => α * c i j x) E g := by
  unfold wavePacketSumOnGroup
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_left_comm α, ← integral_const_mul]
  apply congrArg (((nP i : ℂ))⁻¹ * ·)
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Finset.mul_sum, mul_assoc]

end Families

private theorem ae_smul_nestedLp {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {ν ν' : Measure X} {ρ : Measure Y} (hν : ae ν ≤ ae ν') {H : Submodule ℂ (Lp ℂ 2 ρ)}
    (α : ℂ) (f : Lp H 2 ν') {v : X → Y → ℂ}
    (hf : ∀ᵐ x ∂ν, ⇑(f x : Lp ℂ 2 ρ) =ᵐ[ρ] v x) :
    ∀ᵐ x ∂ν, ⇑((α • f) x : Lp ℂ 2 ρ) =ᵐ[ρ] fun y => α * v x y := by
  filter_upwards [hν (Lp.coeFn_smul α f), hf] with x hx hv
  rw [hx]
  change ⇑(α • (f x : Lp ℂ 2 ρ)) =ᵐ[ρ] _
  exact (Lp.coeFn_smul α (f x : Lp ℂ 2 ρ)).trans (hv.const_smul α)

/-- Joint continuity and covariance of the given Eisenstein continuations, finite expansions
of normalized convolutions and intertwining operators, and existence of the new Eisenstein
continuations imply convolution stability of symmetric packets. -/
def SymmetricWavePacketConvolutionAssemblyStatement : Prop :=
  NormalizedConvolutionFiniteSpanStatement → ImaginaryEisensteinConvolutionStatement →
  IntertwiningSquareIntegrableExpansionStatement → EisensteinImaginaryContinuationStatement →
  SymmetricWavePacketConvolutionStatement

set_option maxHeartbeats 6000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem symmetricWavePacketConvolution_of_finiteExpansions :
    SymmetricWavePacketConvolutionAssemblyStatement := by
  classical
  intro hSpan hCov hExpansion hImag F _ _ G _ _ _ I _ P M U A _ _ _ _ p _ iU l _ a r _ _ _ hA hT π
    hG hUR hMul hπ K hK N d rho hsmooth hcalc hKm hrho μM _ hμM n e β hβ T _ w cw hW _hinj hsurj
    hw nP Mop hMop Φ k v c E D hΦ hE
  let : ∀ i, LocallyOfFiniteType (P i).X.hom := fun i =>
    IsClosedSubgroup.locallyOfFiniteType (j := p i) (inferInstance : IsClosedImmersion (p i).hom.hom.left)
  let A₂ (i : I) := IsSquareIntegrableInducedForm K (hK i).isCompact rho hsmooth hcalc (p i) (iU i) (l i)
  let ν (i : I) := inducedL2Measure K (hK i).isCompact (l i) (μM i) (e i) (β i)
  let Imag (i : I) (x : Fin (n i) → ℝ) := imaginaryParameter F (P i) (e i x)
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have := subsingleton_adelicGroupPoints_of_rank_zero rho hrho
    have hconst : wavePacketSumOnGroup e nP c E = fun _ => wavePacketSumOnGroup e nP c E 1 :=
      funext fun g => congrArg _ (Subsingleton.elim g 1)
    have hmul (g h : AdelicGroupPoints F G) : g * h = g := Subsingleton.elim _ _
    refine ⟨hconst.symm ▸ continuous_const, fun g _ h => congrArg _ (Subsingleton.elim (g * h) h), ?_⟩
    intro kernel _hker
    let α : ℂ := ∫ h, kernel h ∂(Measure.haar : Measure (AdelicGroupPoints F G))
    refine ⟨α • Φ, k, v, fun i j x => α * c i j x, E, D, ⟨hΦ.1, fun i j =>
      ⟨contDiff_const.mul (hΦ.2.1 i j).1, (hΦ.2.1 i j).2.mul_left⟩, ?_⟩, hE, ?_⟩
    · intro i
      have hν : ae (((nP i : ℝ≥0∞))⁻¹ • spectralMeasure (n i)) = ae (spectralMeasure (n i)) :=
        (ae_smul_spectralMeasure_eq _ (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))).trans
          (ae_spectralMeasure_eq _).symm
      have hm := ae_smul_nestedLp hν.ge α (Φ.1 i) (hΦ.2.2 i)
      refine hm.mono fun x hx => hx.trans (Filter.Eventually.of_forall fun z => ?_)
      simp only [inducedRestriction, Finset.mul_sum, mul_assoc]
    · funext g
      simp only [rightConvolution, hmul, integral_mul_const]
      exact wavePacketSumOnGroup_scale e c E α g
  have hAnalytic (i : I) (j : Fin (k i)) :=
    hCov F G (P i) (M i) (U i) (A i) (p i) (iU i) (l i) (a i) (r i) (hA i) (hT i) hG (hUR i) K
      (hK i) rho hsmooth hcalc hN hKm hrho (v i j) (hΦ.1 i j).1 (E i j) (D i)
      (hE i).1 ((hE i).2.1 j) ((hE i).2.2 j)
  have hc (i : I) (j : Fin (k i)) : Continuous (c i j) := (hΦ.2.1 i j).1.continuous
  have hcs (i : I) (j : Fin (k i)) : HasCompactSupport (c i j) := (hΦ.2.1 i j).2
  have hEc (i : I) (j : Fin (k i)) : Continuous (Function.uncurry fun x => E i j (Imag i x)) :=
    (hAnalytic i j).1 (n i) (e i)
  have hEInv (i : I) (j : Fin (k i)) (x : Fin (n i) → ℝ) :
      IsLeftInvariantUnder F G (rationalSubgroup F G) (E i j (Imag i x)) :=
    eisensteinContinuationRationalInvariance F G (P i) (M i) (U i) (A i) (p i) (iU i)
      (l i) (a i) (r i) (hA i) (hT i) hG (hUR i) K (hK i) (v i j) (hΦ.1 i j).1.1
      (E i j) (D i) ((hE i).2.1 j) ((hE i).2.2 j) _ ((hE i).1 ⟨e i x, rfl⟩)
  refine ⟨continuous_wavePacketSumOnGroup e c E hc hcs hEc,
    wavePacketSumOnGroup_leftRationalInvariant e c E hEInv, ?_⟩
  intro kernel hker
  have hk := hker.1
  have hks := hker.2.1
  have hnP (i : I) : nP i ≠ 0 := by
    have := nonempty_self T cw hsurj i
    exact (Finset.sum_pos' (fun _ _ => Nat.zero_le _)
      ⟨i, Finset.mem_univ _, Fintype.card_pos⟩).ne'
  have hL (i : I) (f : AdelicGroupPoints F G → ℂ) (hf : A₂ i f) :
      MemLp (inducedRestriction K (p i) (l i) f) 2 (ν i) :=
    inducedRestrictionMemLp F G (P i) (M i) (U i) (A i) (p i) (iU i) (l i) (a i) (r i)
      (hA i) (hT i) (π i) hG (hUR i) (hMul i) (hπ i) K (hK i) rho hsmooth hcalc hKm hrho
      (μM i) (hμM i) (e i) (β i) (hβ i).1 (hβ i).2.1 (hβ i).2.2.1 f hf
  have hEx (i i' : I) (t : T i i') (f : AdelicGroupPoints F G → ℂ) (hf : A₂ i f) :=
    hExpansion F G (P i) (M i) (U i) (P i') (M i') (U i') (A i) (A i') (p i) (iU i) (l i)
      (a i) (r i) (hA i) (hT i) (p i') (iU i') (l i') (a i') (r i') (π i')
      (w i i' t) (cw i i' t) hG (hUR i) (hUR i') (hMul i') (hπ i') (hW i i' t)
      K (hK i) (hK i') rho hsmooth hcalc f hKm hrho hf
  have hConv (i : I) (f : AdelicGroupPoints F G → ℂ) (hf : A₂ i f) :=
    hSpan F G (P i) (M i) (U i) (A i) (p i) (iU i) (l i) (a i) (r i) (hA i) (hT i)
      (π i) hG (hUR i) (hMul i) (hπ i) K (hK i) rho hsmooth hcalc hKm hrho (μM i) (hμM i) f hf
      kernel hker
  choose m u b hu hcu using fun i j => hConv i (v i j) (hΦ.1 i j)
  let J (i : I) := Σ j : Fin (k i), Fin (m i j)
  let k' (i : I) := Fintype.card (J i)
  let idx (i : I) : J i ≃ Fin (k' i) := Fintype.equivFin (J i)
  let v' (i : I) (q : Fin (k' i)) := u i ((idx i).symm q).1 ((idx i).symm q).2
  let c' (i : I) (q : Fin (k' i)) (x : Fin (n i) → ℝ) :=
    c i ((idx i).symm q).1 x * b i ((idx i).symm q).1 ((idx i).symm q).2 (Imag i x)
  have hSym := exists_symmetricFamily_of_finiteConvolutionExpansions
    (F := F) (G := G) (I := I) (P := P) (M := M) (U := U) (A := A) (p := p) (iU := iU) (l := l)
    (K := K) (hK := hK) (rho := rho) (hsmooth := hsmooth) (hcalc := hcalc) (μM := μM)
    (n := n) (e := e) (β := β) (nP := nP) (T := T) (Mop := Mop) (kernel := kernel)
    (Φ := Φ) (k := k) (v := v) (c := c) (m := m) (u := u) (b := b)
    (π := π) (r := r) (a := a) (hA := hA) (hT := hT) (w := w) (cw := cw) (hw := hw)
    hG hUR hMul hπ hKm hrho hW hMop hβ hnP hL hEx hk hks hConv hΦ hu hcu
  obtain ⟨Ψ, hΨ⟩ := hSym
  have hNew (i : I) := hImag F G (P i) (M i) (U i) (A i) (p i) (iU i) (l i) (a i) (r i)
    (hA i) (hT i) hG (hUR i) K (hK i) rho hsmooth hcalc hKm hrho (k' i) (v' i)
    (fun q => hu i ((idx i).symm q).1 ((idx i).symm q).2)
  choose E' D' hE' using hNew
  refine ⟨Ψ, k', v', c', E', D', hΨ, hE', ?_⟩
  have hSub (i : I) (j : Fin (k i)) : IsEisensteinContinuation (hK i) (r i) (hA i) (hT i)
      (u i j) (fun q => E' i (idx i ⟨j, q⟩)) (D' i) := by
    refine ⟨(hE' i).1, fun q g => (hE' i).2.1 _ g, fun q => ?_⟩
    obtain ⟨R, hR⟩ := (hE' i).2.2 (idx i ⟨j, q⟩)
    have hvsub : v' i (idx i ⟨j, q⟩) = u i j q :=
      congrArg (fun z : J i => u i z.1 z.2) ((idx i).symm_apply_apply ⟨j, q⟩)
    refine ⟨R, fun lam hlam => ?_⟩
    change E' i (idx i ⟨j, q⟩) lam = (hK i).eisensteinSeries (u i j q) lam
    rw [hR lam hlam, hvsub]
  have hCE (i : I) (j : Fin (k i)) (x : Fin (n i) → ℝ) (g : AdelicGroupPoints F G) :
      rightConvolution F G kernel (E i j (Imag i x)) g =
        ∑ q, b i j q (Imag i x) * E' i (idx i ⟨j, q⟩) (Imag i x) g :=
    (hAnalytic i j).2 kernel hk hks (m i j) (u i j) (b i j) _ (D' i) (fun q => (hu i j q).1)
      (hcu i j) (hSub i j) (e i x) g
  funext g
  rw [rightConvolution_wavePacketSumOnGroup e c E hk hks hc hcs hEc g]
  unfold wavePacketSumOnGroup
  refine Finset.sum_congr rfl fun i _ => congrArg (((nP i : ℂ))⁻¹ * ·) ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change (∑ j, c i j x * rightConvolution F G kernel (E i j (Imag i x)) g) =
    ∑ q, c' i q x * E' i q (Imag i x) g
  calc
    _ = ∑ j, ∑ q, (c i j x * b i j q (Imag i x)) * E' i (idx i ⟨j, q⟩) (Imag i x) g := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hCE i j x g, Finset.mul_sum]
      simp only [mul_assoc]
    _ = _ := by
      rw [← Fintype.sum_sigma']
      refine Fintype.sum_equiv (idx i) _ _ fun z => ?_
      have hz : c' i (idx i z) x = c i z.1 x * b i z.1 z.2 (Imag i x) :=
        congrArg (fun q : J i => c i q.1 x * b i q.1 q.2 (Imag i x)) ((idx i).symm_apply_apply z)
      exact congrArg (fun a : ℂ => a * E' i (idx i z) (Imag i x) g) hz.symm

/-- The translation approximation follows from separation, the wave-packet Gram identity,
and the analytic expansions used to construct symmetric convolutions. -/
def WavePacketTranslationOfAnalyticInputsStatement : Prop :=
  RightTranslationTestFunctionSeparationStatement → SymmetricFamilyGramStatement →
  NormalizedConvolutionFiniteSpanStatement → ImaginaryEisensteinConvolutionStatement →
  IntertwiningSquareIntegrableExpansionStatement → EisensteinImaginaryContinuationStatement →
  WavePacketTranslationStatement

theorem wavePacketTranslation_of_analyticInputs : WavePacketTranslationOfAnalyticInputsStatement := by
  intro hSep hGram hSpan hCov hExp hE
  exact wavePacketTranslation_of_convolution hSep hGram
    (symmetricWavePacketConvolution_of_finiteExpansions hSpan hCov hExp hE)

end Langlands.Global
