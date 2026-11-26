import Langlands.Global.AdelicEisensteinCommonGrowthStatement
import Langlands.Global.AdelicEisensteinUniformHeight
import Langlands.Global.AdelicEisensteinTwistGrowth
import Langlands.Global.AdelicEisensteinParameterDecay
import Langlands.Global.AdelicPolynomialCosetRepresentatives
import Langlands.Global.ProjectiveHeightSummability
import Langlands.Global.AdelicEisensteinFiniteCompactChangeProof
import Langlands.Global.AdelicWavePacketRationalInvariance
import Langlands.Automorphic.GroupSchemeInvariantFormsComparison
import Langlands.Automorphic.GroupSchemeFiniteLevelSlices
import Langlands.Geometry.Manifold.SmoothGroupUniformLimit
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! # A common growth exponent for regular Eisenstein series -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry NumberField Filter Set Topology
open scoped Classical CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
  Langlands.Geometry.Manifold AdelicGroupPoints InfiniteAdelicGroupPoints RepresentationGrowth

section NormalSeries

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)

local notation "H" => InfiniteAdelicGroupPoints F G
local notation "FinPts" => FiniteAdelicGroupPoints F G
local notation "S" => InfinitePlotSmoothFunctions F G
local notation "U" => AdelicEnvelopingAlgebra F G hsmooth
local notation "E" => smoothModel F d
local notation "IH" => 𝓘(ℝ, E)

attribute [local instance 100] LieRing.ofAssociativeRing

include hcalc in
private theorem exists_sum_with_derivative_bound {Idx : Type v} (f : Idx → FinPts → S)
    (m : Idx → ℝ) (hm : Summable m) (hm₀ : ∀ i, 0 ≤ m i)
    (w : FinPts → H → ℝ) (hw : ∀ b, Continuous (w b))
    (hbound : ∀ a : U, ∃ C : ℝ, 0 ≤ C ∧ ∀ i b x,
      ‖(plotSmoothEnvelopingAction F G hsmooth hcalc a (f i b)).val x‖ ≤ C * m i * w b x) :
    ∃ g : FinPts → S, (∀ b x, (g b).val x = ∑' i, (f i b).val x) ∧
      ∀ a : U, ∃ C : ℝ, 0 ≤ C ∧ ∀ b x,
        ‖(plotSmoothEnvelopingAction F G hsmooth hcalc a (g b)).val x‖ ≤ C * w b x := by
  let := fun p : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F p
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup IH (minSmoothness ℝ 3) H := LieGroup.of_le (n := ∞) (by simp)
  let A := plotSmoothEnvelopingAction F G hsmooth hcalc
  let term (a : U) (i : Idx) (b : FinPts) (x : H) := (A a (f i b)).val x
  let value (a : U) (b : FinPts) (x : H) := ∑' i, term a i b x
  let gen (X : E) : U := UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)
  choose C hC hterm using hbound
  have hnorm (a : U) (b : FinPts) (x : H) : Summable (fun i => ‖term a i b x‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hterm a · b x) ?_
    exact (hm.mul_left _).mul_right _
  have hlim (a : U) (b : FinPts) :
      TendstoLocallyUniformly (fun T : Finset Idx => fun x => ∑ i ∈ T, term a i b x)
        (value a b) atTop := by
    apply tendstoLocallyUniformly_iff_forall_isCompact.mpr
    intro K hK
    obtain ⟨B, hB⟩ := (hK.image (hw b)).bddAbove
    exact tendstoUniformlyOn_tsum ((hm.mul_left (C a)).mul_right B) fun i x hx =>
      (hterm a i b x).trans (mul_le_mul_of_nonneg_left (hB ⟨x, hx, rfl⟩)
        (mul_nonneg (hC a) (hm₀ i)))
  have hsum (b : FinPts) :
      (∀ a, ContMDiff IH 𝓘(ℝ, ℂ) ∞ (value a b)) ∧
        ∀ a X, groupDirectionalValue IH X (value a b) = value (gen X * a) b := by
    let partialSum (T : Finset Idx) (a : U) : S := ∑ i ∈ T, A a (f i b)
    have hp (T : Finset Idx) (a : U) : (partialSum T a).val = fun x => ∑ i ∈ T, term a i b x := by
      funext x
      simp only [partialSum, Submodule.coe_sum, Finset.sum_apply, term]
    apply contMDiff_of_tendstoLocallyUniformly_invariantDerivatives (l := atTop)
        (fun X a => gen X * a) (f := fun T a => (partialSum T a).val) (g := fun a => value a b)
    · intro T a
      exact (isPlotSmooth_iff_contMDiff F G hsmooth (partialSum T a).val).mp (partialSum T a).property
    · intro T a X
      change (plotSmoothDifferential F G hsmooth X (partialSum T a)).val = (partialSum T (gen X * a)).val
      rw [← plotSmoothEnvelopingAction_real_generator F G hsmooth hcalc X]
      change (A (gen X) (partialSum T a)).val = _
      simp only [partialSum, map_sum, map_mul, Module.End.mul_apply]
    · intro a
      simpa only [hp] using hlim a b
  let series (b : FinPts) : U →ₗ[ℂ] S :=
    { toFun := fun a => ⟨value a b, (isPlotSmooth_iff_contMDiff F G hsmooth (value a b)).mpr
        ((hsum b).1 a)⟩
      map_add' := fun a c => Subtype.ext (funext fun x => by
        change (∑' i, term (a + c) i b x) = (∑' i, term a i b x) + (∑' i, term c i b x)
        rw [← (hnorm a b x).of_norm.tsum_add (hnorm c b x).of_norm]
        apply tsum_congr
        intro i
        simp only [term, map_add, LinearMap.add_apply, Submodule.coe_add, Pi.add_apply])
      map_smul' := fun z a => Subtype.ext (funext fun x => by
        change (∑' i, term (z • a) i b x) = z * (∑' i, term a i b x)
        rw [← tsum_mul_left]
        apply tsum_congr
        intro i
        simp only [term, map_smul, LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply,
          smul_eq_mul]) }
  have hgen (b : FinPts) (X : E) (a : U) : A (gen X) (series b a) = series b (gen X * a) := by
    apply Subtype.ext
    change (plotSmoothEnvelopingAction F G hsmooth hcalc (gen X) (series b a)).val = _
    rw [plotSmoothEnvelopingAction_real_generator]
    exact (hsum b).2 a X
  have hgenC (b : FinPts) (Z : ℂ ⊗[ℝ] GroupLieAlgebra IH H) (a : U) :
      A (UniversalEnvelopingAlgebra.ι ℂ Z) (series b a) =
        series b (UniversalEnvelopingAlgebra.ι ℂ Z * a) := by
    induction Z using TensorProduct.inductionOn with
    | tmul z X =>
      have hz : z ⊗ₜ[ℝ] X = z • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hz, map_smul, map_smul, LinearMap.smul_apply, smul_mul_assoc]
      change z • A (gen X) (series b a) = series b (z • (gen X * a))
      rw [map_smul, hgen]
    | add Z W hZ hW => simp only [map_add, LinearMap.add_apply, add_mul, hZ, hW]
  have hact (b : FinPts) (a : U) : ∀ c : U, A a (series b c) = series b (a * c) := by
    obtain ⟨t, rfl⟩ := RingCon.mkₐ_surjective (α := ℂ)
      (UniversalEnvelopingAlgebra.ringCon ℂ (ℂ ⊗[ℝ] GroupLieAlgebra IH H)) a
    induction t using TensorAlgebra.induction with
    | algebraMap z =>
      intro c
      simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one, LinearMap.smul_apply,
        Module.End.one_apply, smul_mul_assoc, one_mul]
    | «ι» Z => exact hgenC b Z
    | mul v w hv hw =>
      intro c
      simp only [map_mul, Module.End.mul_apply, hw, hv, mul_assoc]
    | add v w hv hw =>
      intro c
      simp only [map_add, LinearMap.add_apply, add_mul, hv, hw]
  refine ⟨fun b => series b 1, fun b x => ?_, fun a => ?_⟩
  · change (∑' i, (A 1 (f i b)).val x) = _
    simp only [map_one, Module.End.one_apply]
  · refine ⟨C a * ∑' i, m i, mul_nonneg (hC a) (tsum_nonneg hm₀), fun b x => ?_⟩
    change ‖(A a (series b 1)).val x‖ ≤ _
    rw [hact, mul_one]
    change ‖∑' i, term a i b x‖ ≤ _
    calc
      _ ≤ ∑' i, ‖term a i b x‖ := norm_tsum_le_tsum_norm (hnorm a b x)
      _ ≤ ∑' i, C a * m i * w b x := (hnorm a b x).tsum_le_tsum (hterm a · b x)
        ((hm.mul_left _).mul_right _)
      _ = _ := by rw [tsum_mul_right, tsum_mul_left]

end NormalSeries

set_option maxHeartbeats 5000000 in
/-- For every sufficiently regular parameter in a bounded set the absolutely
convergent Eisenstein series lies in one common finite-level growth space. -/
theorem eisensteinCommonGrowth : EisensteinCommonGrowthStatement.{u} := by
  intro F _ _ G P M V A _ _ _ _ p _ iU l a r _ _ _ hA hT hG hU K hK N d rho hN hrho
    hsmooth hcalc φ hmax hφ
  let : Smooth G.X.hom := hG.smooth
  let Points := AdelicGroupPoints F G
  let FinPts := FiniteAdelicGroupPoints F G
  let InfPts := InfiniteAdelicGroupPoints F G
  let S := InfinitePlotSmoothFunctions F G
  let UEA := AdelicEnvelopingAlgebra F G hsmooth
  let height := adelicHeight F G rho
  let norm₀ := adelicSourceNorm F G rho
  have hH₁ (g : Points) : 1 ≤ height g := one_le_adelicHeight F G rho hN g
  have hH₀ (g : Points) : 0 ≤ height g := zero_le_one.trans (hH₁ g)
  have hHpos (g : Points) : 0 < height g := zero_lt_one.trans_le (hH₁ g)
  obtain ⟨_, hφs, L₀, hL₀, hφL⟩ := hφ.2.1
  obtain ⟨e₀, he₀, hderφ⟩ := exists_uniformGrowth_functionInfiniteSlices F G hsmooth hcalc rho hN hG
    (K.comap (ofInfinite F G).toMonoidHom) hmax.isMaximalCompact_comap_ofInfinite
    φ hφs hφ.2.2.1 hφ.2.2.2.1 hφ.2.2.2.2
  have hH := hK.hasSmoothHeightPairings_of_maximal hmax hsmooth
  let KF := K.map (finite F G).toMonoidHom
  let L := L₀ ⊓ KF
  have hLo : IsOpen (L : Set FinPts) := hL₀.inter (IsMaximalCompactSubgroup.isOpen_finite F G K hmax)
  have hLc : IsCompact (L : Set FinPts) :=
    (hmax.1.image (finite F G).continuous).of_isClosed_subset (L.isClosed_of_isOpen hLo) inf_le_right
  have hLK (s : FinPts) (hs : s ∈ L) : ofFinite F G s ∈ K := by
    obtain ⟨k, hk, rfl⟩ := show s ∈ KF from hs.2
    exact ((hmax.mem_iff k).mp hk).2
  obtain ⟨nσ, j, σ, hstab⟩ := Chevalley.exists_line_stabilizer F G P p
    r.isCompatible.parabolic.isClosedSubgroup
  obtain ⟨B, d₀, hB, hd₀, hrep⟩ := exists_polynomial_rationalCoset_representatives rho σ j hG
    r.isCompatible.parabolic hstab
  choose rep hrepq hreph using hrep
  let C := ParabolicRationalCosets F p
  let proj := parabolicRationalProjectiveEmbedding σ j hstab
  let Hc (c : C) := (proj c).mulHeight
  let representative (c : C) := rational F G (rep c)
  have hHc (c : C) : 0 < Hc c := (proj c).mulHeight_pos
  obtain ⟨t, ht, hsum⟩ := summable_projectivization_mulHeight_rpow F (Fin (nσ + 1))
  let m (c : C) := Hc c ^ (-t)
  have hm : Summable m := by
    change Summable ((fun y : Projectivization F (Fin (nσ + 1) → F) => y.mulHeight ^ (-t)) ∘ proj)
    exact (hsum t le_rfl).comp_injective proj.injective
  have hm₀ (c : C) : 0 ≤ m c := Real.rpow_nonneg (hHc c).le _
  let decay := d₀ * e₀ + t
  obtain ⟨R₀, hdec⟩ := hK.exists_norm_heightPower_rational_le_projectiveHeight r hA hT hG σ j
    hstab decay (add_nonneg (mul_nonneg hd₀ he₀) ht)
  refine ⟨R₀, fun n e W hW => ⟨L, hLo, hLc, ?_⟩⟩
  obtain ⟨B₁, d₁, hB₁, _, htranslation⟩ := hK.exists_uniform_heightPower_mul_le rho hN hrho
    e.toLinearMap hW
  let R₁ := e₀ + d₁
  refine ⟨R₁, fun R hR s hs hsreg => ?_⟩
  let lam := e s
  obtain ⟨B₂, hB₂, hbase⟩ := hdec n e.toLinearMap {s} isCompact_singleton (by
    intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    exact hsreg)
  have hparam (c : C) (g : Points) :
      ‖hK.heightPower lam (representative c * g)‖ ≤ B₁ * height g ^ d₁ * (B₂ * Hc c ^ (-decay)) := by
    have hb := hbase (rep c) s (Set.mem_singleton s)
    change ‖hK.heightPower lam (representative c)‖ ≤ B₂ * (proj (Quotient.mk _
      ⟨representative c, ⟨rep c, rfl⟩⟩ : C)).mulHeight ^ (-decay) at hb
    rw [hrepq c] at hb
    exact (htranslation s hs (representative c) g).trans
      (mul_le_mul_of_nonneg_left hb (mul_nonneg hB₁.le (Real.rpow_nonneg (hH₀ g) _)))
  have hrepGrowth (c : C) (g : Points) :
      height (representative c * g) ^ e₀ ≤ B ^ e₀ * Hc c ^ (d₀ * e₀) * height g ^ e₀ := by
    have hrepresentative : height (representative c) ≤ B * Hc c ^ d₀ := by
      simpa only [adelicHeightAtLeastOne_eq hN] using hreph c
    have hmul : height (representative c * g) ≤ (B * Hc c ^ d₀) * height g :=
      (adelicHeight_mul_le F G rho hN _ _).trans (mul_le_mul_of_nonneg_right hrepresentative (hH₀ g))
    refine (Real.rpow_le_rpow (hH₀ _) hmul he₀).trans_eq ?_
    rw [Real.mul_rpow (mul_nonneg hB.le (Real.rpow_nonneg (hHc c).le _)) (hH₀ g),
      Real.mul_rpow hB.le (Real.rpow_nonneg (hHc c).le _), Real.rpow_mul (hHc c).le]
  let twisted := hK.parameterTwistSlice hsmooth hH φ hφs lam
  let term (c : C) (b : FinPts) : S :=
    plotSmoothLeftTranslation F G (infinite F G (representative c)) (twisted (finite F G (representative c) * b))
  have hpair (c : C) (b : FinPts) (x : InfPts) :
      pair F G (infinite F G (representative c) * x) (finite F G (representative c) * b) = representative c * pair F G x b := by
    conv_rhs => rw [← pair_projections F G (representative c), AdelicGroupPoints.pair_mul]
  have htermEq (c : C) (b : FinPts) (x : InfPts) :
      (term c b).val x = hK.eisensteinTerm φ lam (pair F G x b) c := by
    rw [hK.eisensteinTerm_eq_of_representative hφ.1 r.isCompatible.levi hU lam _ c
      ⟨representative c, ⟨rep c, rfl⟩⟩ (hrepq c)]
    rw [show (term c b).val x = hK.parameterTwist φ lam
      (pair F G (infinite F G (representative c) * x) (finite F G (representative c) * b)) from rfl, hpair]
  let weight (b : FinPts) (x : InfPts) := height (pair F G x b) ^ R₁
  have hw (b : FinPts) : Continuous (weight b) :=
    ((continuous_adelicHeight F G rho hN).comp ((continuous_pair F G).comp
      (continuous_id.prodMk continuous_const))).rpow_const (fun x => Or.inl (hHpos _).ne')
  have hterms (D : UEA) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ c b x,
      ‖(plotSmoothEnvelopingAction F G hsmooth hcalc D (term c b)).val x‖ ≤ C₀ * m c * weight b x := by
    obtain ⟨C₀, hC₀, hb⟩ := hK.exists_parameterTwist_derivative_bound hmax hsmooth hcalc rho
      hH φ hφs hN e₀ hderφ lam D
    refine ⟨C₀ * B ^ e₀ * B₁ * B₂, by positivity, fun c b x => ?_⟩
    let g := pair F G x b
    have h₁ := hb (finite F G (representative c) * b) (infinite F G (representative c) * x)
    rw [hpair] at h₁
    have hτ : ‖(plotSmoothEnvelopingAction F G hsmooth hcalc D (term c b)).val x‖ ≤
        C₀ * (height (representative c * g) ^ e₀ * ‖hK.heightPower lam (representative c * g)‖) := by
      simpa only [term, plotSmoothEnvelopingAction_leftTranslate F G hsmooth hcalc,
        plotSmoothLeftTranslation_apply, twisted, g] using h₁
    refine hτ.trans ((mul_le_mul_of_nonneg_left
      (mul_le_mul (hrepGrowth c g) (hparam c g) (norm_nonneg _)
        (mul_nonneg (mul_nonneg (Real.rpow_nonneg hB.le _) (Real.rpow_nonneg (hHc c).le _))
          (Real.rpow_nonneg (hH₀ g) _))) hC₀).trans_eq ?_)
    change C₀ * (B ^ e₀ * Hc c ^ (d₀ * e₀) * height g ^ e₀ *
      (B₁ * height g ^ d₁ * (B₂ * Hc c ^ (-decay)))) =
        C₀ * B ^ e₀ * B₁ * B₂ * Hc c ^ (-t) * height g ^ (e₀ + d₁)
    rw [show Hc c ^ (-t) = Hc c ^ (d₀ * e₀) * Hc c ^ (-decay) by
      rw [← Real.rpow_add (hHc c), show d₀ * e₀ + -decay = -t by dsimp [decay]; ring]]
    rw [Real.rpow_add (hHpos g)]
    ring
  have hsummed := exists_sum_with_derivative_bound F G hsmooth hcalc (Idx := C) term m hm
    hm₀ weight hw hterms
  obtain ⟨slice, hslice, hslicebound⟩ := hsummed
  let series := hK.eisensteinSeries φ lam
  have hseries (b : FinPts) (x : InfPts) : (slice b).val x = series (pair F G x b) := by
    rw [hslice]
    exact tsum_congr (fun c => htermEq c b x)
  have hright (y : FinPts) (hy : y ∈ L) (g : Points) : series (g * ofFinite F G y) = series g := by
    apply tsum_congr
    intro c
    change hK.parameterTwist φ lam ((Quotient.out c : rationalSubgroup F G).val *
      (g * ofFinite F G y)) = hK.parameterTwist φ lam ((Quotient.out c : rationalSubgroup F G).val * g)
    rw [← mul_assoc, IsIwasawaCompact.parameterTwist, IsIwasawaCompact.parameterTwist,
      hφL y hy.1, IsIwasawaCompact.heightPower, IsIwasawaCompact.heightPower,
      hK.height_mul_right _ (hLK y hy)]
  have hcont : Continuous series :=
    (continuous_evaluatePlotSmoothSlices F G hsmooth slice ⟨L, hLo⟩ (fun b y =>
      Subtype.ext (funext fun x => by
        rw [hseries, hseries, ← show pair F G x b * ofFinite F G y.val = pair F G x (b * y.val) by
          rw [ofFinite_eq_pair, AdelicGroupPoints.pair_mul, mul_one]]
        exact hright y y.property _))).congr (fun g => by
          change (slice (finite F G g)).val (infinite F G g) = series g
          rw [hseries, pair_projections])
  have hsmoothSeries : IsAdelicSmoothFunction F G series := by
    refine ⟨hcont, fun b => ?_, L, hLo, hright⟩
    have heq : functionInfiniteSlice F G series b = (slice b).val := funext fun x => (hseries b x).symm
    exact heq ▸ (slice b).property
  have hleft := eisensteinSeries_leftRationalInvariant hK hφ.1 hU r.isCompatible.levi lam
  let f := ofRationalSmoothFunction F G series hleft hsmoothSeries
  have hfSlice (b : FinPts) : finitePlotSmoothSlice F G b f = slice b :=
    Subtype.ext (funext fun x => (hseries b x).symm)
  refine ⟨⟨f, ?_, ?_⟩, rfl⟩
  · intro y hy
    apply finitePlotSmoothEvaluation_injective F G
    funext g
    exact hright y hy g
  · intro D
    obtain ⟨C₀, hC₀, hCbound⟩ := hslicebound D
    let c : ℝ := (N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult)
    have hc : 0 ≤ c := pow_nonneg (Nat.cast_nonneg _) _
    refine ⟨C₀ * c ^ R, fun g => ?_⟩
    obtain ⟨⟨x, b⟩, rfl⟩ := (split F G).symm.surjective g
    change ‖evaluate F G (adelicEnvelopingAction F G hsmooth hcalc D f).val (pair F G x b)‖ ≤
      C₀ * c ^ R * norm₀ (pair F G x b) ^ R
    rw [← finitePlotSmoothSlice_apply, finitePlotSmoothSlice_envelopingAction, hfSlice]
    refine (hCbound b x).trans ?_
    change C₀ * height (pair F G x b) ^ R₁ ≤ _
    calc
      _ ≤ C₀ * height (pair F G x b) ^ R := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (hH₁ _) hR) hC₀
      _ = _ := by
        rw [show height (pair F G x b) = c * norm₀ (pair F G x b) from
          adelicHeight_eq_scalar_mul_sourceNorm F G rho _,
          Real.mul_rpow hc (adelicSourceNorm_pos F G rho hN _).le, mul_assoc]

end Langlands.Global
