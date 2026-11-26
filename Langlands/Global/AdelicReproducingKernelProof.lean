import Langlands.Global.AdelicReproducingKernelStatement
import Langlands.Automorphic.GroupSchemeInvariantFormsComparison
import Langlands.Automorphic.GroupSchemeAdaptedCasimirProof
import Langlands.Automorphic.GroupSchemeAutomorphicUniformGrowthReductionProof
import Langlands.Geometry.Manifold.LieGroupEllipticL2
import Langlands.Analysis.CompactL2ReproducingKernel
import Langlands.Global.AdelicMaximalCompactFactors
import Langlands.Global.InfiniteAdelicModularCharacter
import Langlands.Global.AdelicHaarUnimodularityProof
import Langlands.Group.GL.LeviCentralQuotientMeasure
import Langlands.Representation.Unitary.CentralQuotientForm

/-! # A continuous compactly supported reproducing kernel on reductive adelic groups -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj ContDiff ENNReal Manifold NNReal Pointwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
open Langlands.Geometry.Manifold Langlands.Analysis AdelicGroupPoints

section WordSolutions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [Group H] [TopologicalSpace H] [ChartedSpace E H]
  [LieGroup 𝓘(ℝ, E) ∞ H] {n : ℕ}

local notation "𝓘E" => 𝓘(ℝ, E)

/-- The subspace of smooth complex-valued functions for the specified Lie group atlas. -/
private def smoothScalarFunctions : Submodule ℂ (H → ℂ) where
  carrier := {f | ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ f}
  zero_mem' := contMDiff_const
  add_mem' {_f _g} hf hg := hf.add hg
  smul_mem' c _f hf :=
    (((ContinuousLinearMap.mul ℝ ℂ) c).contDiff (n := ∞)).contMDiff.comp hf

/-- One left-invariant direction acts linearly on the smooth subspace. -/
private def directionLinear (X : GroupLieAlgebra 𝓘E H) :
    Module.End ℂ (smoothScalarFunctions (E := E) (H := H)) where
  toFun f := ⟨groupDirectionalValue 𝓘E X f.val, contMDiff_groupDirectionalValue 𝓘E X f.property⟩
  map_add' f g := Subtype.ext (funext fun x => groupDirectionalValue_add 𝓘E X f.property g.property x)
  map_smul' c f := Subtype.ext (funext fun x => groupDirectionalValue_const_smul 𝓘E X c f.property x)

/-- Extend the directional action to the complex algebra of words. -/
private def smoothWordAction (X : Fin n → GroupLieAlgebra 𝓘E H) :
    MonoidAlgebra ℂ (FreeMonoid (Fin n)) →ₐ[ℂ] Module.End ℂ (smoothScalarFunctions (E := E) (H := H)) :=
  MonoidAlgebra.lift ℂ _ (FreeMonoid (Fin n)) (FreeMonoid.lift fun i => directionLinear (X i))

private theorem smoothWordAction_apply (X : Fin n → GroupLieAlgebra 𝓘E H)
    (P : MonoidAlgebra ℂ (FreeMonoid (Fin n)))
    (f : smoothScalarFunctions (E := E) (H := H)) :
    (smoothWordAction X P f).val = lieWordAction X P f.val := by
  have hw (w : FreeMonoid (Fin n)) (g : smoothScalarFunctions (E := E) (H := H)) :
      ((FreeMonoid.lift (fun i => directionLinear (X i))) w g).val = lieWordDerivative X w g.val := by
    induction w using FreeMonoid.inductionOn' with
    | one => rw [map_one, Module.End.one_apply, lieWordDerivative_one]
    | of_mul i w ih =>
      rw [map_mul, Module.End.mul_apply, FreeMonoid.lift_eval_of, lieWordDerivative_of_mul]
      change groupDirectionalValue 𝓘E (X i) _ = _
      rw [ih]
  rw [smoothWordAction, MonoidAlgebra.lift_apply, lieWordAction, Finsupp.sum, Finsupp.sum]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul, hw]

/-- Smooth solutions of a word equation form a subspace of the underlying functions. -/
private def wordSolutions (X : Fin n → GroupLieAlgebra 𝓘E H)
    (P : MonoidAlgebra ℂ (FreeMonoid (Fin n))) : Submodule ℂ (H → ℂ) :=
  (LinearMap.ker (smoothWordAction X P)).map (smoothScalarFunctions (E := E) (H := H)).subtype

private theorem mem_wordSolutions (X : Fin n → GroupLieAlgebra 𝓘E H)
    (P : MonoidAlgebra ℂ (FreeMonoid (Fin n))) (f : H → ℂ) :
    f ∈ wordSolutions X P ↔ ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ f ∧ ∀ x, lieWordAction X P f x = 0 := by
  rw [wordSolutions, Submodule.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨g.property, fun x => ?_⟩
    change lieWordAction X P g.val x = 0
    rw [← smoothWordAction_apply X P g, LinearMap.mem_ker.mp hg]
    rfl
  · rintro ⟨hf, he⟩
    let v : smoothScalarFunctions (E := E) (H := H) := ⟨f, hf⟩
    refine ⟨v, LinearMap.mem_ker.mpr (Subtype.ext ?_), rfl⟩
    rw [smoothWordAction_apply]
    exact funext he

end WordSolutions

section Adelic

variable (F : Type) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local notation "AInf" => InfiniteAdelicGroupPoints F G
local notation "Af" => FiniteAdelicGroupPoints F G
local notation "A" => AdelicGroupPoints F G

omit [IsAffineHom G.X.hom] in
/-- Inversion preserves archimedean Haar for a connected reductive group. -/
private theorem infiniteHaarInvInvariant (hG : IsConnectedReductive G) :
    (Measure.haar : Measure AInf).IsInvInvariant := by
  let haarAd : Measure A := Measure.haar
  have : haarAd.IsMulRightInvariant := adelicHaarUnimodularity.2 F G hG
  have hmod (a : AInf) : Measure.modularCharacter a = 1 := by
    rw [← Langlands.ProductMeasure.modularCharacter_prod_one (H := Af),
      ← show (split F G) (ofInfinite F G a) = (a, 1) by simp,
      Langlands.Aubert.General.modularCharacter_continuousMulEquiv]
    apply NNReal.coe_injective
    change (Measure.modularCharacterFun (ofInfinite F G a) : ℝ) = 1
    obtain ⟨test, ht⟩ := exists_continuous_nonneg_pos (1 : A)
    rw [Measure.modularCharacterFun_eq_haarScalarFactor haarAd,
      Measure.haarScalarFactor_eq_integral_div_of_continuous_nonneg_pos _ _ ht,
      map_mul_right_eq_self,
      ← Measure.haarScalarFactor_eq_integral_div_of_continuous_nonneg_pos haarAd haarAd ht,
      Measure.haarScalarFactor_self, NNReal.coe_one]
  have : (Measure.haar : Measure AInf).IsMulRightInvariant :=
    Langlands.Haar.isMulRightInvariant_of_modularCharacter_eq_one hmod _
  exact Langlands.isInvInvariant_of_isMulRightInvariant Measure.haar

omit [IsAffineHom G.X.hom] in
/-- A compactly supported archimedean reproducer and a common open finite level give
reproduction with respect to the fixed full adelic Haar measure. -/
private theorem lift_reproducingKernel (φ : A → ℂ) (hφ : Continuous φ)
    (L : Subgroup Af) (hLo : IsOpen (L : Set Af))
    (hL : ∀ l ∈ L, ∀ g : A, φ (g * ofFinite F G l) = φ g)
    (κ : AInf → ℂ) (hκ : Continuous κ) (hκc : HasCompactSupport κ)
    (hrep : ∀ g : A, φ g = ∫ a, φ (g * ofInfinite F G a) * κ a ∂(Measure.haar : Measure AInf)) :
    ∃ K : A → ℂ, Continuous K ∧ HasCompactSupport K ∧
      ∀ g : A, φ g = ∫ a, φ (g * a) * K a ∂(Measure.haar : Measure A) := by
  classical
  let : MeasurableSpace Af := borel Af
  have : BorelSpace Af := ⟨rfl⟩
  let U := L ⊓ (FiniteAdelicGroupPoints.compactOpenSubgroup F G).toSubgroup
  have hUo : IsOpen (U : Set Af) := hLo.inter (FiniteAdelicGroupPoints.compactOpenSubgroup F G).isOpen
  have hUclosed := U.isClosed_of_isOpen hUo
  have hUc : IsCompact (U : Set Af) :=
    (FiniteAdelicGroupPoints.isCompact_compactOpenSubgroup F G).of_isClosed_subset
      hUclosed inter_subset_right
  let μInf : Measure AInf := Measure.haar
  let μf : Measure Af := Measure.haar
  let haarAd : Measure A := Measure.haar
  let t := (μf (U : Set Af)).toReal
  have ht : 0 < t := ENNReal.toReal_pos
    (hUo.measure_pos μf ⟨1, U.one_mem⟩).ne' hUc.measure_lt_top.ne
  let χ := (U : Set Af).indicator (fun _ => ((t⁻¹ : ℝ) : ℂ))
  have hχ : Continuous χ := IsClopen.continuous_indicator ⟨hUclosed, hUo⟩ continuous_const
  have hχ0 {b : Af} (hb : b ∉ U) : χ b = 0 := indicator_of_notMem hb _
  have hχint : ∫ b, χ b ∂μf = 1 := by
    rw [integral_indicator_const _ hUo.measurableSet, measureReal_def]
    change t • ((t⁻¹ : ℝ) : ℂ) = 1
    rw [Complex.real_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ ht.ne', Complex.ofReal_one]
  let e := split F G
  let B (p : AInf × Af) := κ p.1 * χ p.2
  have hBc : Continuous B := (hκ.comp continuous_fst).mul (hχ.comp continuous_snd)
  have hBs : HasCompactSupport B := by
    apply HasCompactSupport.of_support_subset_isCompact (hκc.prod hUc)
    intro p hp
    refine ⟨subset_tsupport κ ?_, ?_⟩
    · exact fun h => hp (mul_eq_zero_of_left h _)
    · by_contra h
      exact hp (by simp [B, hχ0 h])
  let ν := (μInf.prod μf).map e.symm
  have : ν.IsHaarMeasure := e.symm.isHaarMeasure_map _
  let c := Measure.haarScalarFactor ν haarAd
  have hν : ν = (c : ℝ≥0∞) • haarAd := Measure.isMulLeftInvariant_eq_smul ν haarAd
  let K₀ := B ∘ e
  have hK₀c : Continuous K₀ := hBc.comp e.continuous
  have hK₀s : HasCompactSupport K₀ := hBs.comp_homeomorph e.toHomeomorph
  refine ⟨fun a => (c : ℂ) * K₀ a, continuous_const.mul hK₀c, ?_, ?_⟩
  · exact hK₀s.mul_left
  intro g
  let integrand (p : AInf × Af) := φ (g * e.symm p) * B p
  have hIntc : Continuous integrand :=
    (hφ.comp (continuous_const.mul e.symm.continuous)).mul hBc
  have hInt : Integrable integrand (μInf.prod μf) :=
    hIntc.integrable_of_hasCompactSupport hBs.mul_left
  have hfib (a : AInf) (b : Af) :
      integrand (a, b) = (φ (g * ofInfinite F G a) * κ a) * χ b := by
    by_cases hb : b ∈ U
    · have hpair : e.symm (a, b) = ofInfinite F G a * ofFinite F G b := by
        simp [e, pair, ← map_mul]
      change φ (g * e.symm (a, b)) * (κ a * χ b) = _
      rw [hpair, ← mul_assoc g, hL b hb.1, mul_assoc]
    · simp [integrand, B, hχ0 hb]
  have hProd : (∫ p, integrand p ∂(μInf.prod μf)) = φ g := by
    rw [integral_prod _ hInt, hrep g]
    apply integral_congr_ae (ae_of_all _ fun a => ?_)
    simp only [hfib, integral_const_mul, hχint, mul_one]
  calc
    φ g = ∫ p, integrand p ∂(μInf.prod μf) := hProd.symm
    _ = ∫ a, φ (g * a) * K₀ a ∂ν := by
      change _ = ∫ a, φ (g * a) * K₀ a ∂((μInf.prod μf).map e.symm.toHomeomorph.toMeasurableEquiv)
      rw [integral_map_equiv]
      apply integral_congr_ae (ae_of_all _ fun p => ?_)
      change φ (g * e.symm p) * B p = φ (g * e.symm p) * B (e (e.symm p))
      rw [e.apply_symm_apply]
    _ = ∫ a, φ (g * a) * ((c : ℂ) * K₀ a) ∂haarAd := by
      rw [hν, integral_smul_measure]
      change (c : ℝ) • (∫ a, φ (g * a) * K₀ a ∂haarAd) = _
      rw [Complex.real_smul, ← integral_const_mul]
      apply integral_congr_ae (ae_of_all _ fun a => ?_)
      change (c : ℂ) * (φ (g * a) * K₀ a) = _
      ring

end Adelic

/-- Harish-Chandra's adelic reproducing-kernel theorem with the original
plot-smoothness, compact finiteness and common centre-ideal hypotheses. -/
theorem adelicReproducingKernel : AdelicReproducingKernelStatement := by
  intro F _ _ G _ _ _ hG K d hsmooth hcalc hK Φ hΓ hΦ hKfin hZfin
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := InfiniteAdelicGroupPoints.smoothChartedSpace F G hsmooth
  let : LieGroup 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d) ∞
      (InfiniteAdelicGroupPoints F G) := InfiniteAdelicGroupPoints.smoothLieGroup F G hsmooth
  let Kinf := K.comap (ofInfinite F G).toMonoidHom
  let f := ofRationalSmoothFunction F G Φ hΓ hΦ
  have hk : IsAdelicInfiniteFinite F G Kinf f :=
    (isInfiniteSubgroupFiniteFunction_evaluate_iff F G Kinf f).mp hKfin
  have hz : IsAdelicCenterFinite F G hsmooth hcalc f :=
    (isCenterFiniteFunction_evaluate_iff F G hsmooth hcalc f).mp hZfin
  obtain ⟨n, r, X, Ptop, Plow, _, hr, htop, hlow, hsym, hsol⟩ :=
    exists_elliptic_slice_annihilator adelicAdaptedCasimir F G Kinf hsmooth hcalc hG
      hK.isMaximalCompact_comap_ofInfinite f hk hz
  let μInf : Measure (InfiniteAdelicGroupPoints F G) := Measure.haar
  have : μInf.IsInvInvariant := infiniteHaarInvInvariant F G hG
  obtain ⟨V, C, hV, hC, hest⟩ := exists_lieWord_l2_evaluation μInf hr X Ptop Plow htop hlow hsym
  let S := wordSolutions (H := InfiniteAdelicGroupPoints F G) X (Ptop + Plow)
  have hc (u : InfiniteAdelicGroupPoints F G → ℂ) (hu : u ∈ S) : Continuous u :=
    ((mem_wordSolutions X (Ptop + Plow) u).mp hu).1.continuous
  have hl (u : InfiniteAdelicGroupPoints F G → ℂ) (hu : u ∈ S) (a : InfiniteAdelicGroupPoints F G) :
      (fun x => u (a * x)) ∈ S := by
    obtain ⟨hu', hsu⟩ := (mem_wordSolutions X (Ptop + Plow) u).mp hu
    apply (mem_wordSolutions X (Ptop + Plow) _).mpr
    refine ⟨hu'.comp (contMDiff_const.mul contMDiff_id), fun x => ?_⟩
    rw [lieWordAction_leftTranslation]
    exact hsu (a * x)
  obtain ⟨κ, hκ, hκc, hkrep⟩ := exists_compact_reproducingKernel_of_l2_evaluation μInf S hc hl V hV C hC
    (fun u hu => let ⟨hu', he⟩ := (mem_wordSolutions X (Ptop + Plow) u).mp hu; hest u hu' he)
  have hrepro (g : AdelicGroupPoints F G) :
      Φ g = ∫ a, Φ (g * ofInfinite F G a) * κ a ∂μInf := by
    let a := infinite F G g
    let b := finite F G g
    let ψ := (finitePlotSmoothSlice F G b f).val
    have hψ : ψ ∈ S := (mem_wordSolutions X (Ptop + Plow) ψ).mpr
      ⟨(InfiniteAdelicGroupPoints.isPlotSmooth_iff_contMDiff F G hsmooth ψ).mp (finitePlotSmoothSlice F G b f).property, hsol b⟩
    have he : (fun x => ψ (a * x)) = fun x => Φ (g * ofInfinite F G x) := by
      funext x
      change Φ (pair F G (a * x) b) = _
      conv_rhs => rw [← pair_projections F G g, ofInfinite_eq_pair, AdelicGroupPoints.pair_mul, mul_one]
    have h := hkrep (fun x => ψ (a * x)) (hl ψ hψ a)
    have heval (x : InfiniteAdelicGroupPoints F G) : ψ (a * x) = Φ (g * ofInfinite F G x) :=
      congrFun he x
    have hone : ψ a = Φ g := by simpa only [map_one, mul_one] using heval 1
    simpa only [heval, hone, map_one, mul_one] using h
  obtain ⟨L, hLo, hL⟩ := hΦ.2.2
  exact lift_reproducingKernel F G Φ hΦ.1 L hLo hL κ hκ hκc hrepro

end Langlands.Global
