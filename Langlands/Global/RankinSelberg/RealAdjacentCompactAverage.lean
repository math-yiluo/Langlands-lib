import Langlands.Global.RankinSelberg.RealAdjacentConvergence
import Langlands.Global.RankinSelberg.RealLocalEqualShiftedProducts
import Mathlib.MeasureTheory.Group.Prod

/-! # Compact averaging in the real unfolded adjacent-rank integral

See the paired Markdown file.
-/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap
open Langlands.RankinSelberg (LeftUnipotentQuotient lastRow)
open Langlands.QuotientIntegration
open Langlands.LocalFactor.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealJacquet

open ArchimedeanLocal RealEqualConvergence
open RealGodement (realCompactMatrixTranslate)

attribute [local instance] archimedeanEquationRealGLMeasurable
  archimedeanEquationRealGLBorel archimedeanEquationRealNMeasurable
  archimedeanEquationRealNBorel archimedeanEquationRealQMeasurable
  archimedeanEquationRealQBorel

variable {r : ℕ}

local notation "H" => Langlands.GeneralLinear (r + 1) ℝ
local notation "Q" => LeftUnipotentQuotient r ℝ
local notation "N" => GeneralLinear.upperUnipotent (r + 1) ℝ
local notation "Mat" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "Rows" => Fin (r + 1) → ℝ
local notation "P" => ArchimedeanLocal.detPower realNormalizedAbs

local instance adjacentAverageMatrixSecondCountable : SecondCountableTopology Mat :=
  inferInstanceAs (SecondCountableTopology (Fin (r + 1) → Fin (r + 1) → ℝ))
local instance adjacentAverageGLSecondCountable : SecondCountableTopology H :=
  (Units.isOpenEmbedding_val (R := Mat)).isInducing.secondCountableTopology
local instance adjacentAverageQuotientSigmaCompact : SigmaCompactSpace Q := by
  have hq := leftQuotient_isOpenQuotientMap N
  apply isSigmaCompact_univ_iff.mp
  rw [← Set.range_eq_univ.mpr hq.surjective]
  exact isSigmaCompact_range hq.continuous

private theorem schwartzLeftTranslate (F : 𝓢(Mat, ℂ)) (g : H) :
    ∃ Ψ : 𝓢(Mat, ℂ), (Ψ : Mat → ℂ) = fun X => F ((g⁻¹).val * X) := by
  let e := (Units.mulLeftLinearEquiv ℝ Mat (g⁻¹)).toContinuousLinearEquiv
  exact ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e F, rfl⟩

/-- The determinant character takes inverse values at `g` and `g⁻¹`. -/
private theorem detCharacter_inv_mul (c : RealCharacterData) (g : H) :
    (c.character (GeneralLinear.determinant g⁻¹) : ℂ) * detCharacter c.character.toMonoidHom g = 1 := by
  unfold detCharacter
  change (c.character (GeneralLinear.determinant g⁻¹) : ℂ) *
    (c.character (GeneralLinear.determinant g) : ℂ) = 1
  rw [← Units.val_mul, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, Units.val_one]

private theorem detPower_eq_one_mul (g z : H) (hg : |g.val.det| = 1) (s : ℂ) :
    P (g * z) s = P z s := by
  rw [realDetPower_mul]
  have h1 : P g s = 1 := by
    simp only [ArchimedeanLocal.detPower, realNormalizedAbs, hg, Real.log_one, Complex.ofReal_zero,
      mul_zero, Complex.exp_zero]
  rw [h1, one_mul]

/-- The compact family of left-translated tests in the unfolded kernel is jointly integrable
with the compact variable, on a common right half-plane. -/
theorem integrable_realAdjacentCompactFamily (D : RealQuotientMeasureData r)
    {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsFiniteMeasure ν]
    (ι : K →* H) (hι : Continuous ι) (w : K → ℂ) (hw : Continuous w)
    (c : RealCharacterData) (F : 𝓢(Mat, ℂ))
    (hfin : FiniteDimensional ℂ
      (Submodule.span ℂ (Set.range fun k : K => fun X : Mat => F (((ι k)⁻¹).val * X))))
    (f : Rows → ℂ) (hf : Continuous f) (hfd : HasRapidDecay f) (U V : H → ℂ)
    (hU : Continuous U) (hV : Continuous V)
    (hinv : ∀ u ∈ N, ∀ g z : H, U (u * g) * V (u * g * z) = U g * V (g * z))
    (hgU : HasGauge U) (hVg : ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ g, ‖V g‖ ≤ C * realMatrixHeight g ^ M) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (fun x : K × (Q × H) => w x.1 *
        realAdjacentUnfoldedKernel c.character.toMonoidHom (fun X => F (((ι x.1)⁻¹).val * X))
          f U V s x.2)
        (ν.prod (D.measure.prod D.groupHaar)) := by
  classical
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let : D.measure.Regular := D.compatible.regular
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let S := Submodule.span ℂ (Set.range fun k : K => fun X : Mat => F (((ι k)⁻¹).val * X))
  let : FiniteDimensional ℂ S := hfin
  let Fl : 𝓢(Mat, ℂ) →ₗ[ℂ] (Mat → ℂ) :=
    { toFun := fun Ψ => Ψ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hS : S ≤ Fl.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact schwartzLeftTranslate F (ι k)
  let b := Module.finBasis ℂ S
  choose Ψ hΨ using fun i => hS (b i).2
  let shift (k : K) : S :=
    ⟨fun X => F (((ι k)⁻¹).val * X), Submodule.subset_span ⟨k, rfl⟩⟩
  let ev (X : Mat) : Module.Dual ℂ S := (LinearMap.proj X).comp S.subtype
  have hcoord (ℓ : Module.Dual ℂ S) : Continuous fun k => ℓ (shift k) := by
    have hmem : ℓ ∈ Submodule.span ℂ (Set.range ev) := by
      apply FiniteDimensional.mem_span_of_iInf_ker_le_ker
      intro v hv
      have hv0 : v = 0 := by
        apply Subtype.ext
        funext X
        exact LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hv X)
      simp [hv0]
    induction hmem using Submodule.span_induction with
    | mem l hl =>
      obtain ⟨X, rfl⟩ := hl
      exact F.continuous.comp
        ((Units.continuous_val.comp hι.inv).matrix_mul continuous_const)
    | zero => exact continuous_const
    | add _ _ _ _ h h' => exact h.add h'
    | smul c _ _ h => exact continuous_const.smul h
  choose σ hσ using fun i => realAdjacentConvergence (r := r) D c (Ψ i) f U V hU hV hf hfd hinv
    hgU hVg
  obtain ⟨β, hβ⟩ := (Set.finite_range σ).bddAbove
  refine ⟨β, fun s hs => ?_⟩
  have hsum (k : K) (X : Mat) :
      F (((ι k)⁻¹).val * X) = ∑ i, b.coord i (shift k) * Ψ i X := by
    have hb := congrArg (fun v : S => v.val X) (b.sum_repr (shift k))
    simpa only [shift, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Module.Basis.coord_apply, ← hΨ, Fl, LinearMap.coe_mk, AddHom.coe_mk] using hb.symm
  refine (integrable_finsetSum Finset.univ (fun i _ =>
    ((hw.mul (hcoord (b.coord i))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).mul_prod
        (hσ i s ((hβ (Set.mem_range_self i)).trans_lt hs)))).congr (ae_of_all _ fun x => ?_)
  simp only [realAdjacentUnfoldedKernel, realAdjacentMatrixWeight, hsum, Finset.sum_mul,
    Finset.mul_sum, Pi.mul_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- A reproducing compact weight in the square test becomes an average of right translates
of the second function. -/
def RealAdjacentCompactAverageStatement : Prop :=
  ∀ (D : RealQuotientMeasureData r)
    {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsFiniteMeasure ν]
    (ι : K →* H), Continuous ι → (∀ k, |(ι k).val.det| = 1) →
  ∀ (κ : K → ℂ), Continuous κ →
  ∀ (c : RealCharacterData) (F : 𝓢(Mat, ℂ)),
    FiniteDimensional ℂ
      (Submodule.span ℂ (Set.range fun k : K => fun X : Mat => F (((ι k)⁻¹).val * X))) →
    (∀ A, ∫ k, κ k * realCompactMatrixTranslate c F (ι k) A ∂ν = F A) →
  ∀ (f : Rows → ℂ), Continuous f → HasRapidDecay f →
  ∀ (U V : H → ℂ), Continuous U → Continuous V →
    (∀ u ∈ N, ∀ g z : H, U (u * g) * V (u * g * z) = U g * V (g * z)) →
    HasGauge U → (∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ g, ‖V g‖ ≤ C * realMatrixHeight g ^ M) →
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      let I := fun p : Q × H =>
        realEqualIntegrand U (fun x => ∫ k, κ k * V (x * ι k * p.2) ∂ν) f s p.1 *
          realAdjacentMatrixWeight c.character.toMonoidHom F s p.2
      Integrable I (D.measure.prod D.groupHaar) ∧
        (∫ p, realAdjacentUnfoldedKernel c.character.toMonoidHom F f U V s p
          ∂(D.measure.prod D.groupHaar)) = ∫ p, I p ∂(D.measure.prod D.groupHaar)

theorem realAdjacentCompactAverage : RealAdjacentCompactAverageStatement (r := r) := by
  intro D K _ _ _ _ _ _ ν _ ι hι hdet κ hκ c F hfin hrep f hf hfd U V hU hV hinv hgU hVg
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let : D.measure.Regular := D.compatible.regular
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let t (k : K) : ℂ := (c.character (GeneralLinear.determinant (ι k)⁻¹) : ℂ)
  have ht : Continuous t := by
    have hd : Continuous fun k : K => GeneralLinear.determinant (ι k)⁻¹ :=
      GeneralLinear.determinantContinuous.continuous.comp hι.inv
    exact Units.continuous_val.comp (c.character.continuous.comp hd)
  obtain ⟨σ, hσ⟩ := integrable_realAdjacentCompactFamily D ν ι hι (fun k => κ k * t k)
    (hκ.mul ht) c F hfin f hf hfd U V hU hV hinv hgU hVg
  refine ⟨σ, fun s hs => ?_⟩
  let μ := D.measure.prod D.groupHaar
  let η := c.character.toMonoidHom
  let J (x : K × (Q × H)) := κ x.1 * t x.1 *
    realAdjacentUnfoldedKernel η (fun X => F (((ι x.1)⁻¹).val * X)) f U V s x.2
  let I (x : K × (Q × H)) := κ x.1 *
    (realEqualIntegrand U (fun y => V (y * ι x.1 * x.2.2)) f s x.2.1 *
      realAdjacentMatrixWeight η F s x.2.2)
  have hJ : Integrable J (ν.prod μ) := hσ s hs
  let e : K × (Q × H) ≃ᵐ K × (Q × H) :=
    { toFun := fun x => (x.1, x.2.1, ι x.1 * x.2.2)
      invFun := fun x => (x.1, x.2.1, (ι x.1)⁻¹ * x.2.2)
      left_inv := by rintro ⟨k, q, z⟩; simp
      right_inv := by rintro ⟨k, q, z⟩; simp
      measurable_toFun := measurable_fst.prodMk (measurable_snd.fst.prodMk
        ((hι.measurable.comp measurable_fst).mul measurable_snd.snd))
      measurable_invFun := measurable_fst.prodMk (measurable_snd.fst.prodMk
        ((hι.inv.measurable.comp measurable_fst).mul measurable_snd.snd)) }
  have he : MeasurePreserving e (ν.prod μ) (ν.prod μ) := by
    refine (MeasurePreserving.id ν).skew_product
      (g := fun k (x : Q × H) => (x.1, ι k * x.2)) ?_ (ae_of_all _ fun k => ?_)
    · exact measurable_snd.fst.prodMk ((hι.measurable.comp measurable_fst).mul measurable_snd.snd)
    · exact ((MeasurePreserving.id D.measure).prod
        (measurePreserving_mul_left D.groupHaar (ι k))).map_eq
  have hweight (k : K) (z : H) :
      t k * realAdjacentMatrixWeight η (fun X => F (((ι k)⁻¹).val * X)) s (ι k * z) =
        realAdjacentMatrixWeight η F s z := by
    unfold realAdjacentMatrixWeight
    dsimp only
    rw [← Units.val_mul, inv_mul_cancel_left, detCharacter_mul,
      detPower_eq_one_mul _ _ (hdet k)]
    have hc := detCharacter_inv_mul c (ι k)
    calc
      _ = (t k * detCharacter η (ι k)) * (F z.val * detCharacter η z * P z (s + (r : ℂ) / 2)) := by
        ring
      _ = _ := by rw [show t k * detCharacter η (ι k) = 1 from hc, one_mul]
  have hchange : J ∘ e = I := by
    funext x
    rcases x with ⟨k, q, z⟩
    change κ k * t k * realAdjacentUnfoldedKernel η (fun X => F (((ι k)⁻¹).val * X)) f U V s
        (q, ι k * z) = κ k * (realEqualIntegrand U (fun y => V (y * ι k * z)) f s q *
          realAdjacentMatrixWeight η F s z)
    simp only [realAdjacentUnfoldedKernel]
    rw [← hweight k z]
    simp only [mul_assoc]
    ring_nf
  have hI : Integrable I (ν.prod μ) := hchange ▸ he.integrable_comp_of_integrable hJ
  let A (p : Q × H) := realEqualIntegrand U (fun x => ∫ k, κ k * V (x * ι k * p.2) ∂ν) f s p.1 *
    realAdjacentMatrixWeight η F s p.2
  have hIavg (p : Q × H) : (∫ k, I (k, p) ∂ν) = A p := by
    let g := p.1.out
    let C := U g * f (lastRow g) * P g s * realAdjacentMatrixWeight η F s p.2
    calc
      (∫ k, I (k, p) ∂ν) = C * ∫ k, κ k * V (g * ι k * p.2) ∂ν := by
        rw [← integral_const_mul]
        exact integral_congr_ae (ae_of_all _ fun k => by
          simp only [I, C, g, realEqualIntegrand, ArchimedeanLocal.equalIntegrand]
          ring)
      _ = A p := by
        simp only [A, C, g, realEqualIntegrand, ArchimedeanLocal.equalIntegrand]
        ring
  have hJavg (p : Q × H) : (∫ k, J (k, p) ∂ν) =
      realAdjacentUnfoldedKernel η F f U V s p := by
    have hrep' := hrep p.2.val
    unfold realAdjacentUnfoldedKernel realAdjacentMatrixWeight
    rw [← hrep', ← integral_mul_const, ← integral_mul_const, ← integral_const_mul]
    apply integral_congr_ae
    refine ae_of_all _ fun k => ?_
    simp only [J, t, realAdjacentUnfoldedKernel, realAdjacentMatrixWeight,
      realCompactMatrixTranslate]
    ring
  change Integrable A μ ∧ (∫ p, realAdjacentUnfoldedKernel η F f U V s p ∂μ) = ∫ p, A p ∂μ
  refine ⟨hI.integral_prod_right.congr (ae_of_all _ hIavg), ?_⟩
  calc
    (∫ p, realAdjacentUnfoldedKernel η F f U V s p ∂μ) = ∫ p, ∫ k, J (k, p) ∂ν ∂μ :=
      integral_congr_ae (ae_of_all _ fun p => (hJavg p).symm)
    _ = ∫ x, J x ∂ν.prod μ := (integral_prod_symm J hJ).symm
    _ = ∫ x, I x ∂ν.prod μ := by
      rw [← hchange]
      exact (he.integral_comp' J).symm
    _ = ∫ p, ∫ k, I (k, p) ∂ν ∂μ := integral_prod_symm I hI
    _ = _ := integral_congr_ae (ae_of_all _ hIavg)

/-- A finite coefficient expansion of the second factor separates the averaged unfolded
product into smaller equal-rank integrals and matrix integrals. -/
def RealAdjacentProductExpansionStatement : Prop :=
  ∀ (D : RealQuotientMeasureData r) (η : ℝˣ →* ℂˣ) (F : Mat → ℂ) (f : Rows → ℂ) (s : ℂ)
    (U : H → ℂ) (m : ℕ) (W C : Fin m → H → ℂ) (V : H → H → ℂ),
    (∀ x z, V x z = ∑ j, W j x * C j z) →
    (∀ j, Integrable (fun z => realAdjacentMatrixWeight η F s z * C j z) D.groupHaar) →
    (∀ j, Integrable (realEqualIntegrand U (W j) f s) D.measure) →
    (∫ p : Q × H, realEqualIntegrand U (fun x => V x p.2) f s p.1 *
      realAdjacentMatrixWeight η F s p.2 ∂(D.measure.prod D.groupHaar)) =
      ∑ j, realEqualIntegral D U (W j) f s *
        ∫ z, realAdjacentMatrixWeight η F s z * C j z ∂D.groupHaar

theorem realAdjacentProductExpansion : RealAdjacentProductExpansionStatement (r := r) := by
  intro D η F f s U m W C V hV hC hW
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let : D.measure.Regular := D.compatible.regular
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let Z (j : Fin m) (z : H) := realAdjacentMatrixWeight η F s z * C j z
  let E (j : Fin m) (q : Q) := realEqualIntegrand U (W j) f s q
  have hpoint (p : Q × H) : realEqualIntegrand U (fun x => V x p.2) f s p.1 *
      realAdjacentMatrixWeight η F s p.2 = ∑ j, E j p.1 * Z j p.2 := by
    simp only [Z, E, realEqualIntegrand, ArchimedeanLocal.equalIntegrand, hV, Finset.sum_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  simp_rw [hpoint]
  rw [integral_finsetSum Finset.univ (fun j _ => (hW j).mul_prod (hC j))]
  refine Finset.sum_congr rfl fun j _ => ?_
  change (∫ p : Q × H, E j p.1 * Z j p.2 ∂D.measure.prod D.groupHaar) =
    (∫ q, E j q ∂D.measure) * ∫ z, Z j z ∂D.groupHaar
  exact integral_prod_mul (E j) (Z j)

end Langlands.Global.RankinSelbergGlobal.RealJacquet
