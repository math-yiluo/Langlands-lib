import Langlands.Global.RankinSelberg.ComplexAdjacentConvergence
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.MeasureTheory.Group.Prod

/-! # Compact averaging in the unfolded adjacent-rank integral -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap Langlands.Archimedean.ComplexDuality

namespace Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding

open ArchimedeanLocal (ComplexQuotientMeasureData complexNormalizedAbs)
open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open ComplexGodement (characterWeight normPower continuous_characterWeight)
open ComplexMaximalParabolicIntegration (normSqC_det_unitary)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}

local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "K" => unitaryCompact ℂ (r + 1)
local notation "Q" => LeftUnipotentQuotient r ℂ
local notation "Mat" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ
local notation "Vec" => Fin (r + 1) → ℂ

local instance adjacentAverageUnitaryCompact : CompactSpace K :=
  ComplexDuality.compactSpace_unitaryCompact (r + 1)
local instance adjacentAverageGLSecondCountable : SecondCountableTopology G :=
  Units.isInducing_embedProduct.secondCountableTopology

private theorem schwartzLeftTranslate (Φ : 𝓢(Mat, ℂ)) (k : K) :
    ∃ Ψ : 𝓢(Mat, ℂ), (Ψ : Mat → ℂ) = fun X => Φ (k.val⁻¹.val * X) := by
  let e := (Units.mulLeftLinearEquiv ℝ Mat k.val⁻¹).toContinuousLinearEquiv
  exact ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e Φ, rfl⟩

private theorem integrable_compactTestFamily (D : ComplexQuotientMeasureData r) [SFinite D.measure]
    (ν : Measure G) [ν.IsHaarMeasure] [SFinite ν] (κ : Measure K) [IsFiniteMeasure κ]
    (u : K → K) (hu : Continuous u) (w : K → ℂ) (hw : Continuous w)
    (d : ComplexCharacterData) (p : ℂ) (Φ : 𝓢(Mat, ℂ)) (φ : 𝓢(Vec, ℂ))
    (hΦ : FiniteDimensional ℂ
      (Submodule.span ℂ (Set.range fun k : K => fun X => Φ (k.val⁻¹.val * X))))
    (a : ℂˣ) (ds es : List ComplexCharacterData)
    (W : complexWhittakerModel r ds a) (V : complexWhittakerModel r es (-a)) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (fun x : K × (G × Q) => w x.1 *
        unfoldedKernel d p s (fun X => Φ ((u x.1).val⁻¹.val * X)) φ W.val V.val x.2)
        (κ.prod (ν.prod D.measure)) := by
  classical
  let S := Submodule.span ℂ (Set.range fun k : K => fun X => Φ (k.val⁻¹.val * X))
  let : FiniteDimensional ℂ S := hΦ
  let F : 𝓢(Mat, ℂ) →ₗ[ℂ] (Mat → ℂ) :=
    { toFun := fun Ψ => Ψ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hS : S ≤ F.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact schwartzLeftTranslate Φ k
  let b := Module.finBasis ℂ S
  choose Ψ hΨ using fun i => hS (b i).2
  let shift (k : K) : S :=
    ⟨fun X => Φ ((u k).val⁻¹.val * X), Submodule.subset_span ⟨u k, rfl⟩⟩
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
      exact Φ.continuous.comp
        ((Units.continuous_val.comp (continuous_subtype_val.comp hu).inv).matrix_mul continuous_const)
    | zero => exact continuous_const
    | add _ _ _ _ h h' => exact h.add h'
    | smul c _ _ h => exact continuous_const.smul h
  choose σ hσ using fun i => complexAdjacentConvergence D ν d p (Ψ i) φ a ds es W V
  obtain ⟨β, hβ⟩ := (Set.finite_range σ).bddAbove
  refine ⟨β, fun s hs => ?_⟩
  have hsum (k : K) (X : Mat) :
      Φ ((u k).val⁻¹.val * X) = ∑ i, b.coord i (shift k) * Ψ i X := by
    have hb := congrArg (fun v : S => v.val X) (b.sum_repr (shift k))
    simpa only [shift, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Module.Basis.coord_apply, ← hΨ, F, LinearMap.coe_mk, AddHom.coe_mk] using hb.symm
  refine (integrable_finsetSum Finset.univ (fun i _ =>
    ((hw.mul (hcoord (b.coord i))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).mul_prod
        (hσ i s ((hβ (Set.mem_range_self i)).trans_lt hs)))).congr (ae_of_all _ fun x => ?_)
  simp only [unfoldedKernel, hsum, Finset.sum_mul, Finset.mul_sum, Pi.mul_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem characterWeight_unitary (d : ComplexCharacterData) (s : ℂ) (k : K) :
    characterWeight d s (determinant k.val) = (d.character (determinant k.val) : ℂ) := by
  change (d.character (determinant k.val) : ℂ) * (ComplexMaximalParabolicIntegration.normSqC
    k.val.val.det) ^ s = _
  rw [normSqC_det_unitary k, Complex.one_cpow, mul_one]

/-- A reproducing compact average in the square test becomes an average of the
right-translated Whittaker function. The unfolded product is absolutely integrable
in a right half-plane after inserting the compact variable. -/
def ComplexAdjacentCompactAverageStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData r) [SFinite D.measure] (ν : Measure G) [ν.IsHaarMeasure]
    [SFinite ν] (κ : Measure K) [IsFiniteMeasure κ] (u : K → K), Continuous u →
  ∀ (w : K → ℂ), Continuous w →
  ∀ (d : ComplexCharacterData) (p : ℂ) (Φ : 𝓢(Mat, ℂ)) (φ : 𝓢(Vec, ℂ)),
    FiniteDimensional ℂ
      (Submodule.span ℂ (Set.range fun k : K => fun X => Φ (k.val⁻¹.val * X))) →
    (∀ X, ∫ k, w k * (d.character ((determinant (u k).val)⁻¹) : ℂ) *
      Φ ((u k).val⁻¹.val * X) ∂κ = Φ X) →
  ∀ (a : ℂˣ) (ds es : List ComplexCharacterData)
    (W : complexWhittakerModel r ds a) (V : complexWhittakerModel r es (-a)),
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      let I := fun x : G × Q => Φ x.1.val * characterWeight d (p + s) (determinant x.1) *
        ArchimedeanLocal.equalIntegrand complexNormalizedAbs W.val
          (fun g => ∫ k, w k * V.val (g * (u k).val * x.1) ∂κ) φ s x.2
      Integrable I (ν.prod D.measure) ∧
        (∫ x, unfoldedKernel d p s Φ φ W.val V.val x ∂ν.prod D.measure) =
          ∫ x, I x ∂ν.prod D.measure

theorem complexAdjacentCompactAverage : ComplexAdjacentCompactAverageStatement (r := r) := by
  intro D _ ν _ _ κ _ u hu w hw d p Φ φ hΦ hrec a ds es W V
  let t (k : K) : ℂ := (d.character ((determinant (u k).val)⁻¹) : ℂ)
  have hu' : Continuous fun k : K => (u k).val := continuous_subtype_val.comp hu
  have ht : Continuous t := by
    have hdet : Continuous fun k : K => (determinant (u k).val)⁻¹ :=
      (determinantContinuous.continuous.comp hu').inv
    have hzero (z : ℂˣ) : characterWeight d 0 z = (d.character z : ℂ) := by
      change (d.character z : ℂ) * ComplexMaximalParabolicIntegration.normSqC (z : ℂ) ^ (0 : ℂ) = _
      rw [Complex.cpow_zero, mul_one]
    simpa only [t, Function.comp_def, hzero] using (continuous_characterWeight d 0).comp hdet
  obtain ⟨σ, hσ⟩ := integrable_compactTestFamily D ν κ u hu
    (fun k => w k * t k) (hw.mul ht) d p Φ φ hΦ a ds es W V
  refine ⟨σ, fun s hs => ?_⟩
  let μ := ν.prod D.measure
  let J (x : K × (G × Q)) := w x.1 * t x.1 *
    unfoldedKernel d p s (fun X => Φ ((u x.1).val⁻¹.val * X)) φ W.val V.val x.2
  let I (x : K × (G × Q)) := w x.1 *
    (Φ x.2.1.val * characterWeight d (p + s) (determinant x.2.1) *
      ArchimedeanLocal.equalIntegrand complexNormalizedAbs W.val
        (fun g => V.val (g * (u x.1).val * x.2.1)) φ s x.2.2)
  have hJ : Integrable J (κ.prod μ) := hσ s hs
  let e : K × (G × Q) ≃ᵐ K × (G × Q) :=
    { toFun := fun x => (x.1, (u x.1).val * x.2.1, x.2.2)
      invFun := fun x => (x.1, (u x.1).val⁻¹ * x.2.1, x.2.2)
      left_inv := by rintro ⟨k, g, q⟩; simp
      right_inv := by rintro ⟨k, g, q⟩; simp
      measurable_toFun := measurable_fst.prodMk
        (((hu'.measurable.comp measurable_fst).mul measurable_snd.fst).prodMk measurable_snd.snd)
      measurable_invFun := measurable_fst.prodMk
        (((hu'.inv.measurable.comp measurable_fst).mul measurable_snd.fst).prodMk measurable_snd.snd) }
  have he : MeasurePreserving e (κ.prod μ) (κ.prod μ) := by
    refine (MeasurePreserving.id κ).skew_product
      (g := fun k (x : G × Q) => ((u k).val * x.1, x.2)) ?_ (ae_of_all _ fun k => ?_)
    · exact ((hu'.measurable.comp measurable_fst).mul measurable_snd.fst).prodMk measurable_snd.snd
    · exact ((measurePreserving_mul_left ν (u k).val).prod (MeasurePreserving.id D.measure)).map_eq
  have hmatrix (k : K) (g : G) :
      t k * (Φ ((u k).val⁻¹.val * ((u k).val * g).val) *
        characterWeight d (p + s) (determinant ((u k).val * g))) =
      Φ g.val * characterWeight d (p + s) (determinant g) := by
    have hcancel : t k * (d.character (determinant (u k).val) : ℂ) = 1 := by
      dsimp only [t]
      rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
    rw [← Units.val_mul, inv_mul_cancel_left, map_mul, map_mul, characterWeight_unitary]
    calc
      _ = (t k * (d.character (determinant (u k).val) : ℂ)) *
          (Φ g.val * characterWeight d (p + s) (determinant g)) := by ring
      _ = _ := by rw [hcancel, one_mul]
  have hchange : J ∘ e = I := by
    funext x
    rcases x with ⟨k, g, q⟩
    change w k * t k *
      unfoldedKernel d p s (fun X => Φ ((u k).val⁻¹.val * X)) φ W.val V.val
        ((u k).val * g, q) =
      w k * (Φ g.val * characterWeight d (p + s) (determinant g) *
        ArchimedeanLocal.equalIntegrand complexNormalizedAbs W.val
          (fun v => V.val (v * (u k).val * g)) φ s q)
    simp only [unfoldedKernel, ArchimedeanLocal.equalIntegrand, mul_assoc]
    simp only [← mul_assoc]
    rw [show w k * t k * Φ ((u k).val⁻¹.val * ((u k).val * g).val) *
        characterWeight d (p + s) (determinant ((u k).val * g)) =
        w k * (t k * (Φ ((u k).val⁻¹.val * ((u k).val * g).val) *
          characterWeight d (p + s) (determinant ((u k).val * g)))) by ring,
      hmatrix, ← mul_assoc]
  have hI : Integrable I (κ.prod μ) := hchange ▸ he.integrable_comp_of_integrable hJ
  let A (x : G × Q) := Φ x.1.val * characterWeight d (p + s) (determinant x.1) *
    ArchimedeanLocal.equalIntegrand complexNormalizedAbs W.val
      (fun g => ∫ k, w k * V.val (g * (u k).val * x.1) ∂κ) φ s x.2
  have hIavg (x : G × Q) : (∫ k, I (k, x) ∂κ) = A x := by
    let g := x.2.out
    let c := Φ x.1.val * characterWeight d (p + s) (determinant x.1) *
      W.val g * φ (Langlands.RankinSelberg.lastRow g) *
      ArchimedeanLocal.detPower complexNormalizedAbs g s
    calc
      (∫ k, I (k, x) ∂κ) = c * ∫ k, w k * V.val (g * (u k).val * x.1) ∂κ := by
        rw [← integral_const_mul]
        exact integral_congr_ae (ae_of_all _ fun k => by
          simp only [I, c, g, ArchimedeanLocal.equalIntegrand]
          ring)
      _ = A x := by
        simp only [A, c, g, ArchimedeanLocal.equalIntegrand]
        ring
  have hJavg (x : G × Q) : (∫ k, J (k, x) ∂κ) =
      unfoldedKernel d p s Φ φ W.val V.val x := by
    unfold unfoldedKernel
    rw [← hrec x.1.val, ← integral_mul_const, ← integral_mul_const]
    apply integral_congr_ae
    exact ae_of_all _ fun k => by simp only [J, t, unfoldedKernel, mul_assoc]
  change Integrable A μ ∧ (∫ x, unfoldedKernel d p s Φ φ W.val V.val x ∂μ) = ∫ x, A x ∂μ
  refine ⟨hI.integral_prod_right.congr (ae_of_all _ hIavg), ?_⟩
  calc
    (∫ x, unfoldedKernel d p s Φ φ W.val V.val x ∂μ) = ∫ x, ∫ k, J (k, x) ∂κ ∂μ :=
      integral_congr_ae (ae_of_all _ fun x => (hJavg x).symm)
    _ = ∫ x, J x ∂κ.prod μ := (integral_prod_symm J hJ).symm
    _ = ∫ x, I x ∂κ.prod μ := by
      rw [← hchange]
      exact (he.integral_comp' J).symm
    _ = ∫ x, ∫ k, I (k, x) ∂κ ∂μ := integral_prod_symm I hI
    _ = _ := integral_congr_ae (ae_of_all _ hIavg)

end Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding
