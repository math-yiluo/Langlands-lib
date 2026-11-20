import Langlands.Global.RankinSelberg.ComplexGodementGeneratorFamily
import Langlands.Global.RankinSelberg.ComplexJacquetRankOne

/-! # Uniform entire Jacquet continuation in all complex ranks -/

noncomputable section

open MeasureTheory Set Filter
open scoped Classical Matrix Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation

open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open Langlands.Archimedean.ComplexPrincipalSeriesExtension (extensionLinear)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open ComplexCompactProfileFamily (characterList IsCompactProfile standardSection standardSection_mem
  standardSection_compactRestriction compactRestriction continuous_standardSection_family differentiable_standardSection)
open ComplexGodement (SmallerProfile smallerWeights smallerExponents addedCharacter retainedCharacters
  smallerSection characterList_cons godementSection)
open ComplexGodementGeneratorFamily (generatorFamily complexGodementGeneratorFamily
  isStrictlyDominant_characterList eq_of_differentiable_eqOn_chamber)
open ComplexGodementJacquetComparison (openCellIntegral)
open ComplexGodementWhittakerFamily (HasUniformSimpleRootBound)
open ComplexJacquetChamberHolomorphic (chamber)
open ComplexJacquetUnipotentMeasure (entryHaar)
open ComplexLocalIwasawa (alpha)
open RealConvergenceAnalysis (rootPos)

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel ArchimedeanLocal.archimedeanComplexNMeasurable
  ArchimedeanLocal.archimedeanComplexNBorel

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "G'" => Langlands.GeneralLinear (r + 1 + 1) ℂ
local notation "U'" => Matrix.unitaryGroup (Fin (r + 1 + 1)) ℂ
local notation "P" => Fin (r + 1) → ℂ
local notation "P'" => Fin (r + 1 + 1) → ℂ
local notation "L'" => Fin (r + 1 + 1) → ℤ

private theorem uniform_bound_mono {X : Type*} {S T : Set X} {W : X → G' → ℂ}
    (hST : S ⊆ T) (hW : HasUniformSimpleRootBound (r := r + 1) T W) :
    HasUniformSimpleRootBound (r := r + 1) S W := by
  obtain ⟨N, hN⟩ := hW
  refine ⟨N, fun J => ?_⟩
  obtain ⟨C, hC, hbound⟩ := hN J
  exact ⟨C, hC, fun p hp g => hbound p (hST hp) g⟩

private theorem uniform_bound_sum {X I : Type*} [Fintype I] (S : Set X)
    (F : I → X → G' → ℂ) (c : X → I → ℂ) (D : I → ℝ)
    (hD : ∀ i, 0 ≤ D i) (hc : ∀ i p, p ∈ S → ‖c p i‖ ≤ D i)
    (hF : ∀ i, HasUniformSimpleRootBound (r := r + 1) S (F i)) :
    HasUniformSimpleRootBound (r := r + 1) S (fun p g => ∑ i, c p i * F i p g) := by
  choose N hN using hF
  let M := Finset.univ.sup N
  refine ⟨M, fun J => ?_⟩
  choose C hC using fun i => hN i J
  refine ⟨∑ i, D i * C i, Finset.sum_nonneg (fun i _ => mul_nonneg (hD i) (hC i).1), fun p hp g => ?_⟩
  let A := ∑ j, |alpha g j|
  let R := (J : ℝ) * rootPos (r := r + 1) (alpha g)
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hE (i : I) : Real.exp ((N i : ℝ) * A - R) ≤ Real.exp ((M : ℝ) * A - R) := by
    have hN' : (N i : ℝ) ≤ M := by exact_mod_cast (Finset.le_sup (f := N) (Finset.mem_univ i))
    exact Real.exp_monotone (sub_le_sub_right (mul_le_mul_of_nonneg_right hN' hA) R)
  change ‖∑ i, c p i * F i p g‖ ≤ (∑ i, D i * C i) * Real.exp ((M : ℝ) * A - R)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, mul_assoc]
  exact mul_le_mul (hc i p hp) (((hC i).2 p hp g).trans
    (mul_le_mul_of_nonneg_left (hE i) (hC i).1)) (norm_nonneg _) (hD i)

private def rowFrame {X J : Type*} {n : ℕ} (v : J → X → Fin n → ℂ) (b : Fin n → J) (p : X) :
    Matrix (Fin n) (Fin n) ℂ := fun i j => v (b i) p j

private theorem finite_frame_continuation {X J : Type*} [MetricSpace X] {n : ℕ}
    (v : J → X → Fin n → ℂ) (F : J → X → G' → ℂ) (u : X → G' → Fin n → ℂ) (c : Fin n → ℂ)
    (hv : ∀ j i, Continuous (fun p => v j p i))
    (hframe : ∀ p, ∃ b : Fin n → J, (rowFrame v b p).det ≠ 0)
    (hFc : ∀ j p, Continuous (F j p))
    (hFb : ∀ j p, ∃ δ : ℝ, 0 < δ ∧ HasUniformSimpleRootBound (r := r + 1) (Metric.ball p δ) (F j))
    (he : ∀ j p g, v j p ⬝ᵥ u p g = F j p g) :
    (∀ p, Continuous (fun g => c ⬝ᵥ u p g)) ∧
    ∀ p, ∃ δ : ℝ, 0 < δ ∧ HasUniformSimpleRootBound (r := r + 1) (Metric.ball p δ) (fun q g => c ⬝ᵥ u q g) := by
  have hloc (p : X) : ∃ δ : ℝ, 0 < δ ∧
      (∀ q ∈ Metric.ball p δ, Continuous (fun g => c ⬝ᵥ u q g)) ∧
      HasUniformSimpleRootBound (r := r + 1) (Metric.ball p δ) (fun q g => c ⬝ᵥ u q g) := by
    obtain ⟨b, hb⟩ := hframe p
    let A := rowFrame v b
    let w (q : X) := c ᵥ* (A q)⁻¹
    have hA : Continuous A := continuous_matrix fun i j => hv (b i) j
    have hInv : ContinuousAt (fun q => (A q)⁻¹) p := by
      have hR : ContinuousAt (Ring.inverse : ℂ → ℂ) (A p).det := by
        have H : (Ring.inverse : ℂ → ℂ) = Inv.inv := funext Ring.inverse_eq_inv
        rw [H]
        exact continuousAt_inv₀ hb
      exact (continuousAt_matrix_inv (A p) hR).comp hA.continuousAt
    have hw (i : Fin n) : ContinuousAt (fun q => w q i) p := by
      have hi : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => (c ᵥ* M) i) :=
        (continuous_apply i).comp (continuous_const.matrix_vecMul continuous_id)
      exact hi.continuousAt.comp hInv
    have hdet : ∀ᶠ q in 𝓝 p, (A q).det ≠ 0 :=
      (isOpen_ne_fun hA.matrix_det continuous_const).mem_nhds hb
    choose ε hε using fun i : Fin n => hFb (b i) p
    have hballs : ∀ᶠ q in 𝓝 p, ∀ i : Fin n, q ∈ Metric.ball p (ε i) :=
      eventually_all.mpr fun i => Metric.ball_mem_nhds _ (hε i).1
    have hcoef : ∀ᶠ q in 𝓝 p, ∀ i : Fin n, ‖w q i‖ < ‖w p i‖ + 1 :=
      eventually_all.mpr fun i => (hw i).norm.eventually_lt continuousAt_const (lt_add_one _)
    obtain ⟨δ, hδ, hsub⟩ := Metric.eventually_nhds_iff_ball.mp (hdet.and (hballs.and hcoef))
    have hsum (q : X) (hq : q ∈ Metric.ball p δ) (g : G') :
        c ⬝ᵥ u q g = ∑ i, w q i * F (b i) q g := by
      have hR : A q *ᵥ u q g = fun i => F (b i) q g := funext fun i => he (b i) q g
      have h := congrArg (fun z => (A q)⁻¹ *ᵥ z) hR
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hsub q hq).1),
        Matrix.one_mulVec] at h
      rw [h, Matrix.dotProduct_mulVec]
      rfl
    refine ⟨δ, hδ, fun q hq => ?_, ?_⟩
    · simp_rw [hsum q hq]
      exact continuous_finsetSum _ fun i _ => (hFc (b i) q).const_mul _
    · have ht := uniform_bound_sum (Metric.ball p δ) (fun i => F (b i)) w (fun i => ‖w p i‖ + 1)
        (fun i => by positivity) (fun i q hq => ((hsub q hq).2.2 i).le)
        (fun i => uniform_bound_mono (fun q hq => (hsub q hq).2.1 i) (hε i).2)
      obtain ⟨N, hN⟩ := ht
      refine ⟨N, fun J => ?_⟩
      obtain ⟨C, hC, hb⟩ := hN J
      refine ⟨C, hC, fun q hq g => ?_⟩
      change ‖c ⬝ᵥ u q g‖ ≤ _
      rw [hsum q hq g]
      exact hb q hq g
  refine ⟨fun p => ?_, fun p => ?_⟩
  · obtain ⟨δ, hδ, hc, _⟩ := hloc p
    exact hc p (Metric.mem_ball_self hδ)
  · obtain ⟨δ, hδ, _, hb⟩ := hloc p
    exact ⟨δ, hδ, hb⟩

private theorem det_ne_zero_of_spanning {k : ℕ} {J : Type*} (v : J → Fin k → ℂ)
    (hv : Submodule.span ℂ (range v) = ⊤) :
    ∃ b : Fin k → J, Matrix.det (fun i j => v (b i) j) ≠ 0 := by
  have hdim : Module.finrank ℂ (Submodule.span ℂ (range v)) = k := by
    rw [hv, finrank_top, Module.finrank_fin_fun]
  have h := Submodule.exists_fun_fin_finrank_span_eq ℂ (range v)
  rw [hdim] at h
  obtain ⟨f, hf, _, hfi⟩ := h
  choose b hb using hf
  refine ⟨b, (?_ : IsUnit (Matrix.det (fun i j => v (b i) j))).ne_zero⟩
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.linearIndependent_rows_iff_isUnit.mp
  have he : Matrix.row (fun i j => v (b i) j) = f := funext hb
  rw [he]
  exact hfi

private def chamberEvaluation (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : L') (p : P')
    (hp : p ∈ chamber (r + 1)) (A : Submodule ℂ (U' → ℂ)) (hA : ∀ v : A, IsCompactProfile l v.val)
    (g : G') : A →ₗ[ℂ] ℂ := by
  let lift : A →ₗ[ℂ] (G' → ℂ) := {
    toFun := fun f => standardSection p f.val
    map_add' := fun x y => (extensionLinear _).map_add x.val y.val
    map_smul' := fun c x => (extensionLinear _).map_smul c x.val }
  let D := lift.codRestrict (Automorphic.complexStandardKFinite (r + 1 + 1) (characterList l p))
    (fun v => standardSection_mem (hA v) p)
  exact (LinearMap.proj (R := ℂ) g).comp
    ((ComplexJacquetChamberIntertwiner.chamberIntertwiner μ (characterList l p) a
      (isStrictlyDominant_characterList l hp)).comp D)

private theorem dotProduct_evaluation {Q : Type*} [AddCommGroup Q] [Module ℂ Q] {n : ℕ}
    (b : Module.Basis (Fin n) ℂ Q) (ℓ : Q →ₗ[ℂ] ℂ) (v : Q) :
    b.equivFun v ⬝ᵥ (fun i => ℓ (b i)) = ℓ v := by
  unfold dotProduct
  conv_rhs => rw [← b.sum_repr v]
  simp only [map_sum, map_smul, smul_eq_mul, Module.Basis.equivFun_apply]

variable (r) in
/-- The uniform Jacquet continuation property passes from one rank to the next. -/
def ComplexJacquetUniformContinuationStepStatement : Prop :=
  ∀ (ν : Measure G) [SFinite ν] [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ), HasLocallyUniformJacquetFamily r μ a →
    HasLocallyUniformJacquetFamily (r + 1) μ a

set_option maxHeartbeats 1800000 in
theorem complexJacquetUniformContinuationStep : ComplexJacquetUniformContinuationStepStatement r := by
  intro ν hνf hν hνr μ a hLower l φ hφ
  obtain ⟨A, hAfin, hφA, hA, J, Φ, f, htest, hspan⟩ :=
    ComplexGodement.complexGodementFiniteProfiles ν l φ hφ
  choose lower hLower' using fun j : J => hLower (smallerWeights l) (f j).val (f j).2
  let b := Module.finBasis ℂ A
  let φA : A := ⟨φ, hφA⟩
  let gen (j : J) (p : P') := godementSection ν (addedCharacter l p) (Φ j) (smallerSection p (f j))
  let v (j : J) (p : P') : A := ⟨compactRestriction (gen j p), by
    rw [← hspan p]
    exact Submodule.subset_span ⟨j, rfl⟩⟩
  let u (j : J) (p : P') := b.equivFun (v j p)
  let F (j : J) := generatorFamily ν μ a l (Φ j) (lower j)
  have hF (j : J) := complexGodementGeneratorFamily (r := r) ν μ a l (Φ j)
    (htest j).1 (htest j).2.1 (f j) (lower j) (hLower' j).1 (hLower' j).2.1 (hLower' j).2.2.1 (hLower' j).2.2.2
  let smallLinear : P' →ₗ[ℂ] P := {
    toFun := smallerExponents
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  let smallCLM : P' →L[ℂ] P := smallLinear.toContinuousLinearMap
  have hgen (j : J) (g : G') : Differentiable ℂ (fun p => gen j p g) := by
    have hfc := (continuous_standardSection_family (f j).2.1).comp
      ((smallCLM.continuous.comp continuous_fst).prodMk continuous_snd)
    have hfd (h : G) := (differentiable_standardSection (f j).val h).comp smallCLM.differentiable
    exact ComplexGodement.complexGodementCompactHolomorphic ν (l 0) _
      (ContinuousLinearMap.proj 0 : P' →L[ℂ] ℂ).differentiable (Φ j)
      (Φ j).continuous (htest j).1 (htest j).2.1 (fun p => smallerSection p (f j)) hfc hfd g
  have hu (j : J) (i : Fin (Module.finrank ℂ A)) : Differentiable ℂ (fun p => u j p i) := by
    obtain ⟨k, x, c, hx⟩ := Langlands.Archimedean.InductionStages.exists_eval_sum A (b.coord i)
    have he : (fun p => u j p i) = fun p => ∑ t : Fin k, c t * gen j p (Unitary.toUnits (x t)) := by
      funext p
      exact hx (v j p)
    rw [he]
    exact Differentiable.fun_sum fun t _ => (hgen j (Unitary.toUnits (x t))).const_mul _
  have huSpan (p : P') : Submodule.span ℂ (range fun j => u j p) = ⊤ := by
    let S := Submodule.span ℂ (range fun j => v j p)
    have hmap : S.map A.subtype = A := by
      change (Submodule.span ℂ (range fun j => v j p)).map A.subtype = A
      rw [Submodule.map_span, ← Set.range_comp]
      exact hspan p
    have hS : S = ⊤ := by
      apply Submodule.map_injective_of_injective A.injective_subtype
      rw [hmap, Submodule.map_top, Submodule.range_subtype]
    have h := congrArg (fun T : Submodule ℂ A => T.map b.equivFun.toLinearMap) hS
    change (Submodule.span ℂ (range fun j => v j p)).map b.equivFun.toLinearMap =
      (⊤ : Submodule ℂ A).map b.equivFun.toLinearMap at h
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top,
      LinearMap.range_eq_top.mpr b.equivFun.surjective] at h
    exact h
  have hStd (j : J) (p : P') : gen j p ∈ Automorphic.complexStandardKFinite (r + 1 + 1) (characterList l p) := by
    rw [characterList_cons]
    exact ComplexGodement.complexGodementKFinite (r + 1) ν (addedCharacter l p) (retainedCharacters l p)
      (Φ j) ((Φ j).smooth ⊤) (htest j).1 (htest j).2.1 (htest j).2.2 (smallerSection p (f j))
      (standardSection_mem (f j).2 (smallerExponents p)).1
  choose W hW using fun i : Fin (Module.finrank ℂ A) =>
    complexJacquetContinuationStep ν μ a hLower l (b i).val (hA (b i))
  let w (p : P') (g : G') := fun i => W i p g
  have hseed (p : P') (hp : p ∈ chamber (r + 1)) (g : G') :
      w p g = fun i => chamberEvaluation μ a l p hp A hA g (b i) :=
    funext fun i => (hW i).2 p hp g
  have hcompare (j : J) (p : P') (g : G') : u j p ⬝ᵥ w p g = F j p g := by
    have hdiff : Differentiable ℂ (fun q => u j q ⬝ᵥ w q g) :=
      Differentiable.fun_sum fun i _ => (hu j i).mul ((hW i).1 g)
    apply congrFun (eq_of_differentiable_eqOn_chamber hdiff ((hF j).1 g) ?_) p
    intro q hq
    change b.equivFun (v j q) ⬝ᵥ w q g = F j q g
    rw [hseed q hq g, dotProduct_evaluation]
    change openCellIntegral a (entryHaar μ (r + 1 + 1))
      (standardSection q (compactRestriction (gen j q))) g = F j q g
    rw [standardSection_compactRestriction (hStd j q)]
    exact ((hF j).2.2.2.2 q hq g).symm
  have hloc := finite_frame_continuation (r := r) u F w (b.equivFun φA)
    (fun j i => (hu j i).continuous) (fun p => det_ne_zero_of_spanning _ (huSpan p))
    (fun j => (hF j).2.1) (fun j => (hF j).2.2.2.1) hcompare
  refine ⟨fun p g => b.equivFun φA ⬝ᵥ w p g, hloc.1,
    fun g => Differentiable.fun_sum (fun i _ => ((hW i).1 g).const_mul _), hloc.2, ?_⟩
  intro p hp g
  change b.equivFun φA ⬝ᵥ w p g = _
  rw [hseed p hp g]
  exact dotProduct_evaluation b (chamberEvaluation μ a l p hp A hA g) φA

/-- In every positive complex rank the fixed-profile Jacquet family continues to all radial
parameters, with continuous group slices and locally uniform logarithmic simple-root estimates. -/
def ComplexJacquetUniformContinuationStatement : Prop :=
  ∀ (r : ℕ) (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ), HasLocallyUniformJacquetFamily r μ a

theorem complexJacquetUniformContinuation : ComplexJacquetUniformContinuationStatement := by
  intro r μ a
  induction r with
  | zero => exact complexJacquetRankOne μ a
  | succ r ih =>
    exact complexJacquetUniformContinuationStep (complexGeneralLinearHaar (r + 1)) μ a ih

end Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation
