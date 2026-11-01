import Langlands.Global.ArchimedeanCompactIndexAverage
import Langlands.Global.ArchimedeanCovarianceProof
import Langlands.Global.ArchimedeanAdjointCoefficientsProof

/-! # Finite expansions of derivatives of actual compact weighted averages -/

noncomputable section
universe u v
open MeasureTheory
open scoped BigOperators TensorProduct
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL.CompactIndexAverage

variable {K : Type u} [Field K] [NumberField K] {n : ℕ}
variable {J : Type u} [TopologicalSpace J] [T2Space J] [CompactSpace J]
variable (r : C(J, InfiniteAdelicGL K n))
variable [MeasurableSpace (J)]
  [BorelSpace (J)]
variable (ν : Measure (J)) [IsFiniteMeasure ν]

/-- One finite expansion works for both every compact translate and every
continuous weighted average. -/
private def HasDerivativeExpansion (a : EnvelopingAlgebra K n) : Prop :=
  ∃ m : ℕ, ∃ b : Fin m → EnvelopingAlgebra K n,
    ∃ c : Fin m → C(J, ℂ),
      (∀ k : J, ∀ f : SmoothFunctions K n,
        envelopingAction K n a (smoothRightAction K n (r k) f) =
          ∑ i, (c i k) • smoothRightAction K n (r k) (envelopingAction K n (b i) f)) ∧
      (∀ w : C(J, ℂ), ∀ f : SmoothFunctions K n,
        envelopingAction K n a (averageSmoothLM r ν w f) =
          ∑ i, averageSmoothLM r ν (w * c i) (envelopingAction K n (b i) f))

private theorem expansion_of_fintype {ι : Type v} [Fintype ι]
    (a : EnvelopingAlgebra K n) (b : ι → EnvelopingAlgebra K n)
    (c : ι → C(J, ℂ))
    (hp : ∀ k : J, ∀ f : SmoothFunctions K n,
      envelopingAction K n a (smoothRightAction K n (r k) f) =
        ∑ i, (c i k) • smoothRightAction K n (r k) (envelopingAction K n (b i) f))
    (ha : ∀ w : C(J, ℂ), ∀ f : SmoothFunctions K n,
      envelopingAction K n a (averageSmoothLM r ν w f) =
        ∑ i, averageSmoothLM r ν (w * c i) (envelopingAction K n (b i) f)) :
    HasDerivativeExpansion r ν a := by
  classical
  let e := Fintype.equivFin ι
  refine ⟨_, b ∘ e.symm, c ∘ e.symm, ?_, ?_⟩
  · intro k f
    rw [hp k f]
    exact (e.symm.sum_comp _).symm
  · intro w f
    rw [ha w f]
    exact (e.symm.sum_comp _).symm

private theorem expansion_scalar (z : ℂ) :
    HasDerivativeExpansion r ν (algebraMap ℂ (EnvelopingAlgebra K n) z) := by
  refine ⟨1, fun _ => algebraMap ℂ (EnvelopingAlgebra K n) z,
    fun _ => 1, ?_, ?_⟩
  · intro k f
    simp
  · intro w f
    simp [Algebra.algebraMap_eq_smul_one]

private theorem expansion_add (a d : EnvelopingAlgebra K n)
    (ha : HasDerivativeExpansion r ν a) (hd : HasDerivativeExpansion r ν d) :
    HasDerivativeExpansion r ν (a + d) := by
  classical
  obtain ⟨m, b, c, hp, hav⟩ := ha
  obtain ⟨l, e, t, hq, hdv⟩ := hd
  apply expansion_of_fintype r ν (a + d) (Sum.elim b e) (Sum.elim c t)
  · intro k f
    simp only [map_add, LinearMap.add_apply, hp, hq,
      Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  · intro w f
    simp only [map_add, LinearMap.add_apply, hav, hdv,
      Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

private theorem expansion_mul (a d : EnvelopingAlgebra K n)
    (ha : HasDerivativeExpansion r ν a) (hd : HasDerivativeExpansion r ν d) :
    HasDerivativeExpansion r ν (a * d) := by
  classical
  obtain ⟨m, b, c, hp, hav⟩ := ha
  obtain ⟨l, e, t, hq, hdv⟩ := hd
  apply expansion_of_fintype r ν (a * d)
    (fun i : Fin l × Fin m => b i.2 * e i.1)
    (fun i : Fin l × Fin m => t i.1 * c i.2)
  · intro k f
    simp only [envelopingAction_mul, hq, map_sum, map_smul, hp, Finset.smul_sum,
      smul_smul, Fintype.sum_prod_type, ContinuousMap.mul_apply]
  · intro w f
    simp only [envelopingAction_mul, hdv, map_sum, hav, Fintype.sum_prod_type, mul_assoc]

private theorem expansion_smul (z : ℂ) (a : EnvelopingAlgebra K n)
    (ha : HasDerivativeExpansion r ν a) :
    HasDerivativeExpansion r ν (z • a) := by
  rw [Algebra.smul_def]
  exact expansion_mul r ν _ a (expansion_scalar r ν z) ha

private theorem expansion_real_generator (X : RealLieAlgebra K n) :
    HasDerivativeExpansion r ν (envelopingGenerator K n (complexify K n X)) := by
  classical
  let a := envelopingGenerator K n (complexify K n X)
  obtain ⟨m, b, c, hc⟩ := envelopingConjugationCoefficients K n a
  let d : Fin m → C(J, ℂ) := fun i =>
    ⟨fun k => c i (r k)⁻¹,
      (c i).continuous.comp (r.continuous.inv)⟩
  have hp : ∀ k : J, ∀ f : SmoothFunctions K n,
      envelopingAction K n a (smoothRightAction K n (r k) f) =
        ∑ i, (d i k) • smoothRightAction K n (r k) (envelopingAction K n (b i) f) := by
    intro k f
    have h := envelopingRightCovariance K n (r k)
      (envelopingConjugation K n (r k)⁻¹ a) f
    rw [envelopingConjugation_inv, AlgEquiv.apply_symm_apply] at h
    rw [← h, ← envelopingConjugation_inv, hc]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    rfl
  refine ⟨m, b, d, hp, ?_⟩
  intro w f
  apply Subtype.ext
  funext x
  change (envelopingAction K n (envelopingGenerator K n (complexify K n X))
    (averageSmoothLM r ν w f)).val x = _
  rw [envelopingAction_real_generator, smoothDifferential_average]
  have hpx (k : J) :
      (smoothDifferential K n X (smoothRightAction K n (r k) f)).val x =
        ∑ i, d i k * (envelopingAction K n (b i) f).val (x * (r k)) := by
    have h := congrArg (fun h : SmoothFunctions K n => h.val x) (hp k f)
    simpa only [a, envelopingAction_real_generator, Submodule.coe_sum, Finset.sum_apply,
      Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, smoothRightAction_apply] using h
  simp only [hpx, Finset.mul_sum, Submodule.coe_sum, Finset.sum_apply,
    averageSmoothLM_apply, average, ContinuousMap.mul_apply, mul_assoc]
  exact integral_finsetSum _ (fun i _ => by
    simpa only [ContinuousMap.mul_apply, mul_assoc] using
      average_integrable r ν (w * d i) (envelopingAction K n (b i) f) x)

private theorem expansion_complex_generator (X : ComplexLieAlgebra K n) :
    HasDerivativeExpansion r ν (envelopingGenerator K n X) := by
  induction X using TensorProduct.inductionOn with
  | tmul z X =>
    have h : z ⊗ₜ[ℝ] X = z • complexify K n X := by
      simp only [complexify_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h, map_smul]
    exact expansion_smul r ν z _ (expansion_real_generator r ν X)
  | add X Y hX hY =>
    rw [map_add]
    exact expansion_add r ν _ _ hX hY

private theorem expansion_all (a : EnvelopingAlgebra K n) :
    HasDerivativeExpansion r ν a := by
  refine Quotient.inductionOn a ?_
  intro t
  let q := UniversalEnvelopingAlgebra.mkAlgHom ℂ (ComplexLieAlgebra K n)
  change HasDerivativeExpansion r ν (q t)
  induction t using TensorAlgebra.induction with
  | algebraMap z =>
    simpa only [AlgHom.commutes] using expansion_scalar r ν z
  | ι X =>
    exact expansion_complex_generator r ν X
  | mul a b ha hb =>
    rw [map_mul]
    exact expansion_mul r ν _ _ ha hb
  | add a b ha hb =>
    rw [map_add]
    exact expansion_add r ν _ _ ha hb

/-- The same finite family controls every compact translate and every
continuous weighted compact average of a genuine enveloping derivative. -/
theorem derivativeExpansion (a : EnvelopingAlgebra K n) :
    ∃ m : ℕ, ∃ b : Fin m → EnvelopingAlgebra K n,
      ∃ c : Fin m → C(J, ℂ),
        (∀ k : J, ∀ f : SmoothFunctions K n,
          envelopingAction K n a (smoothRightAction K n (r k) f) =
            ∑ i, (c i k) • smoothRightAction K n (r k) (envelopingAction K n (b i) f)) ∧
        (∀ w : C(J, ℂ), ∀ f : SmoothFunctions K n,
          envelopingAction K n a (averageSmoothLM r ν w f) =
            ∑ i, averageSmoothLM r ν (w * c i) (envelopingAction K n (b i) f)) :=
  expansion_all r ν a

/-- Every genuine enveloping derivative passes through the scalar compact
integral, with the derivative taken on each actual right translate. -/
theorem envelopingDerivative_average (a : EnvelopingAlgebra K n)
    (w : C(J, ℂ)) (f : SmoothFunctions K n)
    (x : InfiniteAdelicGL K n) :
    (envelopingAction K n a (averageSmoothLM r ν w f)).val x =
      ∫ k : J,
        w k * (envelopingAction K n a (smoothRightAction K n (r k) f)).val x ∂ν := by
  classical
  obtain ⟨m, b, c, hp, ha⟩ := derivativeExpansion r ν a
  have hpx (k : J) :
      (envelopingAction K n a (smoothRightAction K n (r k) f)).val x =
        ∑ i, c i k * (envelopingAction K n (b i) f).val (x * (r k)) := by
    have h := congrArg (fun h : SmoothFunctions K n => h.val x) (hp k f)
    simpa only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
      Pi.smul_apply, smul_eq_mul, smoothRightAction_apply] using h
  rw [ha]
  simp only [Submodule.coe_sum, Finset.sum_apply, averageSmoothLM_apply,
    average, hpx, Finset.mul_sum, ContinuousMap.mul_apply, mul_assoc]
  exact (integral_finsetSum _ (fun i _ => by
    simpa only [ContinuousMap.mul_apply, mul_assoc] using
      average_integrable r ν (w * c i) (envelopingAction K n (b i) f) x)).symm

end Langlands.Global.ArchimedeanGL.CompactIndexAverage
