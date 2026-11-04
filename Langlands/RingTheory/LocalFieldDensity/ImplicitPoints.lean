import Langlands.AlgebraicGeometry.PointManifold.PolynomialCalculus
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.RingTheory.Extension.Presentation.Submersive

/-! # Points of submersive presentations over complete nontrivially normed fields

Let `K` be a complete nontrivially normed field and let `P` be a submersive presentation of a
`K`-algebra `S`. Near the coordinates of any `K`-point of `S`, every value of the variables outside
the image of `P.map` (the free variables) is attained by some `K`-point of `S`. The proof applies
the inverse function theorem to the polynomial map which records the relations together with the
free variables; its derivative is invertible because the Jacobian of `P` is a unit.
-/

noncomputable section

open MvPolynomial Filter Topology

namespace Langlands.RingTheory.LocalFieldDensity

open Langlands.AlgebraicGeometry.PointManifold

variable {K : Type*} [NontriviallyNormedField K]

/-- Polynomial evaluation has the formal derivative as strict derivative, over every nontrivially
normed field. -/
theorem hasStrictFDerivAt_polynomial_eval {ι : Type*} [Fintype ι] (p : MvPolynomial ι K)
    (x : ι → K) :
    HasStrictFDerivAt (fun y : ι → K => eval y p) (polynomialDerivative p x) x := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using (hasStrictFDerivAt_const c x)
  | add p q hp hq => simpa using! hp.add hq
  | mul_X p i hp =>
    simpa [polynomialDerivative_mul] using! hp.mul (hasStrictFDerivAt_apply i x)

/-- A polynomial vanishing on a neighbourhood of a point of `K^τ` is zero. -/
theorem eq_zero_of_eventually_eval_eq_zero {τ : Type*} [Finite τ] {t₀ : τ → K}
    {c : MvPolynomial τ K} (h : ∀ᶠ t in 𝓝 t₀, eval t c = 0) : c = 0 := by
  have := Fintype.ofFinite τ
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp h
  refine MvPolynomial.funext_set (fun i => Metric.ball (t₀ i) ε)
    (fun i => infinite_of_mem_nhds (t₀ i) (Metric.ball_mem_nhds _ hε)) fun t ht => ?_
  rw [map_zero]
  exact hball t (by rwa [ball_pi _ hε])

variable {S : Type*} [CommRing S] [Algebra K S] {ι σ : Type*}

/-- A solution of the relations of a presentation is a `K`-point of the presented algebra. -/
def pointOfSolution (P : Algebra.Presentation K S ι σ) (v : ι → K)
    (hv : ∀ j, eval v (P.relation j) = 0) : S →ₐ[K] K :=
  AlgHom.liftOfSurjective (aeval (R := K) P.val) P.aeval_val_surjective (aeval v) (by
    change RingHom.ker (aeval (R := K) P.val) ≤ RingHom.ker (aeval (R := K) v)
    rw [← P.ker_eq_ker_aeval_val, ← P.span_range_relation_eq_ker, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact hv j)

theorem pointOfSolution_val (P : Algebra.Presentation K S ι σ) (v : ι → K)
    (hv : ∀ j, eval v (P.relation j) = 0) (i : ι) :
    pointOfSolution P v hv (P.val i) = v i := by
  have h : P.val i = aeval (R := K) P.val (X i) := (aeval_X _ _).symm
  rw [pointOfSolution, h, AlgHom.liftOfSurjective_apply, aeval_X]

/-- The free variables of a pre-submersive presentation: those outside the image of `map`. -/
abbrev FreeVar {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]
    (P : Algebra.PreSubmersivePresentation R T ι σ) : Type _ :=
  {i : ι // i ∉ Set.range P.map}

/-- The `K`-points of the presented algebra realize every value of the free variables near the
free coordinates of a given `K`-point. -/
theorem eventually_exists_algHom [CompleteSpace K] [Finite ι] [Finite σ]
    (P : Algebra.SubmersivePresentation K S ι σ) (x : S →ₐ[K] K) :
    ∀ᶠ t in 𝓝 (fun i : FreeVar P.toPreSubmersivePresentation => x (P.val i)),
      ∃ y : S →ₐ[K] K, ∀ i : FreeVar P.toPreSubmersivePresentation, y (P.val i) = t i := by
  classical
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite σ
  set τ := FreeVar P.toPreSubmersivePresentation
  set v₀ : ι → K := fun i => x (P.val i)
  have hrel₀ : ∀ j, eval v₀ (P.relation j) = 0 := fun j => by
    have h := congrArg x (P.aeval_val_relation j)
    rwa [MvPolynomial.comp_aeval_apply, map_zero] at h
  -- the relations together with the free variables
  let Φ : (ι → K) → (σ ⊕ τ → K) :=
    fun v => Sum.elim (fun j => eval v (P.relation j)) (fun i => v i)
  let D : (ι → K) →L[K] (σ ⊕ τ → K) :=
    ContinuousLinearMap.pi
      (Sum.elim (fun j => polynomialDerivative (P.relation j) v₀)
        (fun i => ContinuousLinearMap.proj (i : ι)))
  have hD : HasStrictFDerivAt Φ D v₀ := by
    rw [hasStrictFDerivAt_pi']
    rintro (j | i)
    · simpa [Φ, D] using hasStrictFDerivAt_polynomial_eval (P.relation j) v₀
    · simpa [Φ, D] using hasStrictFDerivAt_apply (𝕜 := K) (i : ι) v₀
  -- the derivative is injective since the Jacobian is a unit
  have hdet : (Matrix.of fun j k : σ =>
      eval v₀ (pderiv (P.map k) (P.relation j))).det ≠ 0 := by
    have h : (Matrix.of fun j k : σ => eval v₀ (pderiv (P.map k) (P.relation j))) =
        ((eval v₀).mapMatrix P.jacobiMatrix).transpose := by
      ext j k
      simp [P.jacobiMatrix_apply]
    rw [h, Matrix.det_transpose, ← RingHom.map_det]
    have hx : eval v₀ P.jacobiMatrix.det = x P.jacobian := by
      rw [P.jacobian_eq_jacobiMatrix_det, P.algebraMap_eq, AlgHom.coe_toRingHom,
        MvPolynomial.comp_aeval_apply]
      rfl
    rw [hx]
    exact (P.jacobian_isUnit.map x).ne_zero
  have hinj : Function.Injective D := by
    rw [injective_iff_map_eq_zero]
    intro h hh
    have hfree : ∀ i : τ, h i = 0 := fun i => by
      simpa [D] using congrFun hh (Sum.inr i)
    have hmap : (fun k => h (P.map k)) = 0 := by
      apply Matrix.eq_zero_of_mulVec_eq_zero hdet
      ext j
      have hj := congrFun hh (Sum.inl j)
      simp only [D, ContinuousLinearMap.pi_apply, Sum.elim_inl, polynomialDerivative_apply,
        Pi.zero_apply] at hj
      rw [Pi.zero_apply, ← hj, Matrix.mulVec, dotProduct]
      refine Fintype.sum_of_injective P.map P.map_inj _ _ (fun i hi => ?_) (fun k => by simp)
      rw [hfree ⟨i, hi⟩, mul_zero]
    funext i
    by_cases hi : i ∈ Set.range P.map
    · obtain ⟨k, rfl⟩ := hi
      exact congrFun hmap k
    · exact hfree ⟨i, hi⟩
  have hcard : Fintype.card (σ ⊕ τ) = Fintype.card ι :=
    Fintype.card_congr ((Equiv.sumCongr (Equiv.ofInjective P.map P.map_inj) (Equiv.refl τ)).trans
      (Equiv.sumCompl (fun i => i ∈ Set.range P.map)))
  have hdim : Module.finrank K (ι → K) = Module.finrank K (σ ⊕ τ → K) := by
    simp only [Module.finrank_fintype_fun_eq_card, hcard]
  let f' : (ι → K) ≃L[K] (σ ⊕ τ → K) :=
    (LinearMap.linearEquivOfInjective D.toLinearMap hinj hdim).toContinuousLinearEquiv
  have hD' : HasStrictFDerivAt Φ (f' : (ι → K) →L[K] (σ ⊕ τ → K)) v₀ := by
    have : (f' : (ι → K) →L[K] (σ ⊕ τ → K)) = D := by
      ext h : 1
      rfl
    rw [this]
    exact hD
  have hmapnhds := hD'.map_nhds_eq_of_equiv
  -- points with prescribed free coordinates
  let g : (τ → K) → (σ ⊕ τ → K) := fun t => Sum.elim (fun _ => 0) t
  have hg : Continuous g := continuous_pi fun k => by
    rcases k with j | i
    · exact continuous_const
    · exact continuous_apply i
  have hg₀ : g (fun i => v₀ i) = Φ v₀ := by
    funext k
    rcases k with j | i
    · exact (hrel₀ j).symm
    · rfl
  have hrange : Set.range Φ ∈ 𝓝 (g (fun i => v₀ i)) := by
    rw [hg₀, ← hmapnhds]
    exact Filter.range_mem_map
  filter_upwards [hg.continuousAt.preimage_mem_nhds hrange] with t ht
  obtain ⟨v, hv⟩ := ht
  have hvrel : ∀ j, eval v (P.relation j) = 0 := fun j => congrFun hv (Sum.inl j)
  refine ⟨pointOfSolution P.toPresentation v hvrel, fun i => ?_⟩
  rw [pointOfSolution_val]
  exact congrFun hv (Sum.inr i)

end Langlands.RingTheory.LocalFieldDensity
