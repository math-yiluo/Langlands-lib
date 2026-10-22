import Langlands.Geometry.Analytic.TateUniversal.Statement
import Langlands.Geometry.Analytic.TateEvaluation
import Langlands.Geometry.Analytic.TateSeries

/-! # The bounded universal property of the strict Tate algebra -/

noncomputable section

universe u v w

namespace Langlands.Analytic

namespace StrictTateAlgebra

variable (σ : Type u) (K : Type v) [NormedField K] [IsUltrametricDist K]

/-- Every monomial is its scalar coefficient times the finite coordinate product. -/
theorem monomial_eq (d : σ →₀ ℕ) (a : K) :
    monomial σ K d a =
      algebraMap K (StrictTateAlgebra σ K) a *
        monomialValue σ (StrictTateAlgebra σ K) (X σ K) d := by
  apply Subtype.ext
  change MvPowerSeries.monomial d a =
    MvPowerSeries.C a * (restrictedSubalgebra σ K).val
      (d.prod fun i n =>
        (⟨(X σ K i).val, (X σ K i).property⟩ : restrictedSubalgebra σ K) ^ n)
  rw [map_finsuppProd]
  simp only [map_pow]
  exact MvPowerSeries.monomial_eq' d a

variable (B : Type w) [NormedCommRing B] [NormedAlgebra K B]

theorem map_monomial (φ : BoundedAlgHom K (StrictTateAlgebra σ K) B)
    (d : σ →₀ ℕ) (a : K) :
    φ (monomial σ K d a) =
      algebraMap K B a * monomialValue σ B (fun i => φ (X σ K i)) d := by
  rw [monomial_eq]
  change φ.toAlgHom (_ * _) = _
  rw [map_mul, AlgHom.commutes]
  congr 1
  unfold monomialValue
  rw [map_finsuppProd]
  simp only [map_pow]

/-- The coordinate images of every bounded algebra map have uniformly bounded
monomials. The bound is inherited from the map, not imposed as an extra premise. -/
theorem hasBoundedMonomials_map_X (φ : BoundedAlgHom K (StrictTateAlgebra σ K) B) :
    HasBoundedMonomials σ B (fun i => φ (X σ K i)) := by
  obtain ⟨C, hCpos, hC⟩ := φ.bounded
  refine ⟨C, hCpos, fun d => ?_⟩
  have heq : monomialValue σ B (fun i => φ (X σ K i)) d =
      φ (monomial σ K d 1) := by
    rw [map_monomial, map_one, one_mul]
  rw [heq]
  have h := hC (monomial σ K d 1)
  change ‖φ (monomial σ K d 1)‖ ≤ C * ‖monomial σ K d 1‖ at h
  simpa only [norm_monomial, norm_one, mul_one] using h

theorem evaluate_X (b : σ → B) (i : σ) :
    evaluate σ K B b (X σ K i) = b i := by
  classical
  rw [X, evaluate_monomial, map_one, one_mul]
  simp [monomialValue, Finsupp.prod_single_index]

variable [CompleteSpace K]

/-- A bounded algebra map evaluates every series by its convergent monomial
expansion and is therefore determined by its coordinate images. -/
theorem map_eq_evaluate (φ : BoundedAlgHom K (StrictTateAlgebra σ K) B)
    (f : StrictTateAlgebra σ K) :
    φ f = evaluate σ K B (fun i => φ (X σ K i)) f := by
  calc
    φ f = φ (∑' d, monomial σ K d (MvPowerSeries.coeff d (series σ K f))) :=
      congrArg φ (tsum_monomials σ K f).symm
    _ = ∑' d, φ (monomial σ K d (MvPowerSeries.coeff d (series σ K f))) :=
      φ.toContinuousLinearMap.map_tsum (summable_monomials σ K f)
    _ = _ := by
      apply tsum_congr
      intro d
      exact map_monomial σ K B φ d _

theorem hom_ext (φ ψ : BoundedAlgHom K (StrictTateAlgebra σ K) B)
    (h : ∀ i, φ (X σ K i) = ψ (X σ K i)) : φ = ψ := by
  apply BoundedAlgHom.ext
  intro f
  rw [map_eq_evaluate, map_eq_evaluate]
  congr 1
  exact funext h

variable [IsUltrametricDist B] [CompleteSpace B]

/-- The bounded universal property: bounded algebra maps from the genuine Tate
algebra correspond exactly to tuples with uniformly bounded monomials. -/
def boundedHomEquiv :
    BoundedAlgHom K (StrictTateAlgebra σ K) B ≃
      {b : σ → B // HasBoundedMonomials σ B b} where
  toFun φ := ⟨fun i => φ (X σ K i), hasBoundedMonomials_map_X σ K B φ⟩
  invFun b := evaluateHom σ K B b.val b.property
  left_inv φ := by
    apply BoundedAlgHom.ext
    intro f
    exact (map_eq_evaluate σ K B φ f).symm
  right_inv b := by
    apply Subtype.ext
    funext i
    exact evaluate_X σ K B b.val i

/-- The exact evaluation, bounded-monomial and uniqueness target. -/
theorem boundedUniversalProperty : BoundedUniversalPropertyStatement.{u, v, w} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro σ B _ _ b
    exact hasBoundedMonomials_iff_pow_bound σ B b
  · intro σ K _ _ B _ _ _ _ b hb
    refine ⟨?_, evaluateHom σ K B b hb, ?_, ?_⟩
    · intro f
      exact (summable_evaluationTerms σ K B b hb f).hasSum
    · intro f
      rfl
    · intro i
      exact evaluate_X σ K B b i
  · intro σ K _ _ _ B _ _
    exact ⟨hasBoundedMonomials_map_X σ K B, hom_ext σ K B⟩
  · intro σ K _ _ _ B _ _ _ _ b hb
    refine ⟨evaluateHom σ K B b hb, ?_, ?_⟩
    · intro i
      exact evaluate_X σ K B b i
    · intro φ hφ
      apply hom_ext σ K B φ (evaluateHom σ K B b hb)
      intro i
      exact (hφ i).trans (evaluate_X σ K B b i).symm

end StrictTateAlgebra

end Langlands.Analytic
