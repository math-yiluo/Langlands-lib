import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.EffectiveData
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeSeriesMap
import Langlands.Geometry.Analytic.GeneralizedAffinoid.ClosedQuotient
import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.RelativeEvaluation

/-! # Finite Banach algebras have actual weighted affinoid presentations -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open GeneralizedTateAlgebra

namespace FiniteBanachPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}
  {B : Type v} [NormedCommRing B] [NormedAlgebra K B]
  [IsUltrametricDist B] [CompleteSpace B]
  (f : BoundedAlgHom K A B) (h1 : ‖(1 : B)‖ ≤ 1)
  {n : ℕ} (b : Fin n → B)

/-- Choose a positive radius strictly larger than each finite generator norm. -/
def radii : PositivePolyradius (Fin n) :=
  ⟨fun i => ‖b i‖ + 1, fun i => by positivity⟩

/-- The actual unconstrained weighted variable adjunction over the supplied
presentation of the coefficient algebra. -/
abbrev freeAlgebra := Adjoin.algebra K A (radii b) ∅

/-- Evaluation first maps the coefficients by their original bounded map,
then evaluates over the target coefficient algebra. Only the second step
uses a contractive coefficient map, namely the identity. -/
def evaluation : BoundedAlgHom K (freeAlgebra (A := A) b) B :=
  (evaluateCoefficientsHom (radii b) (BoundedAlgHom.id K B) b (fun _ => le_rfl)
    (monomialValue_norm_le_weight (radii b) B h1 b
      (fun i => by change ‖b i‖ ≤ ‖b i‖ + 1; linarith))).comp
    ((mapCoefficientsAlgHom (radii b) f).comp (Adjoin.relativeSeriesMap K A (radii b)))

@[simp] theorem evaluation_baseMap (a : A) :
    evaluation f h1 b (Adjoin.baseMap K A (radii b) ∅ a) = f a := by
  change evaluateCoefficients (radii b) (BoundedAlgHom.id K B) b
    (mapCoefficients (radii b) f.toBoundedRingHom
      (Adjoin.relativeSeriesMap K A (radii b) (Adjoin.baseMap K A (radii b) ∅ a))) = _
  rw [Adjoin.relativeSeriesMap_baseMap, constantAlgHom_apply, mapCoefficients_algebraMap]
  exact evaluateCoefficients_constant (radii b) (BoundedAlgHom.id K B) b (f a)

@[simp] theorem evaluation_newCoordinate (i : Fin n) :
    evaluation f h1 b (Adjoin.newCoordinate K A (radii b) ∅ i) = b i := by
  change evaluateCoefficients (radii b) (BoundedAlgHom.id K B) b
    (mapCoefficients (radii b) f.toBoundedRingHom
      (Adjoin.relativeSeriesMap K A (radii b) (Adjoin.newCoordinate K A (radii b) ∅ i))) = _
  rw [Adjoin.relativeSeriesMap_newCoordinate, mapCoefficients_X]
  exact evaluateCoefficients_X (radii b) (BoundedAlgHom.id K B) b i

/-- Linear polynomials in the finite generator coordinates retain the
original coefficient tuple. -/
def linearPolynomial (c : Fin n → A) : freeAlgebra (A := A) b :=
  ∑ i, Adjoin.baseMap K A (radii b) ∅ (c i) * Adjoin.newCoordinate K A (radii b) ∅ i

@[simp] theorem evaluation_linearPolynomial (c : Fin n → A) :
    evaluation f h1 b (linearPolynomial b c) = f.coefficientMap b c := by
  change (evaluation f h1 b).toAlgHom (∑ i, _) = _
  rw [map_sum]
  simp only [map_mul, evaluation_baseMap, evaluation_newCoordinate,
    BoundedAlgHom.coefficientMap_apply]

/-- A positive uniform bound, also when the finite tuple is empty. -/
def polynomialBound : ℝ := (∑ i, radii b i) + 1

omit [IsUltrametricDist B] [CompleteSpace B] in
theorem polynomialBound_pos : 0 < polynomialBound b := by
  have : 0 ≤ ∑ i, radii b i := Finset.sum_nonneg fun i _ => (radii b).positive i |>.le
  dsimp [polynomialBound]
  linarith

omit [CompleteSpace K] [NormedAlgebra K B] [IsUltrametricDist B] [CompleteSpace B] in
theorem norm_linearPolynomial_le (c : Fin n → A) :
    ‖linearPolynomial b c‖ ≤ polynomialBound b * ‖c‖ := by
  calc
    ‖linearPolynomial b c‖ ≤
        ∑ i, ‖Adjoin.baseMap K A (radii b) ∅ (c i) *
          Adjoin.newCoordinate K A (radii b) ∅ i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖c‖ * radii b i := by
      apply Finset.sum_le_sum
      intro i _
      exact (norm_mul_le _ _).trans
        (mul_le_mul ((Adjoin.norm_baseMap_le K A (radii b) ∅ (c i)).trans
          (norm_le_pi_norm c i)) (Adjoin.norm_newCoordinate_le K A (radii b) ∅ i)
            (norm_nonneg _) (norm_nonneg c))
    _ = (∑ i, radii b i) * ‖c‖ := by rw [← Finset.mul_sum, mul_comm]
    _ ≤ polynomialBound b * ‖c‖ :=
      mul_le_mul_of_nonneg_right (by dsimp [polynomialBound]; linarith) (norm_nonneg c)

/-- The supplied norm-controlled finite coefficient lifts give controlled
preimages under the actual weighted evaluation map. -/
theorem evaluation_isAdmissibleEpi {M : ℝ} (hM : 0 < M)
    (hb : ∀ y : B, ∃ c : Fin n → A,
      f.coefficientMap b c = y ∧ ‖c‖ ≤ M * ‖y‖) :
    (evaluation f h1 b).IsAdmissibleEpi := by
  apply (evaluation f h1 b).isAdmissibleEpi_iff_normControlledLifts.mpr
  refine ⟨polynomialBound b * M, mul_pos (polynomialBound_pos b) hM, fun y => ?_⟩
  obtain ⟨c, hc, hcn⟩ := hb y
  refine ⟨linearPolynomial b c, (evaluation_linearPolynomial f h1 b c).trans hc, ?_⟩
  calc
    ‖linearPolynomial b c‖ ≤ polynomialBound b * ‖c‖ := norm_linearPolynomial_le b c
    _ ≤ polynomialBound b * (M * ‖y‖) :=
      mul_le_mul_of_nonneg_left hcn (polynomialBound_pos b).le
    _ = (polynomialBound b * M) * ‖y‖ := (mul_assoc _ _ _).symm

include h1 in
/-- A finite Banach algebra with unit norm at most one has an actual
positive-polyradius presentation boundedly equivalent to its supplied norm. -/
theorem exists_presentation (hf : f.IsFiniteBanach) :
    ∃ P : PresentedAffinoidAlgebra K, Nonempty (BoundedAlgEquiv K P B) := by
  obtain ⟨n, b, M, hM, hb⟩ := hf
  let S := freeAlgebra (A := A) b
  let φ := evaluation f h1 b
  let J := RingHom.ker φ.toAlgHom.toRingHom
  let : IsClosed (J : Set S) := isClosed_eq φ.continuous continuous_const
  exact ⟨ClosedQuotient.algebra S J,
    ⟨ClosedQuotient.equivOfAdmissibleEpi S J φ rfl
      (evaluation_isAdmissibleEpi f h1 b hM hb)⟩⟩

end FiniteBanachPresentation

namespace FiniteAffinoidAlgebraDescent.PairTransitions

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {R : PresentedAffinoidAlgebra K}
  {c : Domain.FiniteCover (Domain.whole K R)} {F : LocalAlgebras c}
  (t : PairTransitions F)

/-- The actual finite-product matching norm has unit norm at most one,
including empty products and zero quotient factors. -/
theorem norm_one_matching_le : ‖(1 : t.MatchingAlgebra)‖ ≤ 1 := by
  change ‖(1 : ∀ i : Fin c.size, F.algebra i)‖ ≤ 1
  exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => norm_one_le K (F.algebra i)

/-- A norm-controlled finite matching structural map already supplies its
actual affinoid matching presentation. -/
def matchingPresentationOfFinite (hf : t.structuralMap.IsFiniteBanach) :
    MatchingPresentation t :=
  let h := FiniteBanachPresentation.exists_presentation t.structuralMap
    t.norm_one_matching_le hf
  ⟨h.choose, Classical.choice h.choose_spec⟩

end FiniteAffinoidAlgebraDescent.PairTransitions
end Langlands.Analytic.PresentedAffinoidAlgebra
