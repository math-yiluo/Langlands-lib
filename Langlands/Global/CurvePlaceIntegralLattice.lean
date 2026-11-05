import Langlands.Global.CurvePlaceCompletedTensorEquiv

/-! # Actual function-field integral lattices in products of upper completions -/

noncomputable section

universe u

open IsDedekindDomain AlgebraicCurve
open scoped Langlands.Global.CurvePlaceCompletionExtension
  Langlands.Global.CurvePlaceIntegralClosure Langlands.Global.CurvePlaceIntegralPrimes

namespace Langlands.Global.CurvePlaceIntegralLattice

variable {k K L : Type u} [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L]
  [FiniteDimensional K L] [Finite k]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [IsScalarTower k K L]
  (p : Place k K)

/-- The actual integral closure consists exactly of elements integral at every upper place. -/
theorem integral_mem_iff (x : L) :
    x ∈ curvePlaceIntegralClosure L p ↔
      ∀ q : CurvePlacesAbove k L p, x ∈ q.1.toValuationSubring := by
  constructor
  · intro hx q
    exact CurvePlaceIntegralPrimes.integralClosure_le p q hx
  · intro hx
    let S := curvePlaceIntegralClosure L p
    have hlocal : x ∈ (⊥ : Subalgebra S L) := by
      rw [← HeightOneSpectrum.iInf_localization_eq_bot S, Algebra.mem_iInf]
      intro Q
      let : Q.asIdeal.LiesOver p.heightOneSpectrum.asIdeal := by
        constructor
        exact (IsLocalRing.eq_maximalIdeal
          (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := p.toValuationSubring)
            Q.asIdeal)).symm
      let P : p.heightOneSpectrum.asIdeal.primesOver S :=
        Ideal.primesOver.mk _ Q.asIdeal
      have hq := hx (CurvePlaceIntegralPrimes.upperPlace p P)
      change x ∈ (Q.valuation L).valuationSubring at hq
      rw [← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring] at hq
      exact hq
    obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hlocal
    exact ha ▸ a.property

/-- The original integral-closure elements embedded in all actual upper completions. -/
def integralEmbedding :
    curvePlaceIntegralClosure L p →+*
      (∀ q : CurvePlacesAbove k L p, curvePlaceCompletion q.1) where
  toFun a q := algebraMap L (curvePlaceCompletion q.1) a
  map_one' := by ext q; exact map_one _
  map_mul' a b := by ext q; exact map_mul _ _ _
  map_zero' := by ext q; exact map_zero _
  map_add' a b := by ext q; exact map_add _ _ _

omit [FiniteDimensional K L] [Finite k] [Algebra (RatFunc k) K]
  [IsScalarTower k (RatFunc k) K] [FunctionField k K] [IsScalarTower k K L] in
@[simp]
theorem integralEmbedding_apply (a : curvePlaceIntegralClosure L p)
    (q : CurvePlacesAbove k L p) :
    integralEmbedding p a q = algebraMap L (curvePlaceCompletion q.1) (a : L) := rfl

omit [Finite k] [Algebra (RatFunc k) K]
  [IsScalarTower k (RatFunc k) K] [FunctionField k K] [IsScalarTower k K L] in
/-- The product integer lattice is open in the full finite product of original completions. -/
theorem productIntegers_isOpen :
    IsOpen (Set.pi Set.univ (fun q : CurvePlacesAbove k L p =>
      (curvePlaceCompletionIntegers q.1 : Set (curvePlaceCompletion q.1)))) :=
  isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring _

/-- Weak approximation by original field elements restricts to integral-closure approximation. -/
theorem productIntegers_subset_closure :
    Set.pi Set.univ (fun q : CurvePlacesAbove k L p =>
      (curvePlaceCompletionIntegers q.1 : Set (curvePlaceCompletion q.1))) ⊆
        closure (Set.range (integralEmbedding (L := L) p)) := by
  have hd := CurvePlaceCompletedProduct.denseRange_family
    (fun q : CurvePlacesAbove k L p => q.1) Subtype.val_injective
  refine (hd.subset_closure_image_preimage_of_isOpen (productIntegers_isOpen p)).trans
    (closure_mono ?_)
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ curvePlaceIntegralClosure L p := (integral_mem_iff p x).mpr fun q =>
    (curvePlaceCompletion_mem_integers_iff q.1 x).mp (hx q trivial)
  exact ⟨⟨x, hx'⟩, rfl⟩

/-- The original integral closure is dense precisely in the full product integer lattice. -/
theorem closure_integralEmbedding :
    closure (Set.range (integralEmbedding (L := L) p)) =
      Set.pi Set.univ (fun q : CurvePlacesAbove k L p =>
        (curvePlaceCompletionIntegers q.1 : Set (curvePlaceCompletion q.1))) := by
  refine le_antisymm (closure_minimal ?_ ?_) (productIntegers_subset_closure p)
  · rintro _ ⟨a, rfl⟩ q _
    exact (curvePlaceCompletion_mem_integers_iff q.1 (a : L)).mpr
      ((integral_mem_iff p (a : L)).mp a.property q)
  · exact isClosed_set_pi fun q _ => Valued.isClosed_valuationSubring _

end Langlands.Global.CurvePlaceIntegralLattice
