/-
The valuation-subring comparison adapts the corresponding proof in
`Langlands.AnthropicFLT.Definitions.Def_JacJ1_ChartAlgebra`, ported from
Anthropic's Lean formalization of Fermat's Last Theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, Copyright 2026 Anthropic, PBC,
under Apache-2.0. See `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and
`ATTRIBUTION.md`. Modified by Worker 208: derive finite normalization over
finite constants without separability, and use it for the original
prime/place correspondence in arbitrary characteristic.
-/
import Langlands.AlgebraicGeometry.NoetherianApproximation.InseparableNormalization
import Langlands.AnthropicFLT.Definitions.Def_JacJ1_ChartAlgebra
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicCurve_RatFuncPlaces

/-! # Finite normalized curve charts over finite constants, including inseparable presentations -/

noncomputable section

universe u

open IntermediateField Polynomial IsDedekindDomain AlgebraicCurve
open scoped AlgebraicCurve.CurveModel IntermediateField.algebraAdjoinAdjoin

namespace Langlands.Global

namespace FiniteConstantCurveChart

variable (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F]
  (s : F) [FiniteDimensional k⟮s⟯ F]

/-- The actual normalized affine chart is finite over the original parameter algebra. -/
theorem moduleFinite :
    Module.Finite (Algebra.adjoin k ({s} : Set F)) (CurveModel.chartRing k ({s} : Set F)) := by
  let A := Algebra.adjoin k ({s} : Set F)
  let C := CurveModel.chartRing k ({s} : Set F)
  let : Module.Finite ℤ k := inferInstance
  let : Algebra.FiniteType ℤ k := inferInstance
  let : Algebra.FiniteType ℤ A :=
    (inferInstance : Algebra.FiniteType ℤ k).trans
      (Algebra.FiniteType.adjoin_of_finite (R := k) (Set.finite_singleton s))
  let : Module.Finite A (integralClosure A F) :=
    Langlands.AlgebraicGeometry.NoetherianApproximation.finite_integralClosure_of_normal_integer_finiteType
      A k⟮s⟯ F
  let e := IsIntegralClosure.equiv A (integralClosure A F) F C
  exact Module.Finite.equiv e.toLinearEquiv

/-- The existing normalized chart has the original field as its fraction field. -/
scoped instance fractionRing : IsFractionRing (CurveModel.chartRing k ({s} : Set F)) F :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    (Algebra.adjoin k ({s} : Set F)) k⟮s⟯ F _

/-- The actual normalized chart is Dedekind without a separability premise. -/
scoped instance dedekind : IsDedekindDomain (CurveModel.chartRing k ({s} : Set F)) := by
  let A := Algebra.adjoin k ({s} : Set F)
  let C := CurveModel.chartRing k ({s} : Set F)
  let : Module.Finite A C := moduleFinite k F s
  let : IsNoetherianRing C := isNoetherianRing_iff.mpr
    (isNoetherian_of_tower A (inferInstance : IsNoetherian A C))
  let : Algebra.IsIntegral A C := IsIntegralClosure.isIntegral_algebra A F
  refine (isDedekindDomain_iff C F).mpr ⟨inferInstance, inferInstance,
    Ring.DimensionLEOne.of_isIntegral A C, ?_⟩
  intro x hx
  exact ⟨IsIntegralClosure.mk' C x (isIntegral_trans (R := A) _ hx),
    IsIntegralClosure.algebraMap_mk' _ _ _⟩

/-- Finite type over the original finite constant field is derived from actual module finiteness. -/
scoped instance finiteType : Algebra.FiniteType k (CurveModel.chartRing k ({s} : Set F)) := by
  let : Module.Finite (Algebra.adjoin k ({s} : Set F))
      (CurveModel.chartRing k ({s} : Set F)) := moduleFinite k F s
  exact (Algebra.FiniteType.adjoin_of_finite (R := k) (Set.finite_singleton s)).trans
    (inferInstance : Algebra.FiniteType (Algebra.adjoin k ({s} : Set F))
      (CurveModel.chartRing k ({s} : Set F)))

private theorem valuationSubringAtPrime_le (O : ValuationSubring F)
    (hK : ∀ a : k, algebraMap k F a ∈ O) (hs : s ∈ O) (hO : O ≠ ⊤) :
    HeightOneSpectrum.valuationSubringAtPrime F
      (CurveModel.primeOfValuationSubring k s O hK hs hO) ≤ O := by
  intro x hx
  have hx' : ∃ (a b : CurveModel.chartRing k ({s} : Set F))
      (_ : b ∈ (CurveModel.centre k s O hK hs).primeCompl),
      x = algebraMap _ F a * (algebraMap _ F b)⁻¹ := hx
  obtain ⟨a, b, hb, rfl⟩ := hx'
  apply O.mem_of_valuation_le_one
  rw [map_mul, map_inv₀, show O.valuation (algebraMap _ F b) = 1 from
    CurveModel.valuation_eq_one_of_not_mem_centre k s O hK hs hb, inv_one, mul_one]
  exact CurveModel.valuation_coe_le_one k s O hK hs a

/-- The actual center prime recovers the original valuation subring. -/
theorem valuationSubringAtPrime_eq (O : ValuationSubring F)
    (hK : ∀ a : k, algebraMap k F a ∈ O) (hs : s ∈ O) (hO : O ≠ ⊤) :
    HeightOneSpectrum.valuationSubringAtPrime F
      (CurveModel.primeOfValuationSubring k s O hK hs hO) = O :=
  ValuationSubring.eq_of_le_of_ne_top _
    (valuationSubringAtPrime_le k F s O hK hs hO) hO

/-- An actual curve place integral on this chart is the place of its actual center prime. -/
theorem ofHeightOneSpectrum_center (p : AlgebraicCurve.Place k F)
    (hs : s ∈ p.toValuationSubring) :
    Place.ofHeightOneSpectrum (K := k)
        (CurveModel.primeOfValuationSubring k s p.toValuationSubring
          p.algebraMap_mem' hs p.ne_top') = p := by
  apply Place.ext
  rw [Place.ofHeightOneSpectrum_toValuationSubring,
    ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  exact valuationSubringAtPrime_eq k F s _ _ hs _

/-- Actual nonzero chart primes correspond to all original curve places integral on the chart. -/
def primeEquivChartPlaces :
    HeightOneSpectrum (CurveModel.chartRing k ({s} : Set F)) ≃
      {p : AlgebraicCurve.Place k F // s ∈ p.toValuationSubring} :=
  Equiv.ofBijective
    (fun P => ⟨Place.ofHeightOneSpectrum (K := k) P, by
      rw [Place.ofHeightOneSpectrum_toValuationSubring, Valuation.mem_valuationSubring_iff]
      exact P.valuation_le_one (⟨s, CurveModel.subset_chartRing k _ (Set.mem_singleton s)⟩ :
        CurveModel.chartRing k ({s} : Set F))⟩)
    ⟨fun _ _ h => Place.ofHeightOneSpectrum_injective (congrArg Subtype.val h),
      fun p => ⟨CurveModel.primeOfValuationSubring k s p.1.toValuationSubring
        p.1.algebraMap_mem' p.2 p.1.ne_top',
        Subtype.ext (ofHeightOneSpectrum_center k F s p.1 p.2)⟩⟩

@[simp]
theorem primeEquivChartPlaces_apply
    (P : HeightOneSpectrum (CurveModel.chartRing k ({s} : Set F))) :
    (primeEquivChartPlaces k F s P).val = Place.ofHeightOneSpectrum (K := k) P := rfl

omit [Finite k] [FiniteDimensional k⟮s⟯ F] in
/-- The reciprocal parameter generates the same original rational subfield. -/
theorem adjoin_inverse_eq : k⟮s⁻¹⟯ = k⟮s⟯ :=
  le_antisymm
    (adjoin_simple_le_iff.mpr (inv_mem (mem_adjoin_simple_self k s)))
    (adjoin_simple_le_iff.mpr (by
      simpa using inv_mem (mem_adjoin_simple_self k s⁻¹)))

/-- Every actual curve place occurs on one of the two actual normalized parameter charts. -/
theorem twoChartsCover (p : AlgebraicCurve.Place k F) :
    (∃ P : HeightOneSpectrum (CurveModel.chartRing k ({s} : Set F)),
      Place.ofHeightOneSpectrum (K := k) P = p) ∨
    (letI : FiniteDimensional k⟮s⁻¹⟯ F := by rw [adjoin_inverse_eq k F s]; infer_instance
     ∃ P : HeightOneSpectrum (CurveModel.chartRing k ({s⁻¹} : Set F)),
      Place.ofHeightOneSpectrum (K := k) P = p) := by
  let : FiniteDimensional k⟮s⁻¹⟯ F := by rw [adjoin_inverse_eq k F s]; infer_instance
  rcases p.toValuationSubring.mem_or_inv_mem s with hs | hs
  · exact Or.inl ⟨CurveModel.primeOfValuationSubring k s p.toValuationSubring
      p.algebraMap_mem' hs p.ne_top', ofHeightOneSpectrum_center k F s p hs⟩
  · exact Or.inr ⟨CurveModel.primeOfValuationSubring k s⁻¹ p.toValuationSubring
      p.algebraMap_mem' hs p.ne_top', ofHeightOneSpectrum_center k F s⁻¹ p hs⟩

end FiniteConstantCurveChart

end Langlands.Global
