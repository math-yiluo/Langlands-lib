import Langlands.FieldTheory.ClosureTransport
import Langlands.CommutativeAlgebra.ArithmeticRegularLocalApproximationStatement
import Langlands.CommutativeAlgebra.ArithmeticRegularLocalApproximation.Mixed
import Langlands.CommutativeAlgebra.DvrCompletion

/-! # Arithmetic regular local approximation of a strictly Henselian trait -/

universe u v w

open IsLocalRing Polynomial

namespace Langlands.CommutativeAlgebra

namespace ArithmeticRegularLocalApproximation

/-- A field extension given by a surjective ring map is purely inseparable. -/
theorem isPurelyInseparable_of_surjective {F E : Type*} [Field F] [Field E] (φ : F →+* E)
    (h : Function.Surjective φ) :
    letI : Algebra F E := φ.toAlgebra
    IsPurelyInseparable F E := by
  let _ : Algebra F E := φ.toAlgebra
  refine ⟨⟨fun x => ?_⟩, fun x _ => h x⟩
  obtain ⟨y, rfl⟩ := h x
  exact isIntegral_algebraMap (x := y)

end ArithmeticRegularLocalApproximation

open ArithmeticRegularLocalApproximation in
/-- **Arithmetic regular local approximation.** For a strictly Henselian discrete valuation ring
`W` with uniformizer `π` and fraction field `L`, every ring map `f : C → L` from a finite type
`ℤ`-algebra induces a map `C → Frac W'` for the completion `W' = Ŵ`. This map factors through
`B[1/t]`, where `B` is a Henselian regular local ring with a local homomorphism `B → W'`
sending the regular parameter `t` to a uniformizer. -/
theorem arithmeticRegularLocalApproximation :
    ArithmeticRegularLocalApproximationStatement.{u, v, w} := by
  intro W _ _ _ _ _ L _ _ _ π C _ _ f hπ
  obtain ⟨_, _⟩ := DvrCompletion.isDomain_and_isDiscreteValuationRing W
  have := DvrCompletion.faithfullyFlat W
  have hϖ : Irreducible (algebraMap W (AdicCompletion (maximalIdeal W) W) π) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
    exact DvrCompletion.maximalIdeal_eq_span W hπ
  have hinj : Function.Injective ((algebraMap (AdicCompletion (maximalIdeal W) W)
      (FractionRing (AdicCompletion (maximalIdeal W) W))).comp
      (algebraMap W (AdicCompletion (maximalIdeal W) W))) :=
    (IsFractionRing.injective (AdicCompletion (maximalIdeal W) W)
      (FractionRing (AdicCompletion (maximalIdeal W) W))).comp
      (FaithfulSMul.algebraMap_injective W (AdicCompletion (maximalIdeal W) W))
  let iFrac : L →+* FractionRing (AdicCompletion (maximalIdeal W) W) := IsFractionRing.lift hinj
  obtain ⟨B, _, _, _, _, t, j, _, ht, ht2, htreg, hjt, hk, jAway, g, hj, hg⟩ :=
    chartConclusion_of_complete hϖ C (iFrac.comp f)
  refine ⟨AdicCompletion (maximalIdeal W) W, inferInstance, inferInstance, inferInstance, ?_, ?_,
    algebraMap W (AdicCompletion (maximalIdeal W) W), inferInstance, hϖ, ?_, ?_⟩
  · exact henselianLocalRing_of_isAdicComplete_maximalIdeal _
  · exact Langlands.FieldTheory.isSepClosed_of_ringEquiv (DvrCompletion.residueEquiv W)
  · exact isPurelyInseparable_of_surjective _ (AdicCompletion.residueField_map_bijective W).2
  · refine ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, t, j, inferInstance,
      ht, ht2, htreg, hjt, hk, iFrac, jAway, g, RingHom.ext fun x => ?_, hj, hg⟩
    rw [RingHom.comp_apply, RingHom.comp_apply]
    exact IsFractionRing.lift_algebraMap hinj x

end Langlands.CommutativeAlgebra
