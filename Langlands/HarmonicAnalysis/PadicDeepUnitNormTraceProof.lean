import Langlands.HarmonicAnalysis.PadicDeepUnitNormTraceStatement
import Langlands.ClassFieldTheory.Local.QuadraticNormTraceProof

/-! The integral quadratic norm error is killed by the actual conductor. -/

noncomputable section

namespace Langlands.HarmonicAnalysis

universe u v

private theorem trace_mem_integers {p : ℕ} [Fact p.Prime]
    {F : PadicField.{u} p} {E : PadicField.{v} p}
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier]
    (T : F.TopologicalData) (S : E.TopologicalData) (y : S.Integers) :
    Algebra.trace F.Carrier E.Carrier (y : E.Carrier) ∈ T.Integers := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := S.topology
  let := S.valuativeRel
  let := S.localField
  let := T.relativeIntegerAlgebra S
  let := T.relativeIntegerFieldAlgebra (E := E)
  let := T.relativeIntegerFieldTower (E := E)
  let := T.relativeIntegerTower S
  obtain ⟨hclosure, hfinite⟩ := LocalClassField.NYLL.relativeIntegerStructure p F E T S
  let := hclosure
  let := hfinite
  let : Module.IsTorsionFree T.Integers S.Integers :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (by
      intro a b h
      apply Subtype.ext
      apply (algebraMap F.Carrier E.Carrier).injective
      exact congrArg Subtype.val h)
  let : Module.Free T.Integers S.Integers := inferInstance
  let := IsIntegralClosure.isLocalization T.Integers F.Carrier E.Carrier S.Integers
  have ht := Algebra.trace_localization (Rₘ := F.Carrier) (Sₘ := E.Carrier)
    T.Integers (nonZeroDivisors T.Integers) y
  change Algebra.trace F.Carrier E.Carrier (y : E.Carrier) =
    (Algebra.trace T.Integers S.Integers y : F.Carrier) at ht
  rw [ht]
  exact (Algebra.trace T.Integers S.Integers y).property

/-- The actual norm pullback has the prescribed trace character on these deep units. -/
theorem padicDeepUnitNormTrace : PadicDeepUnitNormTraceStatement.{u,v} := by
  intro p hp F E hFE hbase hfinite T S
  let := T.topology
  intro ψ c n χ hχ a ha hlevel hquad y
  obtain ⟨r, hr⟩ := LocalClassField.quadraticNormTrace p F E T S a y
  have hat : T.discreteValuation (a : F.Carrier) ≤ 1 := ha.le
  have htr : T.discreteValuation (Algebra.trace F.Carrier E.Carrier (y : E.Carrier)) ≤ 1 :=
    (T.mem_integers_iff_discreteValuation_le_one _).mp (trace_mem_integers T S y)
  have hrv : T.discreteValuation (r : F.Carrier) ≤ 1 :=
    (T.mem_integers_iff_discreteValuation_le_one _).mp r.property
  let w : F.Carrier := (a : F.Carrier) * Algebra.trace F.Carrier E.Carrier (y : E.Carrier) +
    (a : F.Carrier) ^ 2 * (r : F.Carrier)
  have hw : T.discreteValuation w ≤ T.discreteValuation (a : F.Carrier) := by
    apply T.discreteValuation.map_add_le
    · simpa only [map_mul, mul_one] using mul_le_mul' le_rfl htr
    · rw [map_mul, map_pow, pow_two]
      calc
        T.discreteValuation (a : F.Carrier) * T.discreteValuation (a : F.Carrier) *
            T.discreteValuation (r : F.Carrier) ≤
          T.discreteValuation (a : F.Carrier) * 1 * 1 :=
            mul_le_mul' (mul_le_mul' le_rfl hat) hrv
        _ = _ := by simp
  let q : E.Carrier := 1 + algebraMap F.Carrier E.Carrier (a : F.Carrier) * (y : E.Carrier)
  have hn : Algebra.norm F.Carrier q = 1 + w := by
    simpa only [q, w, add_assoc] using hr
  have hnv : T.discreteValuation (Algebra.norm F.Carrier q) = 1 := by
    rw [hn]
    exact (T.discreteValuation.map_add_eq_of_lt_left (x := 1) (y := w)
      (by simpa using hw.trans_lt ha)).trans (map_one _)
  have hn0 : Algebra.norm F.Carrier q ≠ 0 := by
    intro h
    rw [h, map_zero] at hnv
    exact zero_ne_one hnv
  let z : E.Carrierˣ := Units.mk0 q (Algebra.norm_ne_zero_iff.mp hn0)
  have hzmem : Units.map (Algebra.norm F.Carrier) z ∈ T.principalUnits n := by
    constructor
    · exact hnv
    · change T.discreteValuation (Algebra.norm F.Carrier q - 1) ≤ _
      rw [hn, add_sub_cancel_left]
      exact hw.trans hlevel
  refine ⟨z, rfl, hzmem, ?_⟩
  rw [hχ ⟨_, hzmem⟩]
  apply congrArg Circle.toUnits
  have herror : ψ (c * (a : F.Carrier) ^ 2 * (r : F.Carrier)) = 1 := by
    apply (T.additiveConductor_spec ψ).1
    change T.discreteValuation _ ≤ _
    rw [map_mul, map_mul, map_pow]
    exact (mul_le_mul' le_rfl hrv).trans (by simpa using hquad)
  change ψ (c * (Algebra.norm F.Carrier q - 1)) = _
  rw [hn, add_sub_cancel_left]
  change ψ (c * ((a : F.Carrier) * Algebra.trace F.Carrier E.Carrier (y : E.Carrier) +
    (a : F.Carrier) ^ 2 * (r : F.Carrier))) = _
  rw [mul_add, AddChar.map_add_eq_mul]
  simpa only [mul_assoc, herror, mul_one] using
    congrArg (fun t => ψ (c * ((a : F.Carrier) *
      Algebra.trace F.Carrier E.Carrier (y : E.Carrier))) * t) herror

end Langlands.HarmonicAnalysis
