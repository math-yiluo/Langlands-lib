import Langlands.Representation.RankinSelberg.RootFiniteFunctionStatement
import Langlands.Representation.RankinSelberg.RootCoordinateProof
import Langlands.Representation.RankinSelberg.FiniteFunctionClosureProof
import Langlands.LocalField.Normalization.Proof

noncomputable section

namespace Langlands.RankinSelberg

open scoped BigOperators

universe uF

private theorem continuous_normalizedAbs {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) :
    letI := T.topology
    Continuous T.normalizedAbs := by
  rw [T.topology_eq_canonicalNormTopology]
  let := F.canonicalNormedField
  have habs (x : F.Carrier) :
      T.normalizedAbs x = ‖x‖ ^ Module.finrank (Padic p) F.Carrier :=
    T.normalizedAbs_eq_canonicalNorm_pow_degree x
  simp_rw [show T.normalizedAbs = fun x =>
    ‖x‖ ^ Module.finrank (Padic p) F.Carrier from funext habs]
  exact continuous_norm.pow _

/-- The actual inverse modulus in root coordinates preserves the continuous
translation-finite functions used in the torus Mellin reduction. -/
theorem rootCoordinateFiniteFunction {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) :
    RootCoordinateFiniteFunctionStatement F T n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let A := Fin (n + 1) → F.Carrierˣ
  let d : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
  let w : A → ℂ := fun a =>
    (∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^
      ((i.val + 1) * (n - i.val)))⁻¹
  have hc : Continuous (fun a : A =>
      ∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^
        ((i.val + 1) * (n - i.val))) := by
    apply continuous_finsetProd
    intro i _
    exact (Complex.continuous_ofReal.comp
      ((continuous_normalizedAbs F T).comp
        (Units.continuous_val.comp (continuous_apply i)))).pow _
  have hn (a : A) : (∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^
      ((i.val + 1) * (n - i.val))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr
      (T.normalizedAbs_pos (Units.ne_zero (a i))).ne')
  have hwc : Continuous w := hc.inv₀ hn
  have hw1 : w 1 = 1 := by
    change (∏ i : Fin (n + 1), (T.normalizedAbs (1 : F.Carrier) : ℂ) ^
      ((i.val + 1) * (n - i.val)))⁻¹ = 1
    simp [T.normalizedAbs_one]
  have hwm (a b : A) : w (a * b) = w a * w b := by
    change (∏ i, (T.normalizedAbs ((a i : F.Carrier) * (b i : F.Carrier)) : ℂ) ^
      ((i.val + 1) * (n - i.val)))⁻¹ = w a * w b
    simp only [w, T.normalizedAbs_mul,
      Complex.ofReal_mul, mul_pow, Finset.prod_mul_distrib, mul_inv]
  have hdc : Continuous d := (rootCoordinateChange F T n).1
  have hdm (a b : A) : d (a * b) = d a * d b :=
    (rootCoordinateChange F T n).2.2.2.2.1 a b
  let dh : A →* A :=
    { toFun := d
      map_one' := by
        apply funext
        intro i
        change (∏ j ∈ Finset.univ.filter (i ≤ ·), (1 : F.Carrierˣ)) = 1
        simp
      map_mul' := hdm }
  let wh : A →* ℂ := { toFun := w, map_one' := hw1, map_mul' := hwm }
  change Continuous w ∧ w 1 = 1 ∧
    (∀ a b : A, w (a * b) = w a * w b) ∧ _
  refine ⟨hwc, hw1, hwm, ?_⟩
  intro f g hf hg
  obtain ⟨hmul, hpull, hchar⟩ := finiteFunctionClosure A A
  exact hmul _ _ (hmul _ _ (hpull dh hdc f hf) (hpull dh hdc g hg))
    (hchar wh hwc)

end Langlands.RankinSelberg
