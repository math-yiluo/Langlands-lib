import Langlands.Representation.RankinSelberg.Measures
import Langlands.Representation.Whittaker.Iwasawa
import Langlands.Group.GL.SingletonBlocks
import Langlands.Group.GL.BlockModulusHaarProof

/-! # Diagonal conjugation and upper-unipotent Haar measure

Shared helpers extracted without changing their definitions or proofs from
`QuotientIwasawaIntegrationProof` (Worker 113).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators NNReal ENNReal

namespace Langlands.RankinSelberg

open GeneralLinear GeneralLinear.BlockShape

universe uF

def diagonalConj {E : Type*} [Field E] {m : ℕ} (a : Fin m → Eˣ) :
    upperUnipotent m E ≃* upperUnipotent m E :=
  (upperUnipotentEquivRadical E).trans
    (((singletons m).leviAction E (singletonLevi E a)).trans
      (upperUnipotentEquivRadical E).symm)

theorem diagonalConj_val {E : Type*} [Field E] {m : ℕ}
    (a : Fin m → Eˣ) (u : upperUnipotent m E) :
    (diagonalConj a u : Langlands.GeneralLinear m E) =
      Iwasawa.diagonalUnits a * u * (Iwasawa.diagonalUnits a)⁻¹ := by
  have he : (singletons m).leviEmbedding E (singletonLevi E a) =
      Iwasawa.diagonalUnits a := by
    apply Units.ext
    exact leviEmbedding_singletonLevi_val E a
  change (singletons m).leviEmbedding E (singletonLevi E a) * u *
    ((singletons m).leviEmbedding E (singletonLevi E a))⁻¹ = _
  rw [he]

theorem continuous_diagonalConj {E : Type*} [Field E] [TopologicalSpace E]
    [IsTopologicalRing E] {m : ℕ} (a : Fin m → Eˣ) : Continuous (diagonalConj a) := by
  have h : Continuous (fun u : upperUnipotent m E =>
      (diagonalConj a u : Langlands.GeneralLinear m E)) := by
    simp_rw [diagonalConj_val]
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  exact h.subtype_mk _

theorem diagonalConj_map {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ)
    (a : Fin (n + 1) → F.Carrierˣ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    (unipotentHaar F.Carrier n).map (diagonalConj a) =
      ((T.leviModulus (singletons (n + 1)) (singletonLevi F.Carrier a) : ℝ≥0)⁻¹) •
        unipotentHaar F.Carrier n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let B := singletons (n + 1)
  let := borel (B.unipotentRadical F.Carrier)
  let : BorelSpace (B.unipotentRadical F.Carrier) := ⟨rfl⟩
  let := T.unipotentRadicalTopologicalGroup B
  let e := upperUnipotentContinuousEquivRadical (n := n + 1) F.Carrier
  let μ := unipotentHaar F.Carrier n
  have he : Measurable e := e.continuous.measurable
  have hC := (continuous_diagonalConj a).measurable
  have hL : Measurable (B.leviAction F.Carrier (singletonLevi F.Carrier a)) :=
    ((B.continuous_leviAction F.Carrier).comp
      (continuous_const.prodMk continuous_id)).measurable
  have hintertwine : e ∘ diagonalConj a =
      B.leviAction F.Carrier (singletonLevi F.Carrier a) ∘ e := by
    funext u
    rfl
  have hblock := glBlockModulusHaar p F T (n + 1) B (μ.map e)
    (singletonLevi F.Carrier a)
  apply (show MeasurableEmbedding e from e.toHomeomorph.measurableEmbedding).map_injective
  rw [Measure.map_map he hC, hintertwine, ← Measure.map_map hL he,
    Measure.map_smul _ he.aemeasurable, hblock]

theorem singleton_modulus_real {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) {m : ℕ}
    (a : Fin m → F.Carrierˣ) :
    ((T.leviModulus (singletons m) (singletonLevi F.Carrier a) : ℝ≥0) : ℝ) =
      ∏ i : Fin m, ∏ j ∈ Finset.univ.filter (fun j : Fin m => i < j),
        T.normalizedAbs ((a i / a j : F.Carrierˣ) : F.Carrier) := by
  rw [T.leviModulus_singletonLevi]
  simp only [Units.coe_prod, NNReal.coe_prod]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  rw [← map_div, T.normalizedAbsUnits_coe]

end Langlands.RankinSelberg
