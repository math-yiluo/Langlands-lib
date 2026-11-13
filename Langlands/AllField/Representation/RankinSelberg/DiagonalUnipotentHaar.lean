import Langlands.Representation.RankinSelberg.DiagonalUnipotentHaar
import Langlands.AllField.Group.GL.BlockModulusHaarProof
import Langlands.AllField.Group.GL.SingletonBlocks
/-! # Diagonal conjugation and upper-unipotent Haar measure

Shared helpers extracted without changing their definitions or proofs from
`QuotientIwasawaIntegrationProof` (Worker 113).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators NNReal ENNReal

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding diagonalConj_map singleton_modulus_real
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear
open Langlands.GeneralLinear.BlockShape

universe uF

theorem diagonalConj_map 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ)
    (a : Fin (n + 1) → Fˣ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (upperUnipotent (n + 1) F)
    letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
    (unipotentHaar F n).map (diagonalConj a) =
      ((T.leviModulus (singletons (n + 1)) (singletonLevi F a) : ℝ≥0)⁻¹) •
        unipotentHaar F n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let B := singletons (n + 1)
  let := borel (B.unipotentRadical F)
  let : BorelSpace (B.unipotentRadical F) := ⟨rfl⟩
  let := T.unipotentRadicalTopologicalGroup B
  let e := upperUnipotentContinuousEquivRadical (n := n + 1) F
  let μ := unipotentHaar F n
  have he : Measurable e := e.continuous.measurable
  have hC := (continuous_diagonalConj a).measurable
  have hL : Measurable (B.leviAction F (singletonLevi F a)) :=
    ((B.continuous_leviAction F).comp
      (continuous_const.prodMk continuous_id)).measurable
  have hintertwine : e ∘ diagonalConj a =
      B.leviAction F (singletonLevi F a) ∘ e := by
    funext u
    rfl
  have hblock := glBlockModulusHaar F T (n + 1) B (μ.map e)
    (singletonLevi F a)
  apply (show MeasurableEmbedding e from e.toHomeomorph.measurableEmbedding).map_injective
  rw [Measure.map_map he hC, hintertwine, ← Measure.map_map hL he,
    Measure.map_smul _ he.aemeasurable, hblock]

theorem singleton_modulus_real 
    (F : Type uF) [Field F] (T : LocalFieldData F) {m : ℕ}
    (a : Fin m → Fˣ) :
    ((T.leviModulus (singletons m) (singletonLevi F a) : ℝ≥0) : ℝ) =
      ∏ i : Fin m, ∏ j ∈ Finset.univ.filter (fun j : Fin m => i < j),
        T.normalizedAbs ((a i / a j : Fˣ) : F) := by
  rw [T.leviModulus_singletonLevi]
  simp only [Units.coe_prod, NNReal.coe_prod]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  rw [← map_div, T.normalizedAbsUnits_coe]

end Langlands.AllField.RankinSelberg
