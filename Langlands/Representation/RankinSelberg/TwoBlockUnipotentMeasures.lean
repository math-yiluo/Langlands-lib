import Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientData
import Langlands.Representation.RankinSelberg.Measures
import Langlands.Representation.RankinSelberg.UnipotentUnimodularity
import Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity
import Langlands.Analysis.Local.QuotientMeasureExistence
import Langlands.Group.GL.CountabilityProof

/-!
# Fixed measures for the two-block unipotent quotient

The subgroup measure is exactly the transport of the two normalized block
unipotent Haar measures. Its invariance and regularity give compatible quotient
existence. The integral rectangular cube has positive finite mass for every
supplied additive Haar measure.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockUnipotentQuotient

open MeasureTheory GeneralLinear QuotientIntegration TopologicalSpace
open scoped ENNReal

universe uF

section BlockMeasure

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [T2Space F]
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  [∀ i : Fin 2, MeasurableSpace (upperUnipotent (m i + 1) F)]
  [∀ i : Fin 2, BorelSpace (upperUnipotent (m i + 1) F)]
  [MeasurableSpace (blockUnipotent h F)] [BorelSpace (blockUnipotent h F)]

/-- The fixed block subgroup measure, retaining the published product and embedding. -/
def blockHaar : Measure (blockUnipotent h F) :=
  Measure.map (blockUnipotentEquiv h F)
    (Measure.pi (fun i : Fin 2 => unipotentHaar F (m i)))

variable [∀ i : Fin 2, SecondCountableTopology (upperUnipotent (m i + 1) F)]

private instance blockFactor_locallyCompact (i : Fin 2) :
    LocallyCompactSpace (upperUnipotent (m i + 1) F) := by
  have : LocallyCompactSpace (Matrix (Fin (m i + 1)) (Fin (m i + 1)) F) :=
    inferInstanceAs (LocallyCompactSpace (Fin (m i + 1) → Fin (m i + 1) → F))
  exact UpperUnipotent.locallyCompactSpace

instance blockHaar_isHaar : (blockHaar F h).IsHaarMeasure := by
  exact (blockUnipotentHomeomorph h F).isHaarMeasure_map
    (Measure.pi (fun i : Fin 2 => unipotentHaar F (m i)))

instance blockHaar_regular : (blockHaar F h).Regular := by
  let K : PositiveCompacts (BlockUnipotents m F) := Classical.arbitrary _
  have : (Measure.pi (fun i : Fin 2 => unipotentHaar F (m i))).Regular :=
    Measure.regular_of_isMulLeftInvariant K.isCompact K.interior_nonempty
      K.isCompact.measure_ne_top
  exact Measure.Regular.map (blockUnipotentHomeomorph h F).toHomeomorph

instance blockHaar_isMulRightInvariant : (blockHaar F h).IsMulRightInvariant := by
  let e := blockUnipotentHomeomorph h F
  let μ := Measure.pi (fun i : Fin 2 => unipotentHaar F (m i))
  have hemeas : Measurable (e : BlockUnipotents m F → blockUnipotent h F) :=
    e.continuous.measurable
  change (Measure.map e μ).IsMulRightInvariant
  refine ⟨fun g => ?_⟩
  rw [Measure.map_map (f := (e : BlockUnipotents m F → blockUnipotent h F))
    (measurable_mul_const g) hemeas]
  change Measure.map (fun x => e x * g) μ = Measure.map e μ
  have he : (fun x => e x * g) = e ∘ (fun x => x * e.symm g) := by
    funext x
    simp
  rw [he, ← Measure.map_map hemeas (measurable_mul_const _),
    map_mul_right_eq_self]

/-- The fixed ambient and block subgroup measures admit a compatible measure
on the actual left quotient. -/
theorem block_compatibleMeasureExists
    [MeasurableSpace (GeneralLinear (t + 1) F)]
    [BorelSpace (GeneralLinear (t + 1) F)]
    [MeasurableSpace (BlockQuotient h F)] [BorelSpace (BlockQuotient h F)] :
    CompatibleMeasureExists (blockUnipotent h F) (generalLinearHaar F t) (blockHaar F h) := by
  have : LocallyCompactSpace (Matrix (Fin (t + 1)) (Fin (t + 1)) F) :=
    inferInstanceAs (LocallyCompactSpace (Fin (t + 1) → Fin (t + 1) → F))
  exact Langlands.QuotientIntegration.compatibleMeasureExists (blockUnipotent h F)
    (isClosed_blockUnipotent h F) (generalLinearHaar F t) (blockHaar F h)

end BlockMeasure

section FullUnipotentMeasure

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [T2Space F] (t : ℕ)
  [MeasurableSpace (GeneralLinear (t + 1) F)]
  [BorelSpace (GeneralLinear (t + 1) F)]
  [MeasurableSpace (upperUnipotent (t + 1) F)]
  [BorelSpace (upperUnipotent (t + 1) F)]
  [MeasurableSpace (LeftUnipotentQuotient t F)]
  [BorelSpace (LeftUnipotentQuotient t F)]

/-- Compatible quotient existence for the fixed full-unipotent Haar measure. -/
theorem fullUnipotent_compatibleMeasureExists :
    CompatibleMeasureExists (upperUnipotent (t + 1) F)
      (generalLinearHaar F t) (unipotentHaar F t) := by
  have : LocallyCompactSpace (Matrix (Fin (t + 1)) (Fin (t + 1)) F) :=
    inferInstanceAs (LocallyCompactSpace (Fin (t + 1) → Fin (t + 1) → F))
  exact Langlands.QuotientIntegration.compatibleMeasureExists (upperUnipotent (t + 1) F)
    (UpperUnipotent.isClosed (R := F)) (generalLinearHaar F t) (unipotentHaar F t)

end FullUnipotentMeasure

section Canonical

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- Every supplied rectangular additive Haar gives the integral cube positive finite mass. -/
theorem integerCube_mass_pos_lt_top (a b : ℕ) :
    let T := F.canonicalTopologicalData
    letI := T.topology
    letI := T.valuativeRel
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    ∀ (μ : Measure (Matrix (Fin a) (Fin b) F.Carrier)) [μ.IsAddHaarMeasure],
      0 < μ {x | ∀ i j, x i j ∈ (ValuativeRel.valuation F.Carrier).integer} ∧
        μ {x | ∀ i j, x i j ∈ (ValuativeRel.valuation F.Carrier).integer} < ⊤ := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  dsimp only
  intro μ _
  let O := (ValuativeRel.valuation F.Carrier).integer
  have he : {x : Matrix (Fin a) (Fin b) F.Carrier | ∀ i j, x i j ∈ O} =
      Set.univ.pi (fun _ : Fin a => Set.univ.pi (fun _ : Fin b => (O : Set F.Carrier))) := by
    ext x
    change (∀ i j, x i j ∈ O) ↔
      (∀ i ∈ Set.univ, ∀ j ∈ Set.univ, x i j ∈ O)
    simp
  have hc : IsCompact {x : Matrix (Fin a) (Fin b) F.Carrier | ∀ i j, x i j ∈ O} := by
    rw [he]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => T.isCompact_integers
  have ho : IsOpen {x : Matrix (Fin a) (Fin b) F.Carrier | ∀ i j, x i j ∈ O} := by
    rw [he]
    exact isOpen_set_pi Set.finite_univ fun _ _ =>
      isOpen_set_pi Set.finite_univ fun _ _ => T.isOpen_integers
  change 0 < μ {x | ∀ i j, x i j ∈ O} ∧ μ {x | ∀ i j, x i j ∈ O} < ⊤
  exact ⟨ho.measure_pos μ ⟨0, fun _ _ => O.zero_mem⟩, hc.measure_lt_top⟩

end Canonical

end Langlands.RankinSelberg.TwoBlockUnipotentQuotient
