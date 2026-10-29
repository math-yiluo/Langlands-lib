import Langlands.Representation.RankinSelberg.QuotientIwasawaIntegrationStatement
import Langlands.Representation.RankinSelberg.DiagonalUnipotentHaar
import Langlands.Group.GL.SingletonBlocks
import Langlands.Group.GL.BlockModulusHaarProof
import Langlands.Analysis.Local.QuotientCompactOpenOrbitProof
import Langlands.Representation.RankinSelberg.IwasawaTorusSumProof

/-!
# Normalized quotient Iwasawa integration

The compact-open orbit formula and diagonal conjugation compute the restriction
of any compatible quotient measure to each uniformizer orbit. The published
torus-sum identity identifies the sum of these restrictions with the normalized
inverse-modulus-weighted torus/compact pushforward.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators NNReal ENNReal

namespace Langlands.RankinSelberg

open GeneralLinear GeneralLinear.BlockShape QuotientIntegration

universe uF

private theorem singleton_modulus_inverse {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) {m : ℕ}
    (a : Fin m → F.Carrierˣ) :
    (((T.leviModulus (singletons m) (singletonLevi F.Carrier a) : ℝ≥0) : ℝ≥0∞))⁻¹ =
      ENNReal.ofReal ((∏ i : Fin m, ∏ j ∈ Finset.univ.filter (fun j : Fin m => i < j),
        T.normalizedAbs ((a i / a j : F.Carrierˣ) : F.Carrier))⁻¹) := by
  rw [← singleton_modulus_real F T a, ← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal,
    ENNReal.coe_inv (Units.ne_zero _)]

private theorem diagonal_stabilizer_mass {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ)
    (a : Fin (n + 1) → F.Carrierˣ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    unipotentHaar F.Carrier n
      {u : upperUnipotent (n + 1) F.Carrier |
        (Iwasawa.diagonalUnits a)⁻¹ * u * Iwasawa.diagonalUnits a ∈
          Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n} =
      ((T.leviModulus (singletons (n + 1)) (singletonLevi F.Carrier a) : ℝ≥0) : ℝ≥0∞) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  have h := congrArg (fun ν : Measure (upperUnipotent (n + 1) F.Carrier) =>
    ν (unipotentIntegralOpen F.Carrier n : Set _)) (diagonalConj_map F T n a⁻¹)
  rw [Measure.map_apply (continuous_diagonalConj a⁻¹).measurable
      (unipotentIntegralOpen F.Carrier n).isOpen.measurableSet,
    Measure.smul_apply, unipotentHaar_integral] at h
  have hset : (diagonalConj a⁻¹) ⁻¹' (unipotentIntegralOpen F.Carrier n : Set _) =
      {u : upperUnipotent (n + 1) F.Carrier |
        (Iwasawa.diagonalUnits a)⁻¹ * u * Iwasawa.diagonalUnits a ∈
          Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n} := by
    ext u
    change (diagonalConj a⁻¹ u : Langlands.GeneralLinear (n + 1) F.Carrier) ∈
      Conductor.levelSubgroup F.Carrier n 0 ↔ _
    rw [diagonalConj_val, map_inv, inv_inv, Conductor.levelSubgroup_zero]
    rfl
  rw [hset] at h
  change _ = (↑((T.leviModulus (singletons (n + 1))
    (singletonLevi F.Carrier a⁻¹) : ℝ≥0)⁻¹) : ℝ≥0∞) * 1 at h
  simpa only [map_inv, Units.val_inv_eq_inv_val, inv_inv, mul_one] using h

private def integralOrbit {E : Type*} [Field E] [ValuativeRel E] {n : ℕ}
    (ϖ : Eˣ) (lam : Fin (n + 1) → ℤ) : Set (LeftUnipotentQuotient n E) :=
  (fun k => leftQuotientMap (upperUnipotent (n + 1) E) (Iwasawa.torus ϖ lam * k)) ''
    (Conductor.integralSubgroup (ValuativeRel.valuation E).integer n : Set _)

private theorem integralOrbit_disjoint {E : Type*} [Field E] [ValuativeRel E] {n : ℕ}
    {ϖ : Eˣ} (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation E) ϖ) :
    Pairwise (fun lam lam' => Disjoint
      (integralOrbit (n := n) ϖ lam) (integralOrbit (n := n) ϖ lam')) := by
  intro lam lam' hne
  apply Set.disjoint_left.mpr
  rintro x ⟨k, hk, hx⟩ ⟨k', hk', hx'⟩
  have hq := hx.trans hx'.symm
  have hu : Iwasawa.torus ϖ lam' * k' * (Iwasawa.torus ϖ lam * k)⁻¹ ∈
      upperUnipotent (n + 1) E := QuotientGroup.rightRel_apply.mp (Quotient.exact hq)
  apply hne
  exact Iwasawa.iwasawa_exponent_unique hϖ hu (one_mem _) hk hk' (by group)

private theorem integralOrbit_cover {E : Type*} [Field E] [ValuativeRel E] {n : ℕ}
    {ϖ : Eˣ} (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation E) ϖ) :
    (⋃ lam, integralOrbit (n := n) ϖ lam) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  induction x using Quotient.inductionOn with
  | h g =>
    obtain ⟨u, hu, lam, k, hk, rfl⟩ := Iwasawa.exists_iwasawa hϖ g
    apply Set.mem_iUnion.mpr
    refine ⟨lam, k, hk, ?_⟩
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    convert hu using 1
    group

private theorem integralOrbit_isOpen {E : Type*} [Field E] [ValuativeRel E]
    [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}
    (ϖ : Eˣ) (lam : Fin (n + 1) → ℤ) : IsOpen (integralOrbit ϖ lam) := by
  have hK := (Conductor.levelOpenSubgroup E n 0).isOpen
  change IsOpen (Conductor.levelSubgroup E n 0 : Set (Langlands.GeneralLinear (n + 1) E)) at hK
  rw [Conductor.levelSubgroup_zero] at hK
  have h := (leftQuotient_isOpenQuotientMap (upperUnipotent (n + 1) E)).isOpenMap _
    ((Homeomorph.mulLeft (Iwasawa.torus ϖ lam)).isOpenMap _ hK)
  simpa only [Set.image_image, Function.comp_def, Homeomorph.coe_mulLeft, integralOrbit] using h

private theorem integralOrbit_isCompact {E : Type*} [Field E] [ValuativeRel E]
    [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}
    (ϖ : Eˣ) (lam : Fin (n + 1) → ℤ) : IsCompact (integralOrbit ϖ lam) := by
  have hK := Conductor.isCompact_levelOpenSubgroup E n 0
  change IsCompact (Conductor.levelSubgroup E n 0 : Set (Langlands.GeneralLinear (n + 1) E)) at hK
  rw [Conductor.levelSubgroup_zero] at hK
  exact hK.image ((leftQuotient_isOpenQuotientMap (upperUnipotent (n + 1) E)).continuous.comp
    (continuous_const.mul continuous_id))

private theorem measure_eq_sum_integralOrbit {E : Type*} [Field E] [ValuativeRel E]
    [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}
    [MeasurableSpace (LeftUnipotentQuotient n E)] [BorelSpace (LeftUnipotentQuotient n E)]
    {ϖ : Eˣ} (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation E) ϖ)
    (μ : Measure (LeftUnipotentQuotient n E)) :
    μ = Measure.sum (fun lam => μ.restrict (integralOrbit ϖ lam)) := by
  calc
    μ = μ.restrict (⋃ lam, integralOrbit ϖ lam) := by
      rw [integralOrbit_cover hϖ, Measure.restrict_univ]
    _ = _ := Measure.restrict_iUnion (integralOrbit_disjoint hϖ)
      (fun lam => (integralOrbit_isOpen ϖ lam).measurableSet)

private theorem measure_restrict_diagonal_orbit {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)]
      (μ : Measure (LeftUnipotentQuotient n F.Carrier)),
    IsCompatible (upperUnipotent (n + 1) F.Carrier)
      (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ →
    ∀ a : Fin (n + 1) → F.Carrierˣ,
      let K := Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n
      let q := fun k => leftQuotientMap (upperUnipotent (n + 1) F.Carrier)
        (Iwasawa.diagonalUnits a * k)
      μ.restrict (q '' (K : Set _)) =
        ENNReal.ofReal ((∏ i : Fin (n + 1),
          ∏ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => i < j),
            T.normalizedAbs ((a i / a j : F.Carrierˣ) : F.Carrier))⁻¹) •
          Measure.map q ((generalLinearHaar F.Carrier n).restrict (K : Set _)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let : LocallyCompactSpace (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) :=
    inferInstanceAs (LocallyCompactSpace (Fin (n + 1) → Fin (n + 1) → F.Carrier))
  let : SecondCountableTopology (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) :=
    inferInstanceAs (SecondCountableTopology (Fin (n + 1) → Fin (n + 1) → F.Carrier))
  let : SecondCountableTopology
      (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  let : SecondCountableTopology (Langlands.GeneralLinear (n + 1) F.Carrier) :=
    Units.isInducing_embedProduct.secondCountableTopology
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro _ μ hμ a
  have h := (compactOpenOrbitMeasure
    (upperUnipotent (n + 1) F.Carrier) (UpperUnipotent.isClosed (R := F.Carrier))
    (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n)
    (Conductor.levelOpenSubgroup F.Carrier n 0)
    (Conductor.isCompact_levelOpenSubgroup F.Carrier n 0) μ hμ
    (Iwasawa.diagonalUnits a)).2.2
  change μ.restrict
    ((fun k => leftQuotientMap (upperUnipotent (n + 1) F.Carrier)
      (Iwasawa.diagonalUnits a * k)) ''
        (Conductor.levelSubgroup F.Carrier n 0 : Set _)) =
      (unipotentHaar F.Carrier n
        {u : upperUnipotent (n + 1) F.Carrier |
          (Iwasawa.diagonalUnits a)⁻¹ * u * Iwasawa.diagonalUnits a ∈
            Conductor.levelSubgroup F.Carrier n 0})⁻¹ •
        Measure.map
          (fun k => leftQuotientMap (upperUnipotent (n + 1) F.Carrier)
            (Iwasawa.diagonalUnits a * k))
          ((generalLinearHaar F.Carrier n).restrict
            (Conductor.levelSubgroup F.Carrier n 0 : Set _)) at h
  rw [Conductor.levelSubgroup_zero, diagonal_stabilizer_mass F T n a,
    singleton_modulus_inverse F T a] at h
  exact h

private theorem quotientIwasawaIntegration_of_torus_sum
    (hsum : IwasawaTorusSumStatement.{uF}) {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) :
    QuotientIwasawaIntegrationStatement F T n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrierˣ
  let : BorelSpace F.Carrierˣ := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro _ μ hμ
  obtain ⟨ϖ, hϖ⟩ := Iwasawa.exists_isUniformizingElement F.Carrier
  rw [measure_eq_sum_integralOrbit hϖ μ, hsum p F T n ϖ hϖ]
  congr 1
  funext lam
  exact measure_restrict_diagonal_orbit F T n μ hμ (fun i => ϖ ^ lam i)

/-- Every compatible left-unipotent quotient measure is the normalized
inverse-modulus-weighted pushforward of diagonal Haar and restricted compact Haar. -/
theorem quotientIwasawaIntegration {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) :
    QuotientIwasawaIntegrationStatement F T n :=
  quotientIwasawaIntegration_of_torus_sum iwasawaTorusSum F T n

end Langlands.RankinSelberg
