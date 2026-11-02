import Langlands.Global.Arithmetic.CharacterPrescriptionStatement
import Langlands.Global.Arithmetic.IntegralUnitCharacterExtensionProof
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-! # Finite-order characters detecting actual principal units -/

noncomputable section

universe u

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Filter Topology
open scoped WithZero

namespace Langlands.Global

namespace LocalRamifiedCharacters

private theorem compact_character_separates
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (a : G) (ha : a ≠ 1) :
    ∃ χ : G →ₜ* ℂˣ, χ a ≠ 1 := by
  have hnhds : ({a}ᶜ : Set G) ∈ 𝓝 (1 : G) :=
    isClosed_singleton.isOpen_compl.mem_nhds (by simpa using ha.symm)
  obtain ⟨H, _, hH⟩ :=
    ((Langlands.Topology.LocallyProfiniteProof.vanDantzig G).mp
      Langlands.Topology.isLocallyProfinite_of_mathlib).2 _ hnhds
  let Q := G ⧸ H.toSubgroup
  let : Finite Q := Subgroup.quotient_finite_of_isOpen H.toSubgroup H.isOpen
  let : DiscreteTopology Q := QuotientGroup.discreteTopology H.isOpen
  let q : G →ₜ* Q :=
    { QuotientGroup.mk' H.toSubgroup with
      continuous_toFun := QuotientGroup.continuous_mk }
  have hqa : q a ≠ 1 := by
    intro h
    have hm : a ∈ H := (QuotientGroup.eq_one_iff a).mp h
    simpa using hH hm
  obtain ⟨ψ, hψ⟩ := AddChar.exists_apply_ne_zero.mpr
    (show Additive.ofMul (q a) ≠ (0 : Additive Q) from hqa)
  let φ : Q →* ℂ :=
    { toFun := fun b => ψ (Additive.ofMul b)
      map_one' := ψ.map_zero_eq_one
      map_mul' := fun b c => ψ.map_add_eq_mul (Additive.ofMul b) (Additive.ofMul c) }
  let c : Q →ₜ* ℂˣ :=
    { φ.toHomUnits with continuous_toFun := continuous_of_discreteTopology }
  refine ⟨c.comp q, ?_⟩
  intro h
  apply hψ
  exact congrArg Units.val h

private theorem integral_units_totallyDisconnected
    {K : Type u} [Field K] [NumberField K] (v : FinitePlace K) :
    TotallyDisconnectedSpace (v.adicCompletionIntegers K)ˣ := by
  let : ValuativeRel (FiniteCompletion K v) :=
    (CompletionPadic.topologicalData v).valuativeRel
  let : IsNonarchimedeanLocalField (FiniteCompletion K v) :=
    (CompletionPadic.topologicalData v).localField
  let : TotallyDisconnectedSpace (FiniteCompletion K v) := inferInstance
  let : TotallyDisconnectedSpace (v.adicCompletionIntegers K) := inferInstance
  let : TotallyDisconnectedSpace (v.adicCompletionIntegers K)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.isTotallyDisconnected_range.mp
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)
  exact Units.isEmbedding_embedProduct.isTotallyDisconnected_range.mp
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

private theorem deep_nonidentity_unit
    {K : Type u} [Field K] [NumberField K] (v : FinitePlace K) (r : ℕ) :
    ∃ a : (v.adicCompletionIntegers K)ˣ,
      (a : v.adicCompletionIntegers K) - 1 ∈
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ r ∧ a ≠ 1 := by
  obtain ⟨x, hx⟩ := valuedAdicCompletion_surjective K v (WithZero.exp (-1 : ℤ))
  have hxlt : Valued.v x < 1 := by
    rw [hx, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  let π : v.adicCompletionIntegers K := ⟨x, hxlt.le⟩
  have hπ : π ≠ 0 := by
    intro h
    have hz : x = 0 := congrArg Subtype.val h
    rw [hz, map_zero] at hx
    exact WithZero.exp_ne_zero hx.symm
  have hπm : π ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      adicCompletionIntegers.isUnit_iff_valued_eq_one]
    exact hxlt.ne
  let b := π ^ (r + 1)
  have hbm : b ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) :=
    Ideal.pow_le_self (by omega : r + 1 ≠ 0) (Ideal.pow_mem_pow hπm (r + 1))
  have hbr : b ∈ (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ r :=
    Ideal.pow_le_pow_right (Nat.le_succ r) (Ideal.pow_mem_pow hπm (r + 1))
  have hunit : IsUnit (1 + b) := by
    simpa only [sub_neg_eq_add] using
      IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-b)
        ((IsLocalRing.mem_maximalIdeal (-b)).mp
          ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)).neg_mem hbm))
  refine ⟨hunit.unit, ?_, ?_⟩
  · simpa only [hunit.unit_spec, add_sub_cancel_left] using hbr
  · intro h
    have hbzero : b = 0 := by
      have heq := congrArg Units.val h
      simpa only [hunit.unit_spec, Units.val_one, add_eq_left] using heq
    exact (pow_ne_zero _ hπ) hbzero

end LocalRamifiedCharacters

/-- Finite-order continuous local characters detect every requested depth of
actual principal units, for arbitrary number-field universe. -/
theorem localCharactersArbitrarilyRamified :
    LocalCharactersArbitrarilyRamifiedStatement.{u} := by
  intro K _ _ v r
  let : CompactSpace (v.adicCompletionIntegers K) :=
    isCompact_iff_compactSpace.mp (isCompact_adicCompletionIntegers K v)
  let : TotallyDisconnectedSpace (v.adicCompletionIntegers K)ˣ :=
    LocalRamifiedCharacters.integral_units_totallyDisconnected v
  obtain ⟨a, har, ha⟩ := LocalRamifiedCharacters.deep_nonidentity_unit v r
  obtain ⟨η, hη⟩ := LocalRamifiedCharacters.compact_character_separates a ha
  obtain ⟨χ, hχorder, hχunits⟩ := integralUnitCharacterExtension K v η
  refine ⟨χ, hχorder, a, har, ?_⟩
  rw [hχunits]
  exact hη

end Langlands.Global
