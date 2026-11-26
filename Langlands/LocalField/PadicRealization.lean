import Langlands.LocalField.PadicBridge
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.GroupTheory.ArchimedeanDensely
import Mathlib.NumberTheory.Padics.WithVal

/-!
# Realizing characteristic-zero local fields on their supplied carrier

For a field `F` of characteristic zero with supplied local-field data
`T : LocalFieldData F` and a prime `p` that is the characteristic of
`T.ResidueField`, the inclusion of `ℚ` extends to a continuous embedding
`Padic p →+* F`. The resulting `Padic p`-algebra structure makes
`T.toPadicField p` a finite extension of `Padic p` whose carrier and field
operations are those of `F`, and `T.toPadicTopologicalData p` retains the
supplied topology, valuative relation and local-field certificate, so that
forgetting the p-adic structure returns `T` by `rfl`.

Source: Weil, *Basic Number Theory*, second edition (1973), Chapter I, §3,
Theorem 5(b), and §4, Theorem 6, in characteristic zero. See the paired
Markdown for the proof route.
-/

namespace Langlands.LocalFieldData

open ValuativeRel
open scoped ValuativeRel

universe u

section RationalValuation

variable (F : Type u) [Field F] [ValuativeRel F] {p : ℕ} [CharP 𝓀[F] p]

private theorem valuation_intCast_le_one (z : ℤ) : valuation F (z : F) ≤ 1 := by
  let A := (valuation F).valuationSubring
  have hz := (z : A).property
  rwa [show ((z : A) : F) = (z : F) from map_intCast A.subtype z] at hz

private theorem valuation_intCast_lt_one (z : ℤ) :
    valuation F (z : F) < 1 ↔ (p : ℤ) ∣ z := by
  let A := (valuation F).valuationSubring
  rw [← map_intCast A.subtype z]
  change valuation F ((z : A) : F) < 1 ↔ (p : ℤ) ∣ z
  rw [← (valuation F).mem_maximalIdeal_iff, ← IsLocalRing.residue_eq_zero_iff,
    map_intCast, CharP.intCast_eq_zero_iff 𝓀[F] p]

variable [CharZero F] [Fact p.Prime]

/-- In the prime subfield, integrality is equivalent to a reduced denominator
prime to the residue characteristic. -/
theorem valuation_ratCast_le_one_iff (x : ℚ) :
    valuation F (x : F) ≤ 1 ↔ ¬ p ∣ x.den := by
  have hd : 0 < valuation F (x.den : F) := by
    simp [zero_lt_iff, x.den_ne_zero]
  rw [Rat.cast_def, map_div₀, div_le_one₀ hd]
  have hden : valuation F (x.den : F) ≤ 1 := by
    simpa using valuation_intCast_le_one F (x.den : ℤ)
  have hden' : valuation F (x.den : F) < 1 ↔ p ∣ x.den := by
    simpa only [Int.cast_natCast, Int.natCast_dvd_natCast] using
      valuation_intCast_lt_one F (p := p) (x.den : ℤ)
  by_cases h : p ∣ x.den
  · have hnum : ¬ (p : ℤ) ∣ x.num := fun hnum ↦
      Nat.not_coprime_of_dvd_of_dvd (Fact.out : p.Prime).one_lt
        (Int.natCast_dvd.mp hnum) h x.reduced
    have hn : valuation F (x.num : F) = 1 :=
      (valuation_intCast_le_one F x.num).antisymm
        (not_lt.mp (fun hlt ↦ hnum ((valuation_intCast_lt_one F x.num).mp hlt)))
    simp [h, hn, not_le.mpr (hden'.mpr h)]
  · have heq : valuation F (x.den : F) = 1 :=
      hden.antisymm (not_lt.mp (fun hlt ↦ h (hden'.mp hlt)))
    simp [h, heq, valuation_intCast_le_one F x.num]

/-- The restriction of the supplied valuation to the prime subfield is equivalent
to the rational `p`-adic valuation. -/
theorem valuation_ratCast_isEquiv :
    ((valuation F).comap (Rat.castHom F)).IsEquiv (Rat.padicValuation p) :=
  Valuation.isEquiv_of_val_le_one (fun x ↦
    (valuation_ratCast_le_one_iff F x).trans Rat.padicValuation_le_one_iff.symm)

end RationalValuation

section PadicEmbedding

open Filter
open scoped Topology

variable (F : Type u) [Field F] [CharZero F] [TopologicalSpace F] [ValuativeRel F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [CharP 𝓀[F] p]

private def padicRatMap : WithVal (Rat.padicValuation p) →+* F :=
  (Rat.castHom F).comp (WithVal.equiv (Rat.padicValuation p)).toRingHom

private theorem continuous_padicRatMap : Continuous (padicRatMap F p) := by
  let v := WithVal.valuation (Rat.padicValuation p)
  refine continuous_of_continuousAt_zero (padicRatMap F p) ?_
  change Tendsto (padicRatMap F p) (𝓝 0) (𝓝 (padicRatMap F p 0))
  rw [map_zero]
  refine ((Valued.hasBasis_nhds_zero _ _).tendsto_iff
    (IsValuativeTopology.hasBasis_nhds_zero F)).2 ?_
  intro γ _
  have hp : valuation F (p : F) < 1 := by
    simpa only [Int.cast_natCast] using
      (valuation_intCast_lt_one F (p : ℤ)).2 dvd_rfl
  have : MulArchimedean (ValueGroupWithZero F) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hp γ
  let a : WithVal (Rat.padicValuation p) := (p : WithVal (Rat.padicValuation p)) ^ n
  have ha : a ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  refine ⟨Units.mk0 (v.restrict a) (by simpa using ha), trivial, ?_⟩
  intro x hx
  change v.restrict x < v.restrict a at hx
  have hx' := v.restrict_lt_iff.mp hx
  have h := (valuation_ratCast_isEquiv F (p := p)).lt_iff_lt.mpr hx'
  change valuation F (padicRatMap F p x) < γ.val
  refine h.trans ?_
  change valuation F (padicRatMap F p a) < γ.val
  simpa only [a, map_pow, map_natCast] using hn

noncomputable local instance : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
local instance : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
local instance : T2Space F := (ofInstances F).fieldT2

/-- The completion of the prime-field embedding at the residue characteristic. -/
noncomputable def padicEmbedding : Padic p →+* F :=
  (UniformSpace.Completion.extensionHom (padicRatMap F p) (continuous_padicRatMap F p)).comp
    (Padic.withValRingEquiv (p := p)).symm.toRingHom

/-- The completion embedding is continuous for the supplied topology on `F`. -/
theorem continuous_padicEmbedding : Continuous (padicEmbedding F p) :=
  UniformSpace.Completion.continuous_extension.comp
    (Padic.withValUniformEquiv (p := p)).symm.continuous

@[simp] theorem padicEmbedding_ratCast (x : ℚ) :
    padicEmbedding F p (x : Padic p) = (x : F) := map_ratCast _ _

/-- The continuous embedding extends the p-adic valuation up to equivalence. -/
theorem padicEmbedding_isEquiv :
    ((valuation F).comap (padicEmbedding F p)).IsEquiv (Padic.mulValuation (p := p)) := by
  refine Valuation.isEquiv_of_val_le_one ?_
  let s : Set (Padic p) := {x | valuation F (padicEmbedding F p x) ≤ 1}
  let t : Set (Padic p) := {x | Padic.mulValuation x ≤ 1}
  have hs : IsClopen s := by
    have h : IsClopen {x | valuation F x ≤ 1} := by
      simpa only [Valuation.restrict_le_one_iff] using
        ((valuation F).isClopen_closedBall (r := 1) one_ne_zero)
    exact h.preimage (continuous_padicEmbedding F p)
  have ht : IsClopen t := by
    simpa only [Valuation.restrict_le_one_iff] using
      ((Padic.mulValuation (p := p)).isClopen_closedBall (r := 1) one_ne_zero)
  have heq : IsClosed {x | x ∈ s ↔ x ∈ t} := by
    convert (hs.isClosed.inter ht.isClosed).union
      (hs.isOpen.isClosed_compl.inter ht.isOpen.isClosed_compl) using 1
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
    tauto
  refine isClosed_property (Padic.denseRange_ratCast p) heq ?_
  intro x
  change valuation F (padicEmbedding F p (x : Padic p)) ≤ 1 ↔
    ((Padic.mulValuation (p := p)).comap (Rat.castHom (Padic p))) x ≤ 1
  rw [padicEmbedding_ratCast, Padic.comap_mulValuation_eq_padicValuation]
  exact (valuation_ratCast_isEquiv F (p := p)).le_one_iff_le_one

/-- The algebra structure induced by the completion embedding. -/
@[instance_reducible]
noncomputable def padicAlgebra : Algebra (Padic p) F := (padicEmbedding F p).toAlgebra

private theorem padic_valuativeExtension :
    letI := padicAlgebra F p
    ValuativeExtension (Padic p) F := by
  let := padicAlgebra F p
  refine ⟨fun a b ↦ ?_⟩
  rw [(valuation F).vle_iff_le, (Padic.mulValuation (p := p)).vle_iff_le]
  exact (padicEmbedding_isEquiv F p).le_iff_le

private theorem padic_continuousSMul :
    letI := padicAlgebra F p
    ContinuousSMul (Padic p) F := by
  let := padicAlgebra F p
  exact ⟨((continuous_padicEmbedding F p).comp continuous_fst).mul continuous_snd⟩

private theorem padic_finiteDimensional :
    letI := padicAlgebra F p
    FiniteDimensional (Padic p) F := by
  let := padicAlgebra F p
  have := padic_continuousSMul F p
  exact FiniteDimensional.of_locallyCompactSpace (Padic p)

private theorem padic_moduleTopology :
    letI := padicAlgebra F p
    IsModuleTopology (Padic p) F := by
  let := padicAlgebra F p
  have := padic_continuousSMul F p
  have := padic_finiteDimensional F p
  exact isModuleTopologyOfFiniteDimensional

/-- The completion embedding is a closed topological embedding: a `Padic p`-linear
retraction of `F` onto the image is continuous for the module topology. -/
theorem isClosedEmbedding_padicEmbedding :
    Topology.IsClosedEmbedding (padicEmbedding F p) := by
  let := padicAlgebra F p
  have := padic_continuousSMul F p
  have := padic_finiteDimensional F p
  have := padic_moduleTopology F p
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap (Padic p) F)
    (LinearMap.ker_eq_bot.mpr (algebraMap (Padic p) F).injective)
  exact Function.LeftInverse.isClosedEmbedding (f := g) (fun x ↦ LinearMap.congr_fun hg x)
    (IsModuleTopology.continuous_of_linearMap g) (continuous_padicEmbedding F p)

end PadicEmbedding

section Realization

variable {F : Type u} [Field F] (T : LocalFieldData F)

/-- The actual residue field of a nonarchimedean local field has prime characteristic. -/
theorem residueCharacteristic_prime : (ringChar T.ResidueField).Prime := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : Finite T.ResidueField := inferInstanceAs (Finite 𝓀[F])
  exact CharP.prime_ringChar T.ResidueField

variable [CharZero F] (p : ℕ) [Fact p.Prime] [CharP T.ResidueField p]

/-- The p-adic field obtained on the supplied carrier, at the residue characteristic. -/
noncomputable def toPadicField : PadicField.{u} p := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := padicAlgebra F p
  have := padic_finiteDimensional F p
  exact PadicField.ofField F

/-- The finite-dimensional p-adic realization retaining the supplied topology
and valuative relation. -/
noncomputable def toPadicTopologicalData : (T.toPadicField p).TopologicalData := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact
    { topology := T.topology
      valuativeRel := T.valuativeRel
      localField := T.localField
      valuativeExtension := padic_valuativeExtension F p
      moduleTopology := padic_moduleTopology F p }

@[simp] theorem toPadicTopologicalData_toLocalFieldData :
    (T.toPadicTopologicalData p).toLocalFieldData = T := rfl

/-- The carrier of the realization is the original field. -/
@[simp] theorem toPadicField_carrier : (T.toPadicField p).Carrier = F := rfl

/-- The field structure of the realization is the original one. -/
theorem toPadicField_field : HEq (T.toPadicField p).field ‹Field F› := HEq.rfl

/-- The realization retains the supplied topology. -/
theorem toPadicTopologicalData_topology :
    (T.toPadicTopologicalData p).topology = T.topology := rfl

/-- The realization retains the supplied valuative relation. -/
theorem toPadicTopologicalData_valuativeRel :
    (T.toPadicTopologicalData p).valuativeRel = T.valuativeRel := rfl

/-- The realization retains the supplied local-field certificate. -/
theorem toPadicTopologicalData_localField :
    HEq (T.toPadicTopologicalData p).localField T.localField := HEq.rfl

/-- The algebra map of the realization extends the inclusion of the rationals. -/
@[simp] theorem algebraMap_toPadicField_ratCast (x : ℚ) :
    algebraMap (Padic p) (T.toPadicField p).Carrier (x : Padic p) = (x : F) :=
  map_ratCast _ x

/-- For the supplied topology, the algebra map of the realization is a closed
topological embedding. -/
theorem isClosedEmbedding_algebraMap_toPadicField :
    letI := (T.toPadicTopologicalData p).topology
    Topology.IsClosedEmbedding (algebraMap (Padic p) (T.toPadicField p).Carrier) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact isClosedEmbedding_padicEmbedding F p

/-- Restricting the supplied valuation along the algebra map gives the p-adic
valuation of `Padic p` up to equivalence. -/
theorem isEquiv_comap_algebraMap_toPadicField :
    letI := (T.toPadicTopologicalData p).valuativeRel
    ((ValuativeRel.valuation (T.toPadicField p).Carrier).comap
      (algebraMap (Padic p) (T.toPadicField p).Carrier)).IsEquiv
      (Padic.mulValuation (p := p)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact padicEmbedding_isEquiv F p

end Realization

end Langlands.LocalFieldData
