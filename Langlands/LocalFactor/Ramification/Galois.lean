import Langlands.LocalField.Normalization.Definitions
import Langlands.LocalFactor.Ramification.Conductor
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.FieldTheory.Minpoly.Field

/-!
# The actual integer-ring action of finite p-adic Galois groups

Continuity of algebra automorphisms and the topological characterization of
strictly positive valuation construct the action on the supplied integer ring.
No norm-comparison or reciprocity theorem is assumed.
-/

noncomputable section

namespace Langlands.Ramification

open Filter ValuativeRel IsLocalRing
open scoped Topology

private theorem valuation_lt_one_iff_pow_tendsto
    {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] (x : L) :
    valuation L x < 1 ↔ Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  constructor
  · intro hx
    let := IsTopologicalAddGroup.rightUniformSpace L
    have := isUniformAddGroup_of_addCommGroup (G := L)
    have : MulArchimedean (ValueGroupWithZero L) :=
      ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
    exact Valued.tendsto_zero_pow_of_v_lt_one hx
  · intro h
    have hball : {z : L | valuation L z < 1} ∈ 𝓝 (0 : L) :=
      (IsValuativeTopology.hasBasis_nhds_zero' L).mem_of_mem (by simp)
    obtain ⟨n, hn⟩ := (h.eventually hball).exists
    by_contra hx
    have hge : 1 ≤ valuation L x := le_of_not_gt hx
    have hn' : valuation L x ^ n < 1 := by simpa only [Set.mem_ofPred_eq, map_pow] using hn
    exact (not_lt_of_ge (one_le_pow₀ hge)) hn'

private theorem preserves_integers_of_continuous
    {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] (σ : L ≃+* L)
    (hσ : Continuous σ.symm) {x : L} (hx : valuation L x ≤ 1) :
    valuation L (σ x) ≤ 1 := by
  by_contra h
  have hy : 1 < valuation L (σ x) := lt_of_not_ge h
  have hx0 : x ≠ 0 := by
    intro hx0
    simp [hx0] at hy
  have hinv : valuation L ((σ x)⁻¹) < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ hy
  have hpow := (valuation_lt_one_iff_pow_tendsto ((σ x)⁻¹)).mp hinv
  have hback : Tendsto (fun n : ℕ => (x⁻¹) ^ n) atTop (𝓝 0) := by
    simpa only [Function.comp_def, map_pow, map_inv₀, RingEquiv.symm_apply_apply,
      map_zero] using (hσ.tendsto 0).comp hpow
  have hval := (valuation_lt_one_iff_pow_tendsto (x⁻¹)).mpr hback
  rw [map_inv₀] at hval
  have hpos : 0 < valuation L x := by simpa only [zero_lt_iff, map_ne_zero] using hx0
  exact (not_lt_of_ge hx) ((inv_lt_one₀ hpos).mp hval)

namespace Padic

universe uK uL

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p}
  (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
  [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]

/-- Every base-field automorphism acts on the actual supplied valuation ring.
The canonical module topology proves the needed continuity. -/
def integerAutomorphism (σ : F.Carrier ≃ₐ[K] F.Carrier) :
    T.Integers ≃+* T.Integers := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.moduleTopology
  letI := T.localField
  have hσ : Continuous (σ.restrictScalars (Padic p)) :=
    IsModuleTopology.continuous_of_linearMap (σ.restrictScalars (Padic p)).toLinearMap
  have hσinv : Continuous (σ.symm.restrictScalars (Padic p)) :=
    IsModuleTopology.continuous_of_linearMap
      (σ.symm.restrictScalars (Padic p)).toLinearMap
  exact
  { toFun x := ⟨σ x, preserves_integers_of_continuous σ.toRingEquiv hσinv x.property⟩
    invFun x := ⟨σ.symm x, preserves_integers_of_continuous σ.symm.toRingEquiv hσ x.property⟩
    left_inv x := Subtype.ext (σ.symm_apply_apply x)
    right_inv x := Subtype.ext (σ.apply_symm_apply x)
    map_mul' x y := Subtype.ext (σ.map_mul x y)
    map_add' x y := Subtype.ext (σ.map_add x y) }

/-- The actual restriction homomorphism on the integer ring. -/
def integerAutHom : (F.Carrier ≃ₐ[K] F.Carrier) →* RingAut T.Integers where
  toFun := integerAutomorphism T K
  map_one' := by
    ext x
    rfl
  map_mul' _ _ := by
    ext x
    rfl

/-- Explicit action data, installed locally in all constructions below. -/
abbrev integerAction : MulSemiringAction (F.Carrier ≃ₐ[K] F.Carrier) T.Integers :=
  MulSemiringAction.compHom _ (integerAutHom T K)

private theorem integerAction_faithful :
    letI := integerAction T K
    FaithfulSMul (F.Carrier ≃ₐ[K] F.Carrier) T.Integers := by
  let := integerAction T K
  let := T.valuativeRel
  have : IsFractionRing T.Integers F.Carrier :=
    inferInstanceAs (IsFractionRing
      (ValuativeRel.valuation F.Carrier).valuationSubring F.Carrier)
  refine ⟨fun {σ τ} h => ?_⟩
  have heq : σ.toRingHom = τ.toRingHom :=
    IsFractionRing.ringHom_ext (A := T.Integers) (fun x =>
      congrArg (fun y : T.Integers => (y : F.Carrier)) (h x))
  exact AlgEquiv.ext fun x => RingHom.congr_fun heq x

private theorem integerRing_noetherian : IsNoetherianRing T.Integers := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  infer_instance

private theorem automorphismGroup_finite : Finite (F.Carrier ≃ₐ[K] F.Carrier) := by
  have : FiniteDimensional K F.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) K F.Carrier
  infer_instance

/-- The homomorphism induced on the supplied actual residue field. -/
def residueHom : (F.Carrier ≃ₐ[K] F.Carrier) →* RingAut T.ResidueField :=
  IsLocalRing.ResidueField.mapAut.comp (integerAutHom T K)

/-- Inertia is the kernel of the actual residue-field action. -/
def inertia : Subgroup (F.Carrier ≃ₐ[K] F.Carrier) := (residueHom T K).ker

/-- The nonnegative lower ramification filtration on the full automorphism group. -/
def lowerRamificationGroup (i : ℕ) : Subgroup (F.Carrier ≃ₐ[K] F.Carrier) :=
  letI := integerAction T K
  lowerGroup T.Integers (F.Carrier ≃ₐ[K] F.Carrier) i

@[simp] theorem mem_lowerRamificationGroup (i : ℕ) (σ : F.Carrier ≃ₐ[K] F.Carrier) :
    σ ∈ lowerRamificationGroup T K i ↔
      ∀ x : T.Integers, integerAutomorphism T K σ x - x ∈
        maximalIdeal T.Integers ^ (i + 1) := Iff.rfl

/-- The constructed zeroth group is exactly the constructed inertia kernel. -/
theorem lowerRamificationGroup_zero : lowerRamificationGroup T K 0 = inertia T K := by
  ext σ
  rw [mem_lowerRamificationGroup]
  simp only [zero_add, pow_one, inertia, MonoidHom.mem_ker]
  constructor
  · intro h
    ext y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    change residue T.Integers (integerAutomorphism T K σ x) = residue T.Integers x
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact h x
  · intro h x
    have hx := congrArg (fun e : RingAut T.ResidueField => e (residue T.Integers x)) h
    change residue T.Integers (integerAutomorphism T K σ x) = residue T.Integers x at hx
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
    exact hx

theorem exists_lowerRamificationGroup_eq_bot :
    ∃ b : ℕ, ∀ i ≥ b, lowerRamificationGroup T K i = ⊥ := by
  let := integerAction T K
  have := integerAction_faithful T K
  have := integerRing_noetherian T
  have := automorphismGroup_finite (F := F) K
  exact exists_lowerGroup_eq_bot T.Integers (F.Carrier ≃ₐ[K] F.Carrier)

/-- Integer indexing, with `G_{-1}` equal to the full group and constant
extension below `-1`. -/
def lowerRamificationGroupInt (i : ℤ) : Subgroup (F.Carrier ≃ₐ[K] F.Carrier) :=
  letI := integerAction T K
  lowerGroupInt T.Integers (F.Carrier ≃ₐ[K] F.Carrier) i

@[simp] theorem lowerRamificationGroupInt_neg_one :
    lowerRamificationGroupInt T K (-1) = ⊤ := by
  let := integerAction T K
  exact lowerGroupInt_neg_one _ _

instance lowerRamificationGroup_normal (i : ℕ) :
    (lowerRamificationGroup T K i).Normal := by
  let := integerAction T K
  exact lowerGroup_normal T.Integers (F.Carrier ≃ₐ[K] F.Carrier) i

theorem lowerRamificationGroup_antitone : Antitone (lowerRamificationGroup T K) := by
  let := integerAction T K
  exact lowerGroup_antitone T.Integers (F.Carrier ≃ₐ[K] F.Carrier)

/-- Restriction to the actual finite inertia group. -/
abbrev inertiaIntegerAction : MulSemiringAction (inertia T K) T.Integers :=
  MulSemiringAction.compHom _ ((integerAutHom T K).comp (inertia T K).subtype)

private theorem inertiaIntegerAction_faithful :
    letI := inertiaIntegerAction T K
    FaithfulSMul (inertia T K) T.Integers := by
  let := inertiaIntegerAction T K
  let := integerAction T K
  have := integerAction_faithful T K
  refine ⟨fun {σ τ} h => Subtype.ext ?_⟩
  exact FaithfulSMul.eq_of_smul_eq_smul (α := T.Integers) h

/-- The same actual lower groups, regarded as subgroups of inertia. -/
def inertiaLowerGroup (i : ℕ) : Subgroup (inertia T K) :=
  (lowerRamificationGroup T K i).subgroupOf (inertia T K)

@[simp] theorem inertiaLowerGroup_zero : inertiaLowerGroup T K 0 = ⊤ := by
  ext σ
  simp [inertiaLowerGroup, lowerRamificationGroup_zero]

private theorem inertiaLowerGroup_eq (i : ℕ) :
    letI := inertiaIntegerAction T K
    inertiaLowerGroup T K i = lowerGroup T.Integers (inertia T K) i := rfl

universe uk uV
variable {k : Type uk} [Field k] {V : Type uV} [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

/-- The actual finite-extension Artin expression. -/
def artinConductor (ρ : Representation k (F.Carrier ≃ₐ[K] F.Carrier) V) : ℚ := by
  letI := integerAction T K
  letI := integerAction_faithful T K
  letI := integerRing_noetherian T
  letI := automorphismGroup_finite (F := F) K
  exact Ramification.artinConductor T.Integers (F.Carrier ≃ₐ[K] F.Carrier) ρ

/-- The actual finite-extension Swan expression. -/
def swanConductor (ρ : Representation k (F.Carrier ≃ₐ[K] F.Carrier) V) : ℚ := by
  letI := integerAction T K
  letI := integerAction_faithful T K
  letI := integerRing_noetherian T
  letI := automorphismGroup_finite (F := F) K
  exact Ramification.swanConductor T.Integers (F.Carrier ≃ₐ[K] F.Carrier) ρ

/-- Artin expression for a representation of the actual finite inertia group.
It does not require an extension of that representation to the Galois group. -/
def inertiaArtinConductor (ρ : Representation k (inertia T K) V) : ℚ := by
  letI := inertiaIntegerAction T K
  letI := inertiaIntegerAction_faithful T K
  letI := integerRing_noetherian T
  letI := automorphismGroup_finite (F := F) K
  exact Ramification.artinConductor T.Integers (inertia T K) ρ

/-- Swan expression for a representation of the actual finite inertia group. -/
def inertiaSwanConductor (ρ : Representation k (inertia T K) V) : ℚ := by
  letI := inertiaIntegerAction T K
  letI := inertiaIntegerAction_faithful T K
  letI := integerRing_noetherian T
  letI := automorphismGroup_finite (F := F) K
  exact Ramification.swanConductor T.Integers (inertia T K) ρ

/-- The inertia denominator is its actual group cardinality, and the tame
term uses invariants of that whole group. -/
theorem inertiaArtinConductor_eq_tame_add_swan
    (ρ : Representation k (inertia T K) V) :
    inertiaArtinConductor T K ρ =
      (fixedCodimension (inertia T K) ρ ⊤ : ℚ) + inertiaSwanConductor T K ρ := by
  let := inertiaIntegerAction T K
  have := inertiaIntegerAction_faithful T K
  have := integerRing_noetherian T
  have := automorphismGroup_finite (F := F) K
  change Ramification.artinConductor T.Integers (inertia T K) ρ =
    (fixedCodimension (inertia T K) ρ ⊤ : ℚ) +
      Ramification.swanConductor T.Integers (inertia T K) ρ
  rw [Ramification.artinConductor_eq_tame_add_swan,
    ← inertiaLowerGroup_eq T K 0, inertiaLowerGroup_zero]

universe uW
variable {W : Type uW} [AddCommGroup W] [Module k W] [FiniteDimensional k W]

theorem artinConductor_equiv
    {ρ : Representation k (F.Carrier ≃ₐ[K] F.Carrier) V}
    {σ : Representation k (F.Carrier ≃ₐ[K] F.Carrier) W} (e : ρ.Equiv σ) :
    artinConductor T K ρ = artinConductor T K σ := by
  let := integerAction T K
  have := integerAction_faithful T K
  have := integerRing_noetherian T
  have := automorphismGroup_finite (F := F) K
  exact Ramification.artinConductor_equiv T.Integers (F.Carrier ≃ₐ[K] F.Carrier) e

theorem swanConductor_equiv
    {ρ : Representation k (F.Carrier ≃ₐ[K] F.Carrier) V}
    {σ : Representation k (F.Carrier ≃ₐ[K] F.Carrier) W} (e : ρ.Equiv σ) :
    swanConductor T K ρ = swanConductor T K σ := by
  let := integerAction T K
  have := integerAction_faithful T K
  have := integerRing_noetherian T
  have := automorphismGroup_finite (F := F) K
  exact Ramification.swanConductor_equiv T.Integers (F.Carrier ≃ₐ[K] F.Carrier) e

theorem inertiaArtinConductor_equiv
    {ρ : Representation k (inertia T K) V} {σ : Representation k (inertia T K) W}
    (e : ρ.Equiv σ) :
    inertiaArtinConductor T K ρ = inertiaArtinConductor T K σ := by
  let := inertiaIntegerAction T K
  have := inertiaIntegerAction_faithful T K
  have := integerRing_noetherian T
  have := automorphismGroup_finite (F := F) K
  exact Ramification.artinConductor_equiv T.Integers (inertia T K) e

theorem inertiaSwanConductor_equiv
    {ρ : Representation k (inertia T K) V} {σ : Representation k (inertia T K) W}
    (e : ρ.Equiv σ) :
    inertiaSwanConductor T K ρ = inertiaSwanConductor T K σ := by
  let := inertiaIntegerAction T K
  have := inertiaIntegerAction_faithful T K
  have := integerRing_noetherian T
  have := automorphismGroup_finite (F := F) K
  exact Ramification.swanConductor_equiv T.Integers (inertia T K) e

universe uJ
variable {J : Type uJ} [Group J]

/-- Descent through a specified surjective map to the actual finite inertia
group, with the kernel condition explicitly proved by the caller.
This constructor makes no existence or quotient-independence assertion. -/
def descendInertiaRepresentation
    (π : J →* inertia T K) (hπ : Function.Surjective π)
    (ρ : Representation k J V) (hker : π.ker ≤ ρ.ker) :
    Representation k (inertia T K) V :=
  (Units.coeHom (V →ₗ[k] V)).comp (π.liftOfSurjective hπ
    ⟨ρ.asGroupHom, fun _j hj => Units.ext (hker hj)⟩)

omit [FiniteDimensional k V] in
@[simp] theorem descendInertiaRepresentation_apply
    (π : J →* inertia T K) (hπ : Function.Surjective π)
    (ρ : Representation k J V) (hker : π.ker ≤ ρ.ker) (j : J) :
    descendInertiaRepresentation T K π hπ ρ hker (π j) = ρ j := by
  simp [descendInertiaRepresentation, MonoidHom.liftOfSurjective,
    Representation.asGroupHom_apply]

omit [FiniteDimensional k V] in
theorem descendInertiaRepresentation_unique
    (π : J →* inertia T K) (hπ : Function.Surjective π)
    (ρ : Representation k J V) (hker : π.ker ≤ ρ.ker)
    (σ : Representation k (inertia T K) V) (hσ : σ.comp π = ρ) :
    σ = descendInertiaRepresentation T K π hπ ρ hker := by
  apply MonoidHom.ext
  intro g
  obtain ⟨j, rfl⟩ := hπ g
  rw [descendInertiaRepresentation_apply]
  exact DFunLike.congr_fun hσ j

/-- Artin expression for an explicit finite inertia quotient. -/
def artinConductorOfQuotient
    (π : J →* inertia T K) (hπ : Function.Surjective π)
    (ρ : Representation k J V) (hker : π.ker ≤ ρ.ker) : ℚ :=
  inertiaArtinConductor T K (descendInertiaRepresentation T K π hπ ρ hker)

/-- Swan expression for an explicit finite inertia quotient. -/
def swanConductorOfQuotient
    (π : J →* inertia T K) (hπ : Function.Surjective π)
    (ρ : Representation k J V) (hker : π.ker ≤ ρ.ker) : ℚ :=
  inertiaSwanConductor T K (descendInertiaRepresentation T K π hπ ρ hker)

end Padic

end Langlands.Ramification
