import Langlands.ClassFieldTheory.Local.UniversalNormRootDescent
import Langlands.ClassFieldTheory.Local.NormExistenceFiberSupport
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.GroupTheory.OrderOfElement

/-! # Divisibility inside the actual universal norm subgroup -/

noncomputable section

namespace Langlands.LocalClassField

universe u

/-- The family of actual finite abelian intermediate-field norm groups. -/
def finiteAbelianNormFamily (K : Type u) [Field K] : Set (Subgroup Kˣ) :=
  {N | ∃ E : FiniteIntermediateExtension K,
    IsAbelianGalois K E.field ∧ normSubgroup K E.field = N}

theorem finiteAbelianNormFamily_nonempty (K : Type u) [Field K] :
    (finiteAbelianNormFamily K).Nonempty := by
  let E : FiniteIntermediateExtension K :=
    ⟨⊥, inferInstance⟩
  exact ⟨normSubgroup K E.field, E, inferInstance, rfl⟩

theorem mem_universalNormSubgroup_iff (K : Type u) [Field K] (a : Kˣ) :
    a ∈ universalNormSubgroup K ↔
      ∀ N ∈ finiteAbelianNormFamily K, a ∈ N := by
  constructor
  · rintro ha N ⟨E, hAb, rfl⟩
    let := hAb
    exact ha E.field
  · intro ha E hfd hAb
    exact ha (normSubgroup K E) ⟨⟨E, hfd⟩, hAb, rfl⟩

/-- The arithmetic universal-norm lifting input, for all actual finite
extensions of p-adic fields in the same arbitrary carrier universe. -/
def UniversalNormLifting : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F E : PadicField.{u} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier],
    letI : FiniteDimensional F.Carrier E.Carrier :=
      FiniteDimensional.right (Padic p) F.Carrier E.Carrier
    ∀ a : F.Carrierˣ, a ∈ universalNormSubgroup F.Carrier →
      ∃ b : E.Carrierˣ, b ∈ universalNormSubgroup E.Carrier ∧
        normUnits F.Carrier E.Carrier b = a

end Langlands.LocalClassField

namespace Langlands.ClassFieldTheory.Local

universe u

open Langlands.LocalClassField

/-- Global arithmetic lifting removes the roots-of-unity hypothesis from
the prime-power conclusion in the ambient field-unit group. -/
theorem universalNorm_prime_root_of_lifting
    (hLift : UniversalNormLifting.{u})
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    {q : ℕ} (hq : q.Prime) (a : F.Carrierˣ)
    (ha : a ∈ universalNormSubgroup F.Carrier) :
    ∃ c : F.Carrierˣ, c ^ q = a := by
  apply KummerNorm.prime_power_of_universal_lift F hq a
  intro E hfd
  let E' : FiniteIntermediateExtension F.Carrier := ⟨E, hfd⟩
  let F' : PadicField.{u} p := E'.asPadicField
  let : Algebra (Padic p) F'.Carrier := F'.algebra
  let hTower : IsScalarTower (Padic p) F.Carrier F'.Carrier :=
    IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨b, hbU, hb⟩ := @hLift p inferInstance F F' inferInstance hTower a ha
  exact ⟨b, hb, hbU⟩

/-- Compact power fibers produce prime roots inside the universal subgroup
from global arithmetic lifting and a directed closed norm family. -/
theorem universalNorm_prime_root_mem_of_lifting
    (hLift : UniversalNormLifting.{u})
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData)
    (hdir : DirectedOn (· ≥ ·) (finiteAbelianNormFamily F.Carrier))
    (hclosed : letI := T.topology
      ∀ N ∈ finiteAbelianNormFamily F.Carrier, IsClosed (N : Set F.Carrierˣ))
    {q : ℕ} (hq : q.Prime) (a : F.Carrierˣ)
    (ha : a ∈ universalNormSubgroup F.Carrier) :
    ∃ c : F.Carrierˣ, c ∈ universalNormSubgroup F.Carrier ∧ c ^ q = a := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let f : F.Carrierˣ →ₜ* F.Carrierˣ :=
    { powMonoidHom q with continuous_toFun := continuous_id.pow q }
  have hpre : ∀ N ∈ finiteAbelianNormFamily F.Carrier, a ∈ N.map f.toMonoidHom := by
    rintro N ⟨E, hAb, rfl⟩
    let F' : PadicField.{u} p := E.asPadicField
    let : Algebra (Padic p) F'.Carrier := F'.algebra
    let hTower : IsScalarTower (Padic p) F.Carrier F'.Carrier :=
      IsScalarTower.of_algebraMap_eq' rfl
    obtain ⟨b, hbU, hb⟩ := @hLift p inferInstance F F' inferInstance hTower a ha
    obtain ⟨c, hc⟩ := universalNorm_prime_root_of_lifting hLift F' hq b hbU
    refine ⟨normUnits F.Carrier E.field c, ⟨c, rfl⟩, ?_⟩
    change (normUnits F.Carrier E.field c) ^ q = a
    rw [← map_pow, hc, hb]
  obtain ⟨c, hc, hcN⟩ := exists_universal_preimage_of_compact_fiber f
    (finiteAbelianNormFamily F.Carrier) (finiteAbelianNormFamily_nonempty F.Carrier)
    hdir hclosed a (isCompact_power_fiber F T q hq.ne_zero a) hpre
  exact ⟨c, (mem_universalNormSubgroup_iff F.Carrier c).mpr hcN, hc⟩

/-- Prime roots within a subgroup give roots of every positive natural order. -/
theorem subgroup_all_roots_of_prime_roots
    {G : Type u} [Group G] (U : Subgroup G)
    (hprime : ∀ (q : ℕ), q.Prime → ∀ a ∈ U, ∃ b : G, b ∈ U ∧ b ^ q = a) :
    ∀ (n : ℕ), n ≠ 0 → ∀ a ∈ U, ∃ b : G, b ∈ U ∧ b ^ n = a := by
  refine induction_on_primes (motive := fun n =>
    n ≠ 0 → ∀ a ∈ U, ∃ b : G, b ∈ U ∧ b ^ n = a) ?_ ?_ ?_
  · intro h
    exact (h rfl).elim
  · intro _ a ha
    exact ⟨a, ha, pow_one a⟩
  · intro q n hq ih hn a ha
    have hn' : n ≠ 0 := fun h => hn (by rw [h, mul_zero])
    obtain ⟨b, hb, hba⟩ := hprime q hq a ha
    obtain ⟨c, hc, hcb⟩ := ih hn' b hb
    refine ⟨c, hc, ?_⟩
    rw [Nat.mul_comm q n, pow_mul, hcb, hba]

/-- A subgroup divisible by all positive natural numbers lies in every
finite-index subgroup of a commutative group. -/
theorem subgroup_le_finiteIndex_of_all_roots
    {G : Type u} [CommGroup G] (U : Subgroup G)
    (hroots : ∀ (n : ℕ), n ≠ 0 → ∀ a ∈ U, ∃ b : G, b ∈ U ∧ b ^ n = a)
    (H : Subgroup G) [H.FiniteIndex] : U ≤ H := by
  intro a ha
  obtain ⟨b, _, hb⟩ := hroots H.index Subgroup.FiniteIndex.index_ne_zero a ha
  rw [← hb]
  exact H.pow_index_mem b

/-- Conditional divisibility of the actual universal norm subgroup. -/
theorem universalNorm_all_roots_of_lifting
    (hLift : UniversalNormLifting.{u})
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData)
    (hdir : DirectedOn (· ≥ ·) (finiteAbelianNormFamily F.Carrier))
    (hclosed : letI := T.topology
      ∀ N ∈ finiteAbelianNormFamily F.Carrier, IsClosed (N : Set F.Carrierˣ)) :
    ∀ (n : ℕ), n ≠ 0 → ∀ a ∈ universalNormSubgroup F.Carrier,
      ∃ b : F.Carrierˣ, b ∈ universalNormSubgroup F.Carrier ∧ b ^ n = a := by
  apply subgroup_all_roots_of_prime_roots
  intro q hq a ha
  exact universalNorm_prime_root_mem_of_lifting hLift F T hdir hclosed hq a ha

/-- Conditional containment in every finite-index subgroup; no openness
assumption is needed for this purely group-theoretic consequence. -/
theorem universalNorm_le_finiteIndex_of_lifting
    (hLift : UniversalNormLifting.{u})
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData)
    (hdir : DirectedOn (· ≥ ·) (finiteAbelianNormFamily F.Carrier))
    (hclosed : letI := T.topology
      ∀ N ∈ finiteAbelianNormFamily F.Carrier, IsClosed (N : Set F.Carrierˣ))
    (H : Subgroup F.Carrierˣ) [H.FiniteIndex] :
    universalNormSubgroup F.Carrier ≤ H :=
  subgroup_le_finiteIndex_of_all_roots _ (universalNorm_all_roots_of_lifting
    hLift F T hdir hclosed) H

end Langlands.ClassFieldTheory.Local
