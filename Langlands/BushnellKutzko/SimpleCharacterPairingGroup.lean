import Langlands.BushnellKutzko.CharacterIntertwining
import Langlands.BushnellKutzko.SimpleStratumGroupPropertiesStatement

/-! # Group operations used in the simple-character commutator calculation -/

open ValuativeRel
open scoped commutatorElement

namespace Langlands.BushnellKutzko

universe uF uV uG

section Group

variable {G : Type uG} [Group G]

/-- Conjugation by a character normalizer can be evaluated on the original element. -/
theorem conj_mem_and_character_eq {H : Subgroup G} {χ : H →* ℂˣ} {u : G}
    (hu : u ∈ characterNormalizer χ) (x : H) :
    ∃ h : u * (x : G) * u⁻¹ ∈ H, χ ⟨_, h⟩ = χ x := by
  have h := (Subgroup.mem_normalizer_iff.mp hu.1 _).mp x.property
  exact ⟨h, hu.2 x h⟩

/-- Expand the commutator of two products when the first factors normalize
  the character and the three commutators involving either first factor are null. -/
theorem character_commutator_mul_mul {H : Subgroup G} {χ : H →* ℂˣ} {u v w z : G}
    (hu : u ∈ characterNormalizer χ) (hv : v ∈ characterNormalizer χ)
    (hwv : ⁅w, v⁆ ∈ H) (hwz : ⁅w, z⁆ ∈ H) (huv : ⁅u, v⁆ ∈ H) (huz : ⁅u, z⁆ ∈ H)
    (h₁ : χ ⟨_, hwv⟩ = 1) (h₂ : χ ⟨_, huv⟩ = 1) (h₃ : χ ⟨_, huz⟩ = 1)
    (h : ⁅u * w, v * z⁆ ∈ H) : χ ⟨_, h⟩ = χ ⟨_, hwz⟩ := by
  obtain ⟨hA, hAe⟩ := conj_mem_and_character_eq hu ⟨_, hwv⟩
  obtain ⟨hB, hBe⟩ := conj_mem_and_character_eq hv ⟨_, hwz⟩
  obtain ⟨hC, hCe⟩ := conj_mem_and_character_eq hu ⟨_, hB⟩
  obtain ⟨hD, hDe⟩ := conj_mem_and_character_eq hv ⟨_, huz⟩
  have heq : (⟨_, h⟩ : H) = ⟨_, hA⟩ * ⟨_, hC⟩ * ⟨_, huv⟩ * ⟨_, hD⟩ := by
    apply Subtype.ext
    change ⁅u * w, v * z⁆ = u * ⁅w, v⁆ * u⁻¹ * (u * (v * ⁅w, z⁆ * v⁻¹) * u⁻¹) *
      ⁅u, v⁆ * (v * ⁅u, z⁆ * v⁻¹)
    simp only [commutatorElement_def]
    group
  rw [heq, map_mul, map_mul, map_mul, hAe, hCe, hBe, hDe, h₁, h₂, h₃, one_mul, mul_one, mul_one]

/-- Evaluation on a reversed commutator inverts the character value. -/
theorem character_commutator_swap {H : Subgroup G} (χ : H →* ℂˣ) {u v : G}
    (h₁ : ⁅u, v⁆ ∈ H) (h₂ : ⁅v, u⁆ ∈ H) : χ ⟨_, h₁⟩ = (χ ⟨_, h₂⟩)⁻¹ := by
  have he : (⟨_, h₁⟩ : H) = (⟨_, h₂⟩ : H)⁻¹ := Subtype.ext (commutatorElement_inv _ _).symm
  rw [he, map_inv]

end Group

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => Aˣ
local notation "O" => 𝒪[F]

namespace SimpleStratum

local notation "H[" s "," q "]" => simpleHGroup (Stratum.chain s) (Stratum.n s) (Stratum.b s)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "J[" s "," q "]" => simpleJGroup (Stratum.chain s) (Stratum.n s) (Stratum.b s)
  (Stratum.DefiningSequenceChoice.tail q)

/-- The subgroup commutator estimate may be applied to individual representatives. -/
theorem commutator_mem_HGroup (hG : SimpleStratumGroupPropertiesStatement.{uF,uV})
    (S : Stratum O F V) (hS0 : S.r = 0) (hS : S.IsSimple) (q : S.DefiningSequenceChoice)
    {x y : G} {k l p : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hp : p ≤ k + l)
    (hx : x ∈ J[S,q] k) (hy : y ∈ J[S,q] l) : ⁅x, y⁆ ∈ H[S,q] p := by
  have h := (hG F V S hS0 hS q).2.2.2.2 k l hk hl
  exact simpleHGroup_antitone S.chain S.n S.b q.tail hp (h (Subgroup.commutator_mem_commutator hx hy))

end SimpleStratum

end Langlands.BushnellKutzko
