import Langlands.Cohomology.Lie.HorizontalCohomology

/-! # Linear transport on the actual horizontal cohomology quotient -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Cohomology.Lie.Horizontal

universe u v w w' w'' ug

variable {K : Type u} [Field K] [CharZero K]
variable {L : Type v} [LieRing L] [LieAlgebra K L]
variable {M : Type w} [AddCommGroup M] [Module K M]
variable [LieRingModule L M] [LieModule K L M]
variable {N : Type w'} [AddCommGroup N] [Module K N]
variable [LieRingModule L N] [LieModule K L N]
variable {P : Type w''} [AddCommGroup P] [Module K P]
variable [LieRingModule L P] [LieModule K L P]
variable {G : Type ug} [Group G]

variable (H : Submodule K L) (σ : Representation K G L)
variable (ρ : Representation K G M) (τ : Representation K G N)
variable (hσ : ∀ g x y, σ g ⁅x, y⁆ = ⁅σ g x, σ g y⁆)
variable (hρ : ∀ g x m, ρ g ⁅x, m⁆ = ⁅σ g x, ρ g m⁆)
variable (hτ : ∀ g x n, τ g ⁅x, n⁆ = ⁅σ g x, τ g n⁆)
variable (hι : ∀ q, ∀ f ∈ Langlands.HorizontalAlternating.submodule H σ ρ q,
  ∀ y ∈ H, ∀ x : Fin q → L,
    ⁅y, f x⁆ = ∑ i, f (Function.update x i ⁅y, x i⁆))
variable (hκ : ∀ q, ∀ f ∈ Langlands.HorizontalAlternating.submodule H σ τ q,
  ∀ y ∈ H, ∀ x : Fin q → L,
    ⁅y, f x⁆ = ∑ i, f (Function.update x i ⁅y, x i⁆))

local notation "CM" => Langlands.HorizontalAlternating.submodule H σ ρ
local notation "CN" => Langlands.HorizontalAlternating.submodule H σ τ
local notation "DM" => differential H σ ρ hσ hρ hι
local notation "DN" => differential H σ τ hσ hτ hκ
local notation "ZM" => cycles H σ ρ hσ hρ hι
local notation "ZN" => cycles H σ τ hσ hτ hκ
local notation "BM" => boundaries H σ ρ hσ hρ hι
local notation "BN" => boundaries H σ τ hσ hτ hκ
local notation "BZM" => boundariesInCycles H σ ρ hσ hρ hι
local notation "BZN" => boundariesInCycles H σ τ hσ hτ hκ

local instance transportSourceCochainGroup (q : ℕ) : AddCommGroup (CM q) :=
  Submodule.addCommGroup _
local instance transportTargetCochainGroup (q : ℕ) : AddCommGroup (CN q) :=
  Submodule.addCommGroup _
local instance transportSourceCycleGroup (q : ℕ) : AddCommGroup (ZM q) :=
  Submodule.addCommGroup _
local instance transportTargetCycleGroup (q : ℕ) : AddCommGroup (ZN q) :=
  Submodule.addCommGroup _

variable (cochainMap : (q : ℕ) →
  Langlands.HorizontalAlternating.submodule H σ ρ q →ₗ[K]
    Langlands.HorizontalAlternating.submodule H σ τ q)
variable (hMap : ∀ (q : ℕ) (f : Langlands.HorizontalAlternating.submodule H σ ρ q),
  differential H σ τ hσ hτ hκ q (cochainMap q f) =
    cochainMap (q + 1) (differential H σ ρ hσ hρ hι q f))

include hMap

/-- A map commuting with the actual differentials preserves closed cochains. -/
theorem map_mem_cycles (q : ℕ) (f : CM q) (hf : f ∈ ZM q) :
    cochainMap q f ∈ ZN q := by
  change DM q f = 0 at hf
  change DN q (cochainMap q f) = 0
  rw [hMap q f, hf, map_zero]

/-- It also preserves the actual differential-image boundaries. -/
theorem map_mem_boundaries (q : ℕ) (f : CM q) (hf : f ∈ BM q) :
    cochainMap q f ∈ BN q := by
  cases q with
  | zero =>
    change f = 0 at hf
    change cochainMap 0 f = 0
    rw [hf, map_zero]
  | succ q =>
    obtain ⟨g, rfl⟩ := hf
    exact ⟨cochainMap q g, hMap q g⟩

/-- Restrict a degreewise chain map to the existing horizontal cycle modules. -/
def mapCycles (q : ℕ) : ZM q →ₗ[K] ZN q :=
  (cochainMap q).restrict
    (map_mem_cycles H σ ρ τ hσ hρ hτ hι hκ cochainMap hMap q)

@[simp] theorem mapCycles_val (q : ℕ) (f : ZM q) :
    (mapCycles H σ ρ τ hσ hρ hτ hι hκ cochainMap hMap q f).val =
      cochainMap q f.val := rfl

/-- The same restricted map preserves boundaries inside cycles. -/
theorem mapCycles_mem_boundariesInCycles (q : ℕ) (f : ZM q) (hf : f ∈ BZM q) :
    mapCycles H σ ρ τ hσ hρ hτ hι hκ cochainMap hMap q f ∈ BZN q := by
  apply (mem_boundariesInCycles H σ τ hσ hτ hκ).mpr
  exact map_mem_boundaries H σ ρ τ hσ hρ hτ hι hκ cochainMap hMap q f.val
    ((mem_boundariesInCycles H σ ρ hσ hρ hι).mp hf)

/-- Descend the cycle map to the existing horizontal cohomology quotients. -/
def mapCohomology (q : ℕ) :
    HorizontalCohomology H σ ρ hσ hρ hι q →ₗ[K]
      HorizontalCohomology H σ τ hσ hτ hκ q :=
  (BZM q).mapQ (BZN q)
    (mapCycles H σ ρ τ hσ hρ hτ hι hκ cochainMap hMap q)
    (mapCycles_mem_boundariesInCycles H σ ρ τ hσ hρ hτ hι hκ cochainMap hMap q)

/-- The induced quotient map is represented by the original cochain map. -/
@[simp] theorem mapCohomology_class (q : ℕ) (f : ZM q) :
    mapCohomology H σ ρ τ hσ hρ hτ hι hκ cochainMap hMap q
        (cohomologyClass H σ ρ hσ hρ hι q f) =
      cohomologyClass H σ τ hσ hτ hκ q
        (mapCycles H σ ρ τ hσ hρ hτ hι hκ cochainMap hMap q f) := rfl

omit hMap

/-- Identity cochain maps restrict to the identity on cycles. -/
@[simp] theorem mapCycles_id (q : ℕ) :
    mapCycles H σ ρ ρ hσ hρ hρ hι hι
        (fun _ => LinearMap.id) (fun _ _ => rfl) q = LinearMap.id := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  rfl

/-- Identity cochain maps induce the identity on the actual quotient. -/
@[simp] theorem mapCohomology_id (q : ℕ) :
    mapCohomology H σ ρ ρ hσ hρ hρ hι hι
        (fun _ => LinearMap.id) (fun _ _ => rfl) q = LinearMap.id := by
  apply LinearMap.ext
  intro z
  obtain ⟨f, rfl⟩ := cohomologyClass_surjective H σ ρ hσ hρ hι q z
  rw [mapCohomology_class, mapCycles_id, LinearMap.id_apply, LinearMap.id_apply]

include hMap

variable (υ : Representation K G P)
variable (hυ : ∀ g x p, υ g ⁅x, p⁆ = ⁅σ g x, υ g p⁆)
variable (hThirdInsertion : ∀ q, ∀ f ∈ Langlands.HorizontalAlternating.submodule H σ υ q,
  ∀ y ∈ H, ∀ x : Fin q → L,
    ⁅y, f x⁆ = ∑ i, f (Function.update x i ⁅y, x i⁆))
variable (secondMap : (q : ℕ) →
  Langlands.HorizontalAlternating.submodule H σ τ q →ₗ[K]
    Langlands.HorizontalAlternating.submodule H σ υ q)
variable (hSecond : ∀ (q : ℕ) (f : Langlands.HorizontalAlternating.submodule H σ τ q),
  differential H σ υ hσ hυ hThirdInsertion q (secondMap q f) =
    secondMap (q + 1) (differential H σ τ hσ hτ hκ q f))

local notation "hComp" => (fun q f => Eq.trans (hSecond q (cochainMap q f))
  (congrArg (secondMap (q + 1)) (hMap q f)))

/-- Restriction to cycles preserves composition of actual cochain maps. -/
theorem mapCycles_comp (q : ℕ) :
    mapCycles H σ ρ υ hσ hρ hυ hι hThirdInsertion
        (fun q => (secondMap q).comp (cochainMap q)) hComp q =
      (mapCycles H σ τ υ hσ hτ hυ hκ hThirdInsertion secondMap hSecond q).comp
        (mapCycles H σ ρ τ hσ hρ hτ hι hκ cochainMap hMap q) := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  rfl

/-- Descent to the actual quotient preserves composition of cochain maps. -/
theorem mapCohomology_comp (q : ℕ) :
    mapCohomology H σ ρ υ hσ hρ hυ hι hThirdInsertion
        (fun q => (secondMap q).comp (cochainMap q)) hComp q =
      (mapCohomology H σ τ υ hσ hτ hυ hκ hThirdInsertion secondMap hSecond q).comp
        (mapCohomology H σ ρ τ hσ hρ hτ hι hκ cochainMap hMap q) := by
  apply LinearMap.ext
  intro z
  obtain ⟨f, rfl⟩ := cohomologyClass_surjective H σ ρ hσ hρ hι q z
  simp only [mapCohomology_class, LinearMap.comp_apply]
  rfl

end Langlands.Cohomology.Lie.Horizontal
