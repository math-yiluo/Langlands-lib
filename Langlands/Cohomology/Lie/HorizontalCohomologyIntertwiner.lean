import Langlands.Cohomology.Lie.HorizontalCohomologyAction
import Langlands.Cohomology.Lie.HorizontalCohomologyTransport

/-! # Equivariant transport on the actual horizontal cohomology quotient -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Cohomology.Lie.Horizontal

universe u v w w' w'' ug up

variable {K : Type u} [Field K] [CharZero K]
variable {L : Type v} [LieRing L] [LieAlgebra K L]
variable {M : Type w} [AddCommGroup M] [Module K M]
variable [LieRingModule L M] [LieModule K L M]
variable {N : Type w'} [AddCommGroup N] [Module K N]
variable [LieRingModule L N] [LieModule K L N]
variable {V : Type w''} [AddCommGroup V] [Module K V]
variable [LieRingModule L V] [LieModule K L V]
variable {G : Type ug} [Group G] {P : Type up} [Monoid P]

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

local instance intertwinerSourceCochainGroup (q : ℕ) :
    AddCommGroup (Langlands.HorizontalAlternating.submodule H σ ρ q) :=
  Submodule.addCommGroup _
local instance intertwinerTargetCochainGroup (q : ℕ) :
    AddCommGroup (Langlands.HorizontalAlternating.submodule H σ τ q) :=
  Submodule.addCommGroup _
local instance intertwinerSourceCycleGroup (q : ℕ) :
    AddCommGroup (cycles H σ ρ hσ hρ hι q) := Submodule.addCommGroup _
local instance intertwinerTargetCycleGroup (q : ℕ) :
    AddCommGroup (cycles H σ τ hσ hτ hκ q) := Submodule.addCommGroup _

variable (actionM : (q : ℕ) → Representation K P
  (Langlands.HorizontalAlternating.submodule H σ ρ q))
variable (actionN : (q : ℕ) → Representation K P
  (Langlands.HorizontalAlternating.submodule H σ τ q))
variable (hActionM : ∀ (q : ℕ) (p : P)
  (f : Langlands.HorizontalAlternating.submodule H σ ρ q),
  differential H σ ρ hσ hρ hι q (actionM q p f) =
    actionM (q + 1) p (differential H σ ρ hσ hρ hι q f))
variable (hActionN : ∀ (q : ℕ) (p : P)
  (f : Langlands.HorizontalAlternating.submodule H σ τ q),
  differential H σ τ hσ hτ hκ q (actionN q p f) =
    actionN (q + 1) p (differential H σ τ hσ hτ hκ q f))
variable (cochainMap : (q : ℕ) → (actionM q).IntertwiningMap (actionN q))
variable (hMap : ∀ (q : ℕ) (f : Langlands.HorizontalAlternating.submodule H σ ρ q),
  differential H σ τ hσ hτ hκ q (cochainMap q f) =
    cochainMap (q + 1) (differential H σ ρ hσ hρ hι q f))

/-- Restriction of the given equivariant chain map to the existing cycles. -/
def mapCyclesIntertwiner (q : ℕ) :
    (cyclesRepresentation H σ ρ hσ hρ hι actionM hActionM q).IntertwiningMap
      (cyclesRepresentation H σ τ hσ hτ hκ actionN hActionN q) where
  toLinearMap := mapCycles H σ ρ τ hσ hρ hτ hι hκ
    (fun q => (cochainMap q).toLinearMap) hMap q
  isIntertwining' p := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining
      (actionM q) (actionN q) (cochainMap q) p f.val

@[simp] theorem mapCyclesIntertwiner_toLinearMap (q : ℕ) :
    (mapCyclesIntertwiner H σ ρ τ hσ hρ hτ hι hκ
      actionM actionN hActionM hActionN cochainMap hMap q).toLinearMap =
    mapCycles H σ ρ τ hσ hρ hτ hι hκ
      (fun q => (cochainMap q).toLinearMap) hMap q := rfl


/-- The restricted intertwiner retains the original transported cochain. -/
@[simp] theorem mapCyclesIntertwiner_val (q : ℕ) (f : cycles H σ ρ hσ hρ hι q) :
    (mapCyclesIntertwiner H σ ρ τ hσ hρ hτ hι hκ
      actionM actionN hActionM hActionN cochainMap hMap q f).val =
    cochainMap q f.val := rfl

/-- Descent of the same equivariant chain map to the existing quotient representations. -/
def mapCohomologyIntertwiner (q : ℕ) :
    (cohomologyRepresentation H σ ρ hσ hρ hι actionM hActionM q).IntertwiningMap
      (cohomologyRepresentation H σ τ hσ hτ hκ actionN hActionN q) where
  toLinearMap := mapCohomology H σ ρ τ hσ hρ hτ hι hκ
    (fun q => (cochainMap q).toLinearMap) hMap q
  isIntertwining' p := by
    apply LinearMap.ext
    intro z
    obtain ⟨f, rfl⟩ := cohomologyClass_surjective H σ ρ hσ hρ hι q z
    simp only [LinearMap.comp_apply, cohomologyRepresentation_class, mapCohomology_class]
    congr 1
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining
      (actionM q) (actionN q) (cochainMap q) p f.val

@[simp] theorem mapCohomologyIntertwiner_toLinearMap (q : ℕ) :
    (mapCohomologyIntertwiner H σ ρ τ hσ hρ hτ hι hκ
      actionM actionN hActionM hActionN cochainMap hMap q).toLinearMap =
    mapCohomology H σ ρ τ hσ hρ hτ hι hκ
      (fun q => (cochainMap q).toLinearMap) hMap q := rfl

/-- The descended intertwiner sends a class to the class of the same transported cycle. -/
@[simp] theorem mapCohomologyIntertwiner_class (q : ℕ)
    (f : cycles H σ ρ hσ hρ hι q) :
    mapCohomologyIntertwiner H σ ρ τ hσ hρ hτ hι hκ
        actionM actionN hActionM hActionN cochainMap hMap q
        (cohomologyClass H σ ρ hσ hρ hι q f) =
      cohomologyClass H σ τ hσ hτ hκ q
        (mapCyclesIntertwiner H σ ρ τ hσ hρ hτ hι hκ
          actionM actionN hActionM hActionN cochainMap hMap q f) := rfl

/-- The actual quotient projection is natural as a bundled intertwiner. -/
theorem mapCohomologyIntertwiner_class_comp (q : ℕ) :
    (mapCohomologyIntertwiner H σ ρ τ hσ hρ hτ hι hκ
        actionM actionN hActionM hActionN cochainMap hMap q).comp
      (cohomologyClassIntertwiner H σ ρ hσ hρ hι actionM hActionM q) =
    (cohomologyClassIntertwiner H σ τ hσ hτ hκ actionN hActionN q).comp
      (mapCyclesIntertwiner H σ ρ τ hσ hρ hτ hι hκ
        actionM actionN hActionM hActionN cochainMap hMap q) := by
  apply Representation.IntertwiningMap.ext
  exact LinearMap.ext (fun _ => rfl)


/-- Identity cochain intertwiners restrict to the identity cycle intertwiner. -/
@[simp] theorem mapCyclesIntertwiner_id (q : ℕ) :
    mapCyclesIntertwiner H σ ρ ρ hσ hρ hρ hι hι
        actionM actionM hActionM hActionM
        (fun q => Representation.IntertwiningMap.id (actionM q)) (fun _ _ => rfl) q =
      Representation.IntertwiningMap.id
        (cyclesRepresentation H σ ρ hσ hρ hι actionM hActionM q) := by
  apply Representation.IntertwiningMap.ext
  exact mapCycles_id H σ ρ hσ hρ hι q

/-- Identity cochain intertwiners induce the identity quotient intertwiner. -/
@[simp] theorem mapCohomologyIntertwiner_id (q : ℕ) :
    mapCohomologyIntertwiner H σ ρ ρ hσ hρ hρ hι hι
        actionM actionM hActionM hActionM
        (fun q => Representation.IntertwiningMap.id (actionM q)) (fun _ _ => rfl) q =
      Representation.IntertwiningMap.id
        (cohomologyRepresentation H σ ρ hσ hρ hι actionM hActionM q) := by
  apply Representation.IntertwiningMap.ext
  exact mapCohomology_id H σ ρ hσ hρ hι q

variable (υ : Representation K G V)
variable (hυ : ∀ g x v, υ g ⁅x, v⁆ = ⁅σ g x, υ g v⁆)
variable (hThirdInsertion : ∀ q, ∀ f ∈ Langlands.HorizontalAlternating.submodule H σ υ q,
  ∀ y ∈ H, ∀ x : Fin q → L,
    ⁅y, f x⁆ = ∑ i, f (Function.update x i ⁅y, x i⁆))

local instance intertwinerThirdCochainGroup (q : ℕ) :
    AddCommGroup (Langlands.HorizontalAlternating.submodule H σ υ q) :=
  Submodule.addCommGroup _
local instance intertwinerThirdCycleGroup (q : ℕ) :
    AddCommGroup (cycles H σ υ hσ hυ hThirdInsertion q) := Submodule.addCommGroup _

variable (actionV : (q : ℕ) → Representation K P
  (Langlands.HorizontalAlternating.submodule H σ υ q))
variable (hActionV : ∀ (q : ℕ) (p : P)
  (f : Langlands.HorizontalAlternating.submodule H σ υ q),
  differential H σ υ hσ hυ hThirdInsertion q (actionV q p f) =
    actionV (q + 1) p (differential H σ υ hσ hυ hThirdInsertion q f))
variable (secondMap : (q : ℕ) → (actionN q).IntertwiningMap (actionV q))
variable (hSecond : ∀ (q : ℕ) (f : Langlands.HorizontalAlternating.submodule H σ τ q),
  differential H σ υ hσ hυ hThirdInsertion q (secondMap q f) =
    secondMap (q + 1) (differential H σ τ hσ hτ hκ q f))

local notation "hComp" => (fun q f => Eq.trans (hSecond q (cochainMap q f))
  (congrArg (secondMap (q + 1)) (hMap q f)))

/-- Restriction to cycles preserves composition of the bundled chain maps. -/
theorem mapCyclesIntertwiner_comp (q : ℕ) :
    mapCyclesIntertwiner H σ ρ υ hσ hρ hυ hι hThirdInsertion
        actionM actionV hActionM hActionV
        (fun q => (secondMap q).comp (cochainMap q)) hComp q =
      (mapCyclesIntertwiner H σ τ υ hσ hτ hυ hκ hThirdInsertion
        actionN actionV hActionN hActionV secondMap hSecond q).comp
      (mapCyclesIntertwiner H σ ρ τ hσ hρ hτ hι hκ
        actionM actionN hActionM hActionN cochainMap hMap q) := by
  apply Representation.IntertwiningMap.ext
  exact mapCycles_comp H σ ρ τ hσ hρ hτ hι hκ
    (fun q => (cochainMap q).toLinearMap) hMap υ hυ hThirdInsertion
    (fun q => (secondMap q).toLinearMap) hSecond q

/-- Descent to the quotient preserves composition of the bundled chain maps. -/
theorem mapCohomologyIntertwiner_comp (q : ℕ) :
    mapCohomologyIntertwiner H σ ρ υ hσ hρ hυ hι hThirdInsertion
        actionM actionV hActionM hActionV
        (fun q => (secondMap q).comp (cochainMap q)) hComp q =
      (mapCohomologyIntertwiner H σ τ υ hσ hτ hυ hκ hThirdInsertion
        actionN actionV hActionN hActionV secondMap hSecond q).comp
      (mapCohomologyIntertwiner H σ ρ τ hσ hρ hτ hι hκ
        actionM actionN hActionM hActionN cochainMap hMap q) := by
  apply Representation.IntertwiningMap.ext
  exact mapCohomology_comp H σ ρ τ hσ hρ hτ hι hκ
    (fun q => (cochainMap q).toLinearMap) hMap υ hυ hThirdInsertion
    (fun q => (secondMap q).toLinearMap) hSecond q

end Langlands.Cohomology.Lie.Horizontal
