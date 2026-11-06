import Langlands.Cohomology.Lie.HorizontalCohomologyIntertwinerLaws

/-! # Commutative squares on actual horizontal cohomology -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 20000

namespace Langlands.Cohomology.Lie.Horizontal

universe u v w w' w'' w''' ug up

/-- A square retains all four original equivariant maps together with their
bundled commutation law. -/
structure IntertwinerSquare
    {K : Type u} [Field K] {P : Type up} [Monoid P]
    {A : Type w} [AddCommGroup A] [Module K A]
    {B : Type w'} [AddCommGroup B] [Module K B]
    {C : Type w''} [AddCommGroup C] [Module K C]
    {D : Type w'''} [AddCommGroup D] [Module K D]
    (α : Representation K P A) (β : Representation K P B)
    (γ : Representation K P C) (δ : Representation K P D) where
  top : α.IntertwiningMap β
  right : β.IntertwiningMap δ
  left : α.IntertwiningMap γ
  bottom : γ.IntertwiningMap δ
  commutes : right.comp top = bottom.comp left

variable {K : Type u} [Field K] [CharZero K]
variable {L : Type v} [LieRing L] [LieAlgebra K L]
variable {M : Type w} [AddCommGroup M] [Module K M]
variable [LieRingModule L M] [LieModule K L M]
variable {N : Type w'} [AddCommGroup N] [Module K N]
variable [LieRingModule L N] [LieModule K L N]
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

local instance squareSourceCochainGroup (q : ℕ) :
    AddCommGroup (Langlands.HorizontalAlternating.submodule H σ ρ q) :=
  Submodule.addCommGroup _
local instance squareTargetCochainGroup (q : ℕ) :
    AddCommGroup (Langlands.HorizontalAlternating.submodule H σ τ q) :=
  Submodule.addCommGroup _
local instance squareSourceCycleGroup (q : ℕ) :
    AddCommGroup (cycles H σ ρ hσ hρ hι q) := Submodule.addCommGroup _
local instance squareTargetCycleGroup (q : ℕ) :
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


variable {V : Type w''} [AddCommGroup V] [Module K V]
variable [LieRingModule L V] [LieModule K L V]
variable (υ : Representation K G V)
variable (hυ : ∀ g x v, υ g ⁅x, v⁆ = ⁅σ g x, υ g v⁆)
variable (hInsertionV : ∀ q, ∀ f ∈ Langlands.HorizontalAlternating.submodule H σ υ q,
  ∀ y ∈ H, ∀ x : Fin q → L,
    ⁅y, f x⁆ = ∑ i, f (Function.update x i ⁅y, x i⁆))
local instance squareThirdCochainGroup (q : ℕ) :
    AddCommGroup (Langlands.HorizontalAlternating.submodule H σ υ q) :=
  Submodule.addCommGroup _
local instance squareThirdCycleGroup (q : ℕ) :
    AddCommGroup (cycles H σ υ hσ hυ hInsertionV q) := Submodule.addCommGroup _
variable (actionV : (q : ℕ) → Representation K P
  (Langlands.HorizontalAlternating.submodule H σ υ q))
variable (hActionV : ∀ (q : ℕ) (p : P)
  (f : Langlands.HorizontalAlternating.submodule H σ υ q),
  differential H σ υ hσ hυ hInsertionV q (actionV q p f) =
    actionV (q + 1) p (differential H σ υ hσ hυ hInsertionV q f))

variable {W : Type w'''} [AddCommGroup W] [Module K W]
variable [LieRingModule L W] [LieModule K L W]
variable (ω : Representation K G W)
variable (hω : ∀ g x v, ω g ⁅x, v⁆ = ⁅σ g x, ω g v⁆)
variable (hInsertionW : ∀ q, ∀ f ∈ Langlands.HorizontalAlternating.submodule H σ ω q,
  ∀ y ∈ H, ∀ x : Fin q → L,
    ⁅y, f x⁆ = ∑ i, f (Function.update x i ⁅y, x i⁆))
local instance squareFourthCochainGroup (q : ℕ) :
    AddCommGroup (Langlands.HorizontalAlternating.submodule H σ ω q) :=
  Submodule.addCommGroup _
local instance squareFourthCycleGroup (q : ℕ) :
    AddCommGroup (cycles H σ ω hσ hω hInsertionW q) := Submodule.addCommGroup _
variable (actionW : (q : ℕ) → Representation K P
  (Langlands.HorizontalAlternating.submodule H σ ω q))
variable (hActionW : ∀ (q : ℕ) (p : P)
  (f : Langlands.HorizontalAlternating.submodule H σ ω q),
  differential H σ ω hσ hω hInsertionW q (actionW q p f) =
    actionW (q + 1) p (differential H σ ω hσ hω hInsertionW q f))

variable (rightMap : (q : ℕ) → (actionN q).IntertwiningMap (actionW q))
variable (hRight : ∀ (q : ℕ) (f : Langlands.HorizontalAlternating.submodule H σ τ q),
  differential H σ ω hσ hω hInsertionW q (rightMap q f) =
    rightMap (q + 1) (differential H σ τ hσ hτ hκ q f))
variable (leftMap : (q : ℕ) → (actionM q).IntertwiningMap (actionV q))
variable (hLeft : ∀ (q : ℕ) (f : Langlands.HorizontalAlternating.submodule H σ ρ q),
  differential H σ υ hσ hυ hInsertionV q (leftMap q f) =
    leftMap (q + 1) (differential H σ ρ hσ hρ hι q f))
variable (bottomMap : (q : ℕ) → (actionV q).IntertwiningMap (actionW q))
variable (hBottom : ∀ (q : ℕ) (f : Langlands.HorizontalAlternating.submodule H σ υ q),
  differential H σ ω hσ hω hInsertionW q (bottomMap q f) =
    bottomMap (q + 1) (differential H σ υ hσ hυ hInsertionV q f))

local notation "topCycles" => mapCyclesIntertwiner H σ ρ τ hσ hρ hτ hι hκ
  actionM actionN hActionM hActionN cochainMap hMap
local notation "rightCycles" => mapCyclesIntertwiner H σ τ ω hσ hτ hω hκ hInsertionW
  actionN actionW hActionN hActionW rightMap hRight
local notation "leftCycles" => mapCyclesIntertwiner H σ ρ υ hσ hρ hυ hι hInsertionV
  actionM actionV hActionM hActionV leftMap hLeft
local notation "bottomCycles" => mapCyclesIntertwiner H σ υ ω hσ hυ hω hInsertionV hInsertionW
  actionV actionW hActionV hActionW bottomMap hBottom

/-- A commuting square of equivariant chain maps restricts to the existing cycles. -/
theorem mapCyclesIntertwiner_square
    (hSquare : ∀ q, (rightMap q).comp (cochainMap q) = (bottomMap q).comp (leftMap q))
    (q : ℕ) :
    (rightCycles q).comp (topCycles q) = (bottomCycles q).comp (leftCycles q) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  exact congrArg (fun A => A f.val) (hSquare q)

local notation "topCohomology" => mapCohomologyIntertwiner H σ ρ τ hσ hρ hτ hι hκ
  actionM actionN hActionM hActionN cochainMap hMap
local notation "rightCohomology" => mapCohomologyIntertwiner H σ τ ω hσ hτ hω hκ hInsertionW
  actionN actionW hActionN hActionW rightMap hRight
local notation "leftCohomology" => mapCohomologyIntertwiner H σ ρ υ hσ hρ hυ hι hInsertionV
  actionM actionV hActionM hActionV leftMap hLeft
local notation "bottomCohomology" => mapCohomologyIntertwiner H σ υ ω hσ hυ hω hInsertionV hInsertionW
  actionV actionW hActionV hActionW bottomMap hBottom

/-- The same commuting square descends to the actual cycle quotients. -/
theorem mapCohomologyIntertwiner_square
    (hSquare : ∀ q, (rightMap q).comp (cochainMap q) = (bottomMap q).comp (leftMap q))
    (q : ℕ) :
    (rightCohomology q).comp (topCohomology q) =
      (bottomCohomology q).comp (leftCohomology q) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  obtain ⟨f, rfl⟩ := cohomologyClass_surjective H σ ρ hσ hρ hι q z
  change rightCohomology q (topCohomology q (cohomologyClass H σ ρ hσ hρ hι q f)) =
    bottomCohomology q (leftCohomology q (cohomologyClass H σ ρ hσ hρ hι q f))
  simp only [mapCohomologyIntertwiner_class]
  apply congrArg (cohomologyClass H σ ω hσ hω hInsertionW q)
  apply Subtype.ext
  exact congrArg (fun A => A f.val) (hSquare q)


/-- Restrict all four edges to the original cycle representations, retaining
their commuting square as bundled data. -/
def mapCyclesIntertwinerSquare
    (hSquare : ∀ q, (rightMap q).comp (cochainMap q) = (bottomMap q).comp (leftMap q))
    (q : ℕ) :
    IntertwinerSquare
      (cyclesRepresentation H σ ρ hσ hρ hι actionM hActionM q)
      (cyclesRepresentation H σ τ hσ hτ hκ actionN hActionN q)
      (cyclesRepresentation H σ υ hσ hυ hInsertionV actionV hActionV q)
      (cyclesRepresentation H σ ω hσ hω hInsertionW actionW hActionW q) where
  top := topCycles q
  right := rightCycles q
  left := leftCycles q
  bottom := bottomCycles q
  commutes := mapCyclesIntertwiner_square H σ ρ τ hσ hρ hτ hι hκ
    actionM actionN hActionM hActionN cochainMap hMap
    υ hυ hInsertionV actionV hActionV ω hω hInsertionW actionW hActionW
    rightMap hRight leftMap hLeft bottomMap hBottom hSquare q

/-- Descend all four edges to the original cycle quotients, retaining their
commuting square as bundled data. -/
def mapCohomologyIntertwinerSquare
    (hSquare : ∀ q, (rightMap q).comp (cochainMap q) = (bottomMap q).comp (leftMap q))
    (q : ℕ) :
    IntertwinerSquare
      (cohomologyRepresentation H σ ρ hσ hρ hι actionM hActionM q)
      (cohomologyRepresentation H σ τ hσ hτ hκ actionN hActionN q)
      (cohomologyRepresentation H σ υ hσ hυ hInsertionV actionV hActionV q)
      (cohomologyRepresentation H σ ω hσ hω hInsertionW actionW hActionW q) where
  top := topCohomology q
  right := rightCohomology q
  left := leftCohomology q
  bottom := bottomCohomology q
  commutes := mapCohomologyIntertwiner_square H σ ρ τ hσ hρ hτ hι hκ
    actionM actionN hActionM hActionN cochainMap hMap
    υ hυ hInsertionV actionV hActionV ω hω hInsertionW actionW hActionW
    rightMap hRight leftMap hLeft bottomMap hBottom hSquare q

end Langlands.Cohomology.Lie.Horizontal
