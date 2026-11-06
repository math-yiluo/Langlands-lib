import Langlands.Cohomology.Lie.HorizontalCohomologyIntertwiner

/-! # Extensionality of equivariant horizontal cohomology transport -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Cohomology.Lie.Horizontal

universe u v w w' ug up

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

local instance cohomologyCongrSourceCochainGroup (q : ℕ) :
    AddCommGroup (Langlands.HorizontalAlternating.submodule H σ ρ q) :=
  Submodule.addCommGroup _
local instance cohomologyCongrTargetCochainGroup (q : ℕ) :
    AddCommGroup (Langlands.HorizontalAlternating.submodule H σ τ q) :=
  Submodule.addCommGroup _
local instance cohomologyCongrSourceCycleGroup (q : ℕ) :
    AddCommGroup (cycles H σ ρ hσ hρ hι q) := Submodule.addCommGroup _
local instance cohomologyCongrTargetCycleGroup (q : ℕ) :
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


/-- Equal cochain maps induce equal intertwiners on the existing cycles. -/
theorem mapCyclesIntertwiner_congr
    (otherMap : (q : ℕ) → (actionM q).IntertwiningMap (actionN q))
    (hOther : ∀ (q : ℕ) (f : Langlands.HorizontalAlternating.submodule H σ ρ q),
      differential H σ τ hσ hτ hκ q (otherMap q f) =
        otherMap (q + 1) (differential H σ ρ hσ hρ hι q f))
    (hEq : ∀ q, cochainMap q = otherMap q) (q : ℕ) :
    mapCyclesIntertwiner H σ ρ τ hσ hρ hτ hι hκ
        actionM actionN hActionM hActionN cochainMap hMap q =
      mapCyclesIntertwiner H σ ρ τ hσ hρ hτ hι hκ
        actionM actionN hActionM hActionN otherMap hOther q := by
  have h := funext hEq
  subst otherMap
  rfl

/-- Equal cochain maps induce equal intertwiners on the existing quotient. -/
theorem mapCohomologyIntertwiner_congr
    (otherMap : (q : ℕ) → (actionM q).IntertwiningMap (actionN q))
    (hOther : ∀ (q : ℕ) (f : Langlands.HorizontalAlternating.submodule H σ ρ q),
      differential H σ τ hσ hτ hκ q (otherMap q f) =
        otherMap (q + 1) (differential H σ ρ hσ hρ hι q f))
    (hEq : ∀ q, cochainMap q = otherMap q) (q : ℕ) :
    mapCohomologyIntertwiner H σ ρ τ hσ hρ hτ hι hκ
        actionM actionN hActionM hActionN cochainMap hMap q =
      mapCohomologyIntertwiner H σ ρ τ hσ hρ hτ hι hκ
        actionM actionN hActionM hActionN otherMap hOther q := by
  have h := funext hEq
  subst otherMap
  rfl


/-- A cochain family equal to identity restricts to the identity on cycles. -/
theorem mapCyclesIntertwiner_id_of_eq
    (selfMap : (q : ℕ) → (actionM q).IntertwiningMap (actionM q))
    (hSelf : ∀ (q : ℕ) (f : Langlands.HorizontalAlternating.submodule H σ ρ q),
      differential H σ ρ hσ hρ hι q (selfMap q f) =
        selfMap (q + 1) (differential H σ ρ hσ hρ hι q f))
    (hEq : ∀ q, selfMap q = Representation.IntertwiningMap.id (actionM q)) (q : ℕ) :
    mapCyclesIntertwiner H σ ρ ρ hσ hρ hρ hι hι
        actionM actionM hActionM hActionM selfMap hSelf q =
      Representation.IntertwiningMap.id
        (cyclesRepresentation H σ ρ hσ hρ hι actionM hActionM q) := by
  exact (mapCyclesIntertwiner_congr H σ ρ ρ hσ hρ hρ hι hι
    actionM actionM hActionM hActionM selfMap hSelf
    (fun q => Representation.IntertwiningMap.id (actionM q)) (fun _ _ => rfl) hEq q).trans
    (mapCyclesIntertwiner_id H σ ρ hσ hρ hι actionM hActionM q)

/-- A cochain family equal to identity descends to the identity on cohomology. -/
theorem mapCohomologyIntertwiner_id_of_eq
    (selfMap : (q : ℕ) → (actionM q).IntertwiningMap (actionM q))
    (hSelf : ∀ (q : ℕ) (f : Langlands.HorizontalAlternating.submodule H σ ρ q),
      differential H σ ρ hσ hρ hι q (selfMap q f) =
        selfMap (q + 1) (differential H σ ρ hσ hρ hι q f))
    (hEq : ∀ q, selfMap q = Representation.IntertwiningMap.id (actionM q)) (q : ℕ) :
    mapCohomologyIntertwiner H σ ρ ρ hσ hρ hρ hι hι
        actionM actionM hActionM hActionM selfMap hSelf q =
      Representation.IntertwiningMap.id
        (cohomologyRepresentation H σ ρ hσ hρ hι actionM hActionM q) := by
  exact (mapCohomologyIntertwiner_congr H σ ρ ρ hσ hρ hρ hι hι
    actionM actionM hActionM hActionM selfMap hSelf
    (fun q => Representation.IntertwiningMap.id (actionM q)) (fun _ _ => rfl) hEq q).trans
    (mapCohomologyIntertwiner_id H σ ρ hσ hρ hι actionM hActionM q)

universe w''
variable {V : Type w''} [AddCommGroup V] [Module K V]
variable [LieRingModule L V] [LieModule K L V]
variable (υ : Representation K G V)
variable (hυ : ∀ g x v, υ g ⁅x, v⁆ = ⁅σ g x, υ g v⁆)
variable (hThirdInsertion : ∀ q, ∀ f ∈ Langlands.HorizontalAlternating.submodule H σ υ q,
  ∀ y ∈ H, ∀ x : Fin q → L,
    ⁅y, f x⁆ = ∑ i, f (Function.update x i ⁅y, x i⁆))
local instance cohomologyCongrThirdCochainGroup (q : ℕ) :
    AddCommGroup (Langlands.HorizontalAlternating.submodule H σ υ q) :=
  Submodule.addCommGroup _
local instance cohomologyCongrThirdCycleGroup (q : ℕ) :
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
variable (combinedMap : (q : ℕ) → (actionM q).IntertwiningMap (actionV q))
variable (hCombined : ∀ (q : ℕ) (f : Langlands.HorizontalAlternating.submodule H σ ρ q),
  differential H σ υ hσ hυ hThirdInsertion q (combinedMap q f) =
    combinedMap (q + 1) (differential H σ ρ hσ hρ hι q f))
variable (hEq : ∀ q, combinedMap q = (secondMap q).comp (cochainMap q))
local notation "hComp" => (fun q f => Eq.trans (hSecond q (cochainMap q f))
  (congrArg (secondMap (q + 1)) (hMap q f)))

include hEq in
/-- A cochain family equal to a composite restricts to the composite on cycles. -/
theorem mapCyclesIntertwiner_comp_of_eq (q : ℕ) :
    mapCyclesIntertwiner H σ ρ υ hσ hρ hυ hι hThirdInsertion
        actionM actionV hActionM hActionV combinedMap hCombined q =
      (mapCyclesIntertwiner H σ τ υ hσ hτ hυ hκ hThirdInsertion
        actionN actionV hActionN hActionV secondMap hSecond q).comp
      (mapCyclesIntertwiner H σ ρ τ hσ hρ hτ hι hκ
        actionM actionN hActionM hActionN cochainMap hMap q) := by
  exact (mapCyclesIntertwiner_congr H σ ρ υ hσ hρ hυ hι hThirdInsertion
    actionM actionV hActionM hActionV combinedMap hCombined
    (fun q => (secondMap q).comp (cochainMap q)) hComp hEq q).trans
    (mapCyclesIntertwiner_comp H σ ρ τ hσ hρ hτ hι hκ
      actionM actionN hActionM hActionN cochainMap hMap υ hυ hThirdInsertion
      actionV hActionV secondMap hSecond q)

include hEq in
/-- A cochain family equal to a composite descends to the composite on cohomology. -/
theorem mapCohomologyIntertwiner_comp_of_eq (q : ℕ) :
    mapCohomologyIntertwiner H σ ρ υ hσ hρ hυ hι hThirdInsertion
        actionM actionV hActionM hActionV combinedMap hCombined q =
      (mapCohomologyIntertwiner H σ τ υ hσ hτ hυ hκ hThirdInsertion
        actionN actionV hActionN hActionV secondMap hSecond q).comp
      (mapCohomologyIntertwiner H σ ρ τ hσ hρ hτ hι hκ
        actionM actionN hActionM hActionN cochainMap hMap q) := by
  exact (mapCohomologyIntertwiner_congr H σ ρ υ hσ hρ hυ hι hThirdInsertion
    actionM actionV hActionM hActionV combinedMap hCombined
    (fun q => (secondMap q).comp (cochainMap q)) hComp hEq q).trans
    (mapCohomologyIntertwiner_comp H σ ρ τ hσ hρ hτ hι hκ
      actionM actionN hActionM hActionN cochainMap hMap υ hυ hThirdInsertion
      actionV hActionV secondMap hSecond q)

end Langlands.Cohomology.Lie.Horizontal
