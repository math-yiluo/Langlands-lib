import Langlands.Cohomology.Lie.HorizontalCohomologyIntertwiner

/-! # Equivalence transport on the actual horizontal cohomology quotient -/

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

local instance equivalenceSourceCochainGroup (q : ℕ) :
    AddCommGroup (Langlands.HorizontalAlternating.submodule H σ ρ q) :=
  Submodule.addCommGroup _
local instance equivalenceTargetCochainGroup (q : ℕ) :
    AddCommGroup (Langlands.HorizontalAlternating.submodule H σ τ q) :=
  Submodule.addCommGroup _
local instance equivalenceSourceCycleGroup (q : ℕ) :
    AddCommGroup (cycles H σ ρ hσ hρ hι q) := Submodule.addCommGroup _
local instance equivalenceTargetCycleGroup (q : ℕ) :
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

variable (cochainEquiv : (q : ℕ) → (actionM q).Equiv (actionN q))
variable (hEquiv : ∀ (q : ℕ) (f : Langlands.HorizontalAlternating.submodule H σ ρ q),
  differential H σ τ hσ hτ hκ q (cochainEquiv q f) =
    cochainEquiv (q + 1) (differential H σ ρ hσ hρ hι q f))

include hEquiv

/-- Differential compatibility of the inverse follows from the forward equation. -/
theorem differential_cochainEquiv_symm (q : ℕ)
    (f : Langlands.HorizontalAlternating.submodule H σ τ q) :
    differential H σ ρ hσ hρ hι q ((cochainEquiv q).symm f) =
      (cochainEquiv (q + 1)).symm (differential H σ τ hσ hτ hκ q f) := by
  apply (cochainEquiv (q + 1)).toLinearEquiv.injective
  change cochainEquiv (q + 1)
      (differential H σ ρ hσ hρ hι q ((cochainEquiv q).symm f)) =
    cochainEquiv (q + 1)
      ((cochainEquiv (q + 1)).symm (differential H σ τ hσ hτ hκ q f))
  rw [← hEquiv q, Representation.Equiv.apply_symm_apply,
    Representation.Equiv.apply_symm_apply]

local notation "hInverse" =>
  differential_cochainEquiv_symm H σ ρ τ hσ hρ hτ hι hκ
    actionM actionN cochainEquiv hEquiv

/-- An equivariant cochain equivalence restricts to the existing cycle representations. -/
def equivCycles (q : ℕ) :
    (cyclesRepresentation H σ ρ hσ hρ hι actionM hActionM q).Equiv
      (cyclesRepresentation H σ τ hσ hτ hκ actionN hActionN q) where
  toLinearMap := (mapCyclesIntertwiner H σ ρ τ hσ hρ hτ hι hκ
    actionM actionN hActionM hActionN
    (fun q => (cochainEquiv q).toIntertwiningMap) hEquiv q).toLinearMap
  invFun := mapCyclesIntertwiner H σ τ ρ hσ hτ hρ hκ hι
    actionN actionM hActionN hActionM
    (fun q => (cochainEquiv q).symm.toIntertwiningMap) hInverse q
  left_inv f := by
    apply Subtype.ext
    exact (cochainEquiv q).symm_apply_apply f.val
  right_inv f := by
    apply Subtype.ext
    exact (cochainEquiv q).apply_symm_apply f.val
  isIntertwining' := (mapCyclesIntertwiner H σ ρ τ hσ hρ hτ hι hκ
    actionM actionN hActionM hActionN
    (fun q => (cochainEquiv q).toIntertwiningMap) hEquiv q).isIntertwining'

/-- Its underlying intertwiner is exactly the published restricted transport. -/
@[simp] theorem equivCycles_toIntertwiningMap (q : ℕ) :
    (equivCycles H σ ρ τ hσ hρ hτ hι hκ
      actionM actionN hActionM hActionN cochainEquiv hEquiv q).toIntertwiningMap =
    mapCyclesIntertwiner H σ ρ τ hσ hρ hτ hι hκ
      actionM actionN hActionM hActionN
      (fun q => (cochainEquiv q).toIntertwiningMap) hEquiv q := rfl

@[simp] theorem equivCycles_val (q : ℕ) (f : cycles H σ ρ hσ hρ hι q) :
    (equivCycles H σ ρ τ hσ hρ hτ hι hκ
      actionM actionN hActionM hActionN cochainEquiv hEquiv q f).val =
    cochainEquiv q f.val := rfl

/-- The same equivalence descends to the actual image-boundary quotient representations. -/
def equivCohomology (q : ℕ) :
    (cohomologyRepresentation H σ ρ hσ hρ hι actionM hActionM q).Equiv
      (cohomologyRepresentation H σ τ hσ hτ hκ actionN hActionN q) where
  toLinearMap := (mapCohomologyIntertwiner H σ ρ τ hσ hρ hτ hι hκ
    actionM actionN hActionM hActionN
    (fun q => (cochainEquiv q).toIntertwiningMap) hEquiv q).toLinearMap
  invFun := mapCohomologyIntertwiner H σ τ ρ hσ hτ hρ hκ hι
    actionN actionM hActionN hActionM
    (fun q => (cochainEquiv q).symm.toIntertwiningMap) hInverse q
  left_inv z := by
    obtain ⟨f, rfl⟩ := cohomologyClass_surjective H σ ρ hσ hρ hι q z
    change mapCohomology H σ τ ρ hσ hτ hρ hκ hι
        (fun q => (cochainEquiv q).symm.toLinearMap) hInverse q
        (mapCohomology H σ ρ τ hσ hρ hτ hι hκ
          (fun q => (cochainEquiv q).toLinearMap) hEquiv q
          (cohomologyClass H σ ρ hσ hρ hι q f)) =
      cohomologyClass H σ ρ hσ hρ hι q f
    rw [mapCohomology_class, mapCohomology_class]
    congr 1
    apply Subtype.ext
    exact (cochainEquiv q).symm_apply_apply f.val
  right_inv z := by
    obtain ⟨f, rfl⟩ := cohomologyClass_surjective H σ τ hσ hτ hκ q z
    change mapCohomology H σ ρ τ hσ hρ hτ hι hκ
        (fun q => (cochainEquiv q).toLinearMap) hEquiv q
        (mapCohomology H σ τ ρ hσ hτ hρ hκ hι
          (fun q => (cochainEquiv q).symm.toLinearMap) hInverse q
          (cohomologyClass H σ τ hσ hτ hκ q f)) =
      cohomologyClass H σ τ hσ hτ hκ q f
    rw [mapCohomology_class, mapCohomology_class]
    congr 1
    apply Subtype.ext
    exact (cochainEquiv q).apply_symm_apply f.val
  isIntertwining' := (mapCohomologyIntertwiner H σ ρ τ hσ hρ hτ hι hκ
    actionM actionN hActionM hActionN
    (fun q => (cochainEquiv q).toIntertwiningMap) hEquiv q).isIntertwining'

/-- Its underlying intertwiner is exactly the published quotient transport. -/
@[simp] theorem equivCohomology_toIntertwiningMap (q : ℕ) :
    (equivCohomology H σ ρ τ hσ hρ hτ hι hκ
      actionM actionN hActionM hActionN cochainEquiv hEquiv q).toIntertwiningMap =
    mapCohomologyIntertwiner H σ ρ τ hσ hρ hτ hι hκ
      actionM actionN hActionM hActionN
      (fun q => (cochainEquiv q).toIntertwiningMap) hEquiv q := rfl

/-- Forward transport sends the class of a cycle to the class of its transported cycle. -/
@[simp] theorem equivCohomology_class (q : ℕ) (f : cycles H σ ρ hσ hρ hι q) :
    equivCohomology H σ ρ τ hσ hρ hτ hι hκ
        actionM actionN hActionM hActionN cochainEquiv hEquiv q
        (cohomologyClass H σ ρ hσ hρ hι q f) =
      cohomologyClass H σ τ hσ hτ hκ q
        (equivCycles H σ ρ τ hσ hρ hτ hι hκ
          actionM actionN hActionM hActionN cochainEquiv hEquiv q f) := rfl

/-- Inverse transport has the corresponding representative formula. -/
@[simp] theorem equivCohomology_symm_class (q : ℕ) (f : cycles H σ τ hσ hτ hκ q) :
    (equivCohomology H σ ρ τ hσ hρ hτ hι hκ
        actionM actionN hActionM hActionN cochainEquiv hEquiv q).symm
        (cohomologyClass H σ τ hσ hτ hκ q f) =
      cohomologyClass H σ ρ hσ hρ hι q
        ((equivCycles H σ ρ τ hσ hρ hτ hι hκ
          actionM actionN hActionM hActionN cochainEquiv hEquiv q).symm f) := rfl

/-- Transport of the inverse cochain equivalence is the inverse cycle equivalence. -/
@[simp] theorem equivCycles_symm (q : ℕ) :
    (equivCycles H σ ρ τ hσ hρ hτ hι hκ
      actionM actionN hActionM hActionN cochainEquiv hEquiv q).symm =
    equivCycles H σ τ ρ hσ hτ hρ hκ hι
      actionN actionM hActionN hActionM (fun q => (cochainEquiv q).symm) hInverse q := by
  apply Representation.Equiv.ext
  rfl

/-- Transport of the inverse cochain equivalence is the inverse quotient equivalence. -/
@[simp] theorem equivCohomology_symm (q : ℕ) :
    (equivCohomology H σ ρ τ hσ hρ hτ hι hκ
      actionM actionN hActionM hActionN cochainEquiv hEquiv q).symm =
    equivCohomology H σ τ ρ hσ hτ hρ hκ hι
      actionN actionM hActionN hActionM (fun q => (cochainEquiv q).symm) hInverse q := by
  apply Representation.Equiv.ext
  rfl

omit hEquiv

/-- Identity cochain equivalences restrict to identity cycle equivalences. -/
@[simp] theorem equivCycles_refl (q : ℕ) :
    equivCycles H σ ρ ρ hσ hρ hρ hι hι
        actionM actionM hActionM hActionM
        (fun q => Representation.Equiv.refl (actionM q)) (fun _ _ => rfl) q =
      Representation.Equiv.refl
        (cyclesRepresentation H σ ρ hσ hρ hι actionM hActionM q) := by
  apply Representation.Equiv.ext
  funext f
  apply Subtype.ext
  rfl

/-- Identity cochain equivalences induce identity quotient equivalences. -/
@[simp] theorem equivCohomology_refl (q : ℕ) :
    equivCohomology H σ ρ ρ hσ hρ hρ hι hι
        actionM actionM hActionM hActionM
        (fun q => Representation.Equiv.refl (actionM q)) (fun _ _ => rfl) q =
      Representation.Equiv.refl
        (cohomologyRepresentation H σ ρ hσ hρ hι actionM hActionM q) := by
  apply Representation.Equiv.ext
  funext z
  obtain ⟨f, rfl⟩ := cohomologyClass_surjective H σ ρ hσ hρ hι q z
  change mapCohomology H σ ρ ρ hσ hρ hρ hι hι
      (fun _ => LinearMap.id) (fun _ _ => rfl) q
      (cohomologyClass H σ ρ hσ hρ hι q f) =
    cohomologyClass H σ ρ hσ hρ hι q f
  rw [mapCohomology_id]
  rfl

include hEquiv

variable {V : Type w''} [AddCommGroup V] [Module K V]
variable [LieRingModule L V] [LieModule K L V]
variable (υ : Representation K G V)
variable (hυ : ∀ g x v, υ g ⁅x, v⁆ = ⁅σ g x, υ g v⁆)
variable (hThirdInsertion : ∀ q, ∀ f ∈ Langlands.HorizontalAlternating.submodule H σ υ q,
  ∀ y ∈ H, ∀ x : Fin q → L,
    ⁅y, f x⁆ = ∑ i, f (Function.update x i ⁅y, x i⁆))

local instance equivalenceThirdCochainGroup (q : ℕ) :
    AddCommGroup (Langlands.HorizontalAlternating.submodule H σ υ q) :=
  Submodule.addCommGroup _
local instance equivalenceThirdCycleGroup (q : ℕ) :
    AddCommGroup (cycles H σ υ hσ hυ hThirdInsertion q) := Submodule.addCommGroup _

variable (actionV : (q : ℕ) → Representation K P
  (Langlands.HorizontalAlternating.submodule H σ υ q))
variable (hActionV : ∀ (q : ℕ) (p : P)
  (f : Langlands.HorizontalAlternating.submodule H σ υ q),
  differential H σ υ hσ hυ hThirdInsertion q (actionV q p f) =
    actionV (q + 1) p (differential H σ υ hσ hυ hThirdInsertion q f))
variable (secondEquiv : (q : ℕ) → (actionN q).Equiv (actionV q))
variable (hSecond : ∀ (q : ℕ) (f : Langlands.HorizontalAlternating.submodule H σ τ q),
  differential H σ υ hσ hυ hThirdInsertion q (secondEquiv q f) =
    secondEquiv (q + 1) (differential H σ τ hσ hτ hκ q f))

local notation "hComposite" => (fun q f => Eq.trans (hSecond q (cochainEquiv q f))
  (congrArg (secondEquiv (q + 1)) (hEquiv q f)))

/-- Cycle transport preserves composition, with the first equivalence applied first. -/
theorem equivCycles_trans (q : ℕ) :
    equivCycles H σ ρ υ hσ hρ hυ hι hThirdInsertion
        actionM actionV hActionM hActionV
        (fun q => (cochainEquiv q).trans (secondEquiv q)) hComposite q =
      (equivCycles H σ ρ τ hσ hρ hτ hι hκ
        actionM actionN hActionM hActionN cochainEquiv hEquiv q).trans
      (equivCycles H σ τ υ hσ hτ hυ hκ hThirdInsertion
        actionN actionV hActionN hActionV secondEquiv hSecond q) := by
  apply Representation.Equiv.ext
  funext f
  apply Subtype.ext
  rfl

/-- Quotient transport preserves composition in the same order. -/
theorem equivCohomology_trans (q : ℕ) :
    equivCohomology H σ ρ υ hσ hρ hυ hι hThirdInsertion
        actionM actionV hActionM hActionV
        (fun q => (cochainEquiv q).trans (secondEquiv q)) hComposite q =
      (equivCohomology H σ ρ τ hσ hρ hτ hι hκ
        actionM actionN hActionM hActionN cochainEquiv hEquiv q).trans
      (equivCohomology H σ τ υ hσ hτ hυ hκ hThirdInsertion
        actionN actionV hActionN hActionV secondEquiv hSecond q) := by
  apply Representation.Equiv.ext
  funext z
  obtain ⟨f, rfl⟩ := cohomologyClass_surjective H σ ρ hσ hρ hι q z
  simp only [equivCohomology_class, Representation.Equiv.trans_apply]
  congr 1

end Langlands.Cohomology.Lie.Horizontal
