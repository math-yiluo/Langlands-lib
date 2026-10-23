import Langlands.Representation.Shahidi.LocalCoefficientPadic

/-! # Stabilized Jacquet functionals on the actual induced spaces

Restriction of the published scalar stable integral to the actual source and
swapped target of Shahidi induction. Total functionals are constructed only
from a proof that every induced section stabilizes.
-/

noncomputable section

namespace Langlands.Shahidi

open Langlands.Shahidi MeasureTheory HarmonicAnalysis

universe uF uV

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F]
variable (abv : AbsoluteValue F ℝ) (hopen : IsOpenNormOne abv)

variable {m n : ℕ} (s : ℂ)
variable {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
variable (π₁ : Representation ℂ (GeneralLinear (m + 1) F) V₁)
  (π₂ : Representation ℂ (GeneralLinear (n + 1) F) V₂)
variable (ψ : UnitaryAdditiveCharacter F)
  (ℓ₁ : V₁ →ₗ[ℂ] ℂ) (ℓ₂ : V₂ →ₗ[ℂ] ℂ)

section Source

variable (μ : Measure (Matrix (Fin (n + 1)) (Fin (m + 1)) F))

/-- The graph of a total stabilized Jacquet functional on the actual source.
This predicate asserts stabilization of each section, not absolute convergence. -/
def IsSourceJacquetFunctional (Λ : SourceSpace abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ →ₗ[ℂ] ℂ) : Prop :=
  ∀ f, HasJacquetIntegral m n ψ (pairFunctional ℓ₁ ℓ₂) μ (sourceEval abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ f) (Λ f)

/-- Stabilized values uniquely determine a total Jacquet functional. -/
theorem IsSourceJacquetFunctional.unique
    {Λ Λ' : SourceSpace abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ →ₗ[ℂ] ℂ}
    (h : IsSourceJacquetFunctional abv hopen s π₁ π₂ ψ ℓ₁ ℓ₂ μ Λ)
    (h' : IsSourceJacquetFunctional abv hopen s π₁ π₂ ψ ℓ₁ ℓ₂ μ Λ') : Λ = Λ' := by
  ext f
  exact HasJacquetIntegral.unique m n ψ (pairFunctional ℓ₁ ℓ₂) (h f) (h' f)

variable (h : ∃ K : OpenAddSubgroup (Matrix (Fin (n + 1)) (Fin (m + 1)) F),
  IsCompact (K : Set (Matrix (Fin (n + 1)) (Fin (m + 1)) F)))

/-- The actual induced sections whose Jacquet integral stabilizes. -/
def sourceJacquetStableDomain : Submodule ℂ (SourceSpace abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂) :=
  (jacquetStableDomain m n ψ (pairFunctional ℓ₁ ℓ₂) μ h).comap
    (sourceFunction abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂)

@[simp] theorem mem_sourceJacquetStableDomain (f : SourceSpace abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂) :
    f ∈ sourceJacquetStableDomain abv hopen s π₁ π₂ ψ ℓ₁ ℓ₂ μ h ↔
      ∃ z, HasJacquetIntegral m n ψ (pairFunctional ℓ₁ ℓ₂) μ
        (sourceEval abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ f) z := Iff.rfl

/-- The linear stabilized Jacquet functional on its actual induced domain. -/
def sourceJacquetStableFunctional : sourceJacquetStableDomain abv hopen s π₁ π₂ ψ ℓ₁ ℓ₂ μ h →ₗ[ℂ] ℂ :=
  (jacquetStableFunctional m n ψ (pairFunctional ℓ₁ ℓ₂) μ h).comp
    (LinearMap.codRestrict (jacquetStableDomain m n ψ (pairFunctional ℓ₁ ℓ₂) μ h)
      ((sourceFunction abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂).comp (sourceJacquetStableDomain abv hopen s π₁ π₂ ψ ℓ₁ ℓ₂ μ h).subtype)
      (fun f => f.property))

/-- The functional takes the unique stabilized value of the defining integrand. -/
theorem sourceJacquetStableFunctional_spec (f : sourceJacquetStableDomain abv hopen s π₁ π₂ ψ ℓ₁ ℓ₂ μ h) :
    HasJacquetIntegral m n ψ (pairFunctional ℓ₁ ℓ₂) μ
      (sourceEval abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ f.val) (sourceJacquetStableFunctional abv hopen s π₁ π₂ ψ ℓ₁ ℓ₂ μ h f) := by
  exact hasJacquetIntegral_jacquetStableFunctional m n ψ (pairFunctional ℓ₁ ℓ₂) μ h
    ⟨sourceFunction abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ f.val, f.property⟩

/-- Extend to the whole induced space only from a proof that the stable domain
is the whole space. The construction chooses no unsupported integral value. -/
def sourceJacquetFunctional
    (hall : sourceJacquetStableDomain abv hopen s π₁ π₂ ψ ℓ₁ ℓ₂ μ h = ⊤) : SourceSpace abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ →ₗ[ℂ] ℂ :=
  (sourceJacquetStableFunctional abv hopen s π₁ π₂ ψ ℓ₁ ℓ₂ μ h).comp
    (LinearMap.codRestrict (sourceJacquetStableDomain abv hopen s π₁ π₂ ψ ℓ₁ ℓ₂ μ h) LinearMap.id
      (fun f => by rw [hall]; trivial))

/-- The conditional total construction has the required stabilization graph. -/
theorem sourceJacquetFunctional_spec (hall : sourceJacquetStableDomain abv hopen s π₁ π₂ ψ ℓ₁ ℓ₂ μ h = ⊤) :
    IsSourceJacquetFunctional abv hopen s π₁ π₂ ψ ℓ₁ ℓ₂ μ (sourceJacquetFunctional abv hopen s π₁ π₂ ψ ℓ₁ ℓ₂ μ h hall) := by
  intro f
  exact sourceJacquetStableFunctional_spec abv hopen s π₁ π₂ ψ ℓ₁ ℓ₂ μ h ⟨f, by rw [hall]; trivial⟩

/-- Existence of a total linear Jacquet functional is exactly stabilization
on every induced section. -/
theorem exists_isSourceJacquetFunctional_iff :
    (∃ Λ, IsSourceJacquetFunctional abv hopen s π₁ π₂ ψ ℓ₁ ℓ₂ μ Λ) ↔
      sourceJacquetStableDomain abv hopen s π₁ π₂ ψ ℓ₁ ℓ₂ μ h = ⊤ := by
  constructor
  · rintro ⟨Λ, hΛ⟩
    apply top_unique
    intro f _
    exact ⟨Λ f, hΛ f⟩
  · intro hall
    exact ⟨sourceJacquetFunctional abv hopen s π₁ π₂ ψ ℓ₁ ℓ₂ μ h hall, sourceJacquetFunctional_spec abv hopen s π₁ π₂ ψ ℓ₁ ℓ₂ μ h hall⟩

end Source

section Target

variable (μ : Measure (Matrix (Fin (m + 1)) (Fin (n + 1)) F))

/-- The graph of a total stabilized Jacquet functional on the actual target.
This predicate asserts stabilization of each section, not absolute convergence. -/
def IsTargetJacquetFunctional (Λ : TargetSpace abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ →ₗ[ℂ] ℂ) : Prop :=
  ∀ f, HasSwappedJacquetIntegral m n ψ (pairFunctional ℓ₂ ℓ₁) μ (targetEval abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ f) (Λ f)

/-- Stabilized values uniquely determine a total Jacquet functional. -/
theorem IsTargetJacquetFunctional.unique
    {Λ Λ' : TargetSpace abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ →ₗ[ℂ] ℂ}
    (h : IsTargetJacquetFunctional abv hopen s π₁ π₂ ψ ℓ₁ ℓ₂ μ Λ)
    (h' : IsTargetJacquetFunctional abv hopen s π₁ π₂ ψ ℓ₁ ℓ₂ μ Λ') : Λ = Λ' := by
  ext f
  exact HasSwappedJacquetIntegral.unique m n ψ (pairFunctional ℓ₂ ℓ₁) (h f) (h' f)

variable (h : ∃ K : OpenAddSubgroup (Matrix (Fin (m + 1)) (Fin (n + 1)) F),
  IsCompact (K : Set (Matrix (Fin (m + 1)) (Fin (n + 1)) F)))

/-- The actual induced sections whose Jacquet integral stabilizes. -/
def targetJacquetStableDomain : Submodule ℂ (TargetSpace abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂) :=
  (swappedJacquetStableDomain m n ψ (pairFunctional ℓ₂ ℓ₁) μ h).comap
    (targetFunction abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂)

@[simp] theorem mem_targetJacquetStableDomain (f : TargetSpace abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂) :
    f ∈ targetJacquetStableDomain abv hopen s π₁ π₂ ψ ℓ₁ ℓ₂ μ h ↔
      ∃ z, HasSwappedJacquetIntegral m n ψ (pairFunctional ℓ₂ ℓ₁) μ
        (targetEval abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ f) z := Iff.rfl

/-- The linear stabilized Jacquet functional on its actual induced domain. -/
def targetJacquetStableFunctional : targetJacquetStableDomain abv hopen s π₁ π₂ ψ ℓ₁ ℓ₂ μ h →ₗ[ℂ] ℂ :=
  (swappedJacquetStableFunctional m n ψ (pairFunctional ℓ₂ ℓ₁) μ h).comp
    (LinearMap.codRestrict (swappedJacquetStableDomain m n ψ (pairFunctional ℓ₂ ℓ₁) μ h)
      ((targetFunction abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂).comp (targetJacquetStableDomain abv hopen s π₁ π₂ ψ ℓ₁ ℓ₂ μ h).subtype)
      (fun f => f.property))

/-- The functional takes the unique stabilized value of the defining integrand. -/
theorem targetJacquetStableFunctional_spec (f : targetJacquetStableDomain abv hopen s π₁ π₂ ψ ℓ₁ ℓ₂ μ h) :
    HasSwappedJacquetIntegral m n ψ (pairFunctional ℓ₂ ℓ₁) μ
      (targetEval abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ f.val) (targetJacquetStableFunctional abv hopen s π₁ π₂ ψ ℓ₁ ℓ₂ μ h f) := by
  exact hasSwappedJacquetIntegral_swappedJacquetStableFunctional m n ψ (pairFunctional ℓ₂ ℓ₁) μ h
    ⟨targetFunction abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ f.val, f.property⟩

/-- Extend to the whole induced space only from a proof that the stable domain
is the whole space. The construction chooses no unsupported integral value. -/
def targetJacquetFunctional
    (hall : targetJacquetStableDomain abv hopen s π₁ π₂ ψ ℓ₁ ℓ₂ μ h = ⊤) : TargetSpace abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ →ₗ[ℂ] ℂ :=
  (targetJacquetStableFunctional abv hopen s π₁ π₂ ψ ℓ₁ ℓ₂ μ h).comp
    (LinearMap.codRestrict (targetJacquetStableDomain abv hopen s π₁ π₂ ψ ℓ₁ ℓ₂ μ h) LinearMap.id
      (fun f => by rw [hall]; trivial))

/-- The conditional total construction has the required stabilization graph. -/
theorem targetJacquetFunctional_spec (hall : targetJacquetStableDomain abv hopen s π₁ π₂ ψ ℓ₁ ℓ₂ μ h = ⊤) :
    IsTargetJacquetFunctional abv hopen s π₁ π₂ ψ ℓ₁ ℓ₂ μ (targetJacquetFunctional abv hopen s π₁ π₂ ψ ℓ₁ ℓ₂ μ h hall) := by
  intro f
  exact targetJacquetStableFunctional_spec abv hopen s π₁ π₂ ψ ℓ₁ ℓ₂ μ h ⟨f, by rw [hall]; trivial⟩

/-- Existence of a total linear Jacquet functional is exactly stabilization
on every induced section. -/
theorem exists_isTargetJacquetFunctional_iff :
    (∃ Λ, IsTargetJacquetFunctional abv hopen s π₁ π₂ ψ ℓ₁ ℓ₂ μ Λ) ↔
      targetJacquetStableDomain abv hopen s π₁ π₂ ψ ℓ₁ ℓ₂ μ h = ⊤ := by
  constructor
  · rintro ⟨Λ, hΛ⟩
    apply top_unique
    intro f _
    exact ⟨Λ f, hΛ f⟩
  · intro hall
    exact ⟨targetJacquetFunctional abv hopen s π₁ π₂ ψ ℓ₁ ℓ₂ μ h hall, targetJacquetFunctional_spec abv hopen s π₁ π₂ ψ ℓ₁ ℓ₂ μ h hall⟩

end Target

end Langlands.Shahidi

namespace Langlands.PadicField.TopologicalData

open Langlands.Shahidi MeasureTheory HarmonicAnalysis

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

private theorem jacquetTopologicalRing :
    letI := T.topology
    IsTopologicalRing F.Carrier := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  infer_instance

variable [MeasurableSpace F.Carrier]

variable {m n : ℕ} (s : ℂ)
variable {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
variable (π₁ : Representation ℂ (GeneralLinear (m + 1) F.Carrier) V₁)
  (π₂ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V₂)
variable (ψ : letI := T.topology; UnitaryAdditiveCharacter F.Carrier)
  (ℓ₁ : V₁ →ₗ[ℂ] ℂ) (ℓ₂ : V₂ →ₗ[ℂ] ℂ)

section Source

variable (μ : Measure (Matrix (Fin (n + 1)) (Fin (m + 1)) F.Carrier))

/-- The graph of a total stabilized Jacquet functional on the actual source.
This predicate asserts stabilization of each section, not absolute convergence. -/
def IsSourceJacquetFunctional (Λ : T.ShahidiSourceSpace (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ →ₗ[ℂ] ℂ) : Prop :=
  letI := T.topology
  letI := T.jacquetTopologicalRing
  ∀ f, HasJacquetIntegral m n ψ (pairFunctional ℓ₁ ℓ₂) μ (T.shahidiSourceEval (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ f) (Λ f)

/-- Stabilized values uniquely determine a total Jacquet functional. -/
theorem IsSourceJacquetFunctional.unique
    {Λ Λ' : T.ShahidiSourceSpace (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ →ₗ[ℂ] ℂ}
    (h : T.IsSourceJacquetFunctional s π₁ π₂ ψ ℓ₁ ℓ₂ μ Λ)
    (h' : T.IsSourceJacquetFunctional s π₁ π₂ ψ ℓ₁ ℓ₂ μ Λ') : Λ = Λ' := by
  let := T.topology
  let := T.jacquetTopologicalRing
  ext f
  exact HasJacquetIntegral.unique m n ψ (pairFunctional ℓ₁ ℓ₂) (h f) (h' f)

variable (h : letI := T.topology; ∃ K : OpenAddSubgroup (Matrix (Fin (n + 1)) (Fin (m + 1)) F.Carrier),
  IsCompact (K : Set (Matrix (Fin (n + 1)) (Fin (m + 1)) F.Carrier)))

/-- The actual induced sections whose Jacquet integral stabilizes. -/
def shahidiSourceJacquetStableDomain : Submodule ℂ (T.ShahidiSourceSpace (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂) :=
  letI := T.topology
  letI := T.jacquetTopologicalRing
  (jacquetStableDomain m n ψ (pairFunctional ℓ₁ ℓ₂) μ h).comap
    (T.shahidiSourceFunction (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂)

@[simp] theorem mem_shahidiSourceJacquetStableDomain (f : T.ShahidiSourceSpace (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂) :
    f ∈ T.shahidiSourceJacquetStableDomain s π₁ π₂ ψ ℓ₁ ℓ₂ μ h ↔
      letI := T.topology; letI := T.jacquetTopologicalRing; ∃ z, HasJacquetIntegral m n ψ (pairFunctional ℓ₁ ℓ₂) μ
        (T.shahidiSourceEval (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ f) z := Iff.rfl

/-- The linear stabilized Jacquet functional on its actual induced domain. -/
def shahidiSourceJacquetStableFunctional : T.shahidiSourceJacquetStableDomain s π₁ π₂ ψ ℓ₁ ℓ₂ μ h →ₗ[ℂ] ℂ :=
  letI := T.topology
  letI := T.jacquetTopologicalRing
  (jacquetStableFunctional m n ψ (pairFunctional ℓ₁ ℓ₂) μ h).comp
    (LinearMap.codRestrict (jacquetStableDomain m n ψ (pairFunctional ℓ₁ ℓ₂) μ h)
      ((T.shahidiSourceFunction (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂).comp (T.shahidiSourceJacquetStableDomain s π₁ π₂ ψ ℓ₁ ℓ₂ μ h).subtype)
      (fun f => f.property))

/-- The functional takes the unique stabilized value of the defining integrand. -/
theorem shahidiSourceJacquetStableFunctional_spec (f : T.shahidiSourceJacquetStableDomain s π₁ π₂ ψ ℓ₁ ℓ₂ μ h) :
    letI := T.topology; letI := T.jacquetTopologicalRing; HasJacquetIntegral m n ψ (pairFunctional ℓ₁ ℓ₂) μ
      (T.shahidiSourceEval (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ f.val) (T.shahidiSourceJacquetStableFunctional s π₁ π₂ ψ ℓ₁ ℓ₂ μ h f) := by
  let := T.topology
  let := T.jacquetTopologicalRing
  exact hasJacquetIntegral_jacquetStableFunctional m n ψ (pairFunctional ℓ₁ ℓ₂) μ h
    ⟨T.shahidiSourceFunction (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ f.val, f.property⟩

/-- Extend to the whole induced space only from a proof that the stable domain
is the whole space. The construction chooses no unsupported integral value. -/
def shahidiSourceJacquetFunctional
    (hall : T.shahidiSourceJacquetStableDomain s π₁ π₂ ψ ℓ₁ ℓ₂ μ h = ⊤) : T.ShahidiSourceSpace (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ →ₗ[ℂ] ℂ :=
  (T.shahidiSourceJacquetStableFunctional s π₁ π₂ ψ ℓ₁ ℓ₂ μ h).comp
    (LinearMap.codRestrict (T.shahidiSourceJacquetStableDomain s π₁ π₂ ψ ℓ₁ ℓ₂ μ h) LinearMap.id
      (fun f => by rw [hall]; trivial))

/-- The conditional total construction has the required stabilization graph. -/
theorem shahidiSourceJacquetFunctional_spec (hall : T.shahidiSourceJacquetStableDomain s π₁ π₂ ψ ℓ₁ ℓ₂ μ h = ⊤) :
    T.IsSourceJacquetFunctional s π₁ π₂ ψ ℓ₁ ℓ₂ μ (T.shahidiSourceJacquetFunctional s π₁ π₂ ψ ℓ₁ ℓ₂ μ h hall) := by
  let := T.topology
  let := T.jacquetTopologicalRing
  intro f
  exact T.shahidiSourceJacquetStableFunctional_spec s π₁ π₂ ψ ℓ₁ ℓ₂ μ h ⟨f, by rw [hall]; trivial⟩

/-- Existence of a total linear Jacquet functional is exactly stabilization
on every induced section. -/
theorem exists_isSourceJacquetFunctional_iff :
    (∃ Λ, T.IsSourceJacquetFunctional s π₁ π₂ ψ ℓ₁ ℓ₂ μ Λ) ↔
      T.shahidiSourceJacquetStableDomain s π₁ π₂ ψ ℓ₁ ℓ₂ μ h = ⊤ := by
  let := T.topology
  let := T.jacquetTopologicalRing
  constructor
  · rintro ⟨Λ, hΛ⟩
    apply top_unique
    intro f _
    exact ⟨Λ f, hΛ f⟩
  · intro hall
    exact ⟨T.shahidiSourceJacquetFunctional s π₁ π₂ ψ ℓ₁ ℓ₂ μ h hall, T.shahidiSourceJacquetFunctional_spec s π₁ π₂ ψ ℓ₁ ℓ₂ μ h hall⟩

end Source

section Target

variable (μ : Measure (Matrix (Fin (m + 1)) (Fin (n + 1)) F.Carrier))

/-- The graph of a total stabilized Jacquet functional on the actual target.
This predicate asserts stabilization of each section, not absolute convergence. -/
def IsTargetJacquetFunctional (Λ : T.ShahidiTargetSpace (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ →ₗ[ℂ] ℂ) : Prop :=
  letI := T.topology
  letI := T.jacquetTopologicalRing
  ∀ f, HasSwappedJacquetIntegral m n ψ (pairFunctional ℓ₂ ℓ₁) μ (T.shahidiTargetEval (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ f) (Λ f)

/-- Stabilized values uniquely determine a total Jacquet functional. -/
theorem IsTargetJacquetFunctional.unique
    {Λ Λ' : T.ShahidiTargetSpace (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ →ₗ[ℂ] ℂ}
    (h : T.IsTargetJacquetFunctional s π₁ π₂ ψ ℓ₁ ℓ₂ μ Λ)
    (h' : T.IsTargetJacquetFunctional s π₁ π₂ ψ ℓ₁ ℓ₂ μ Λ') : Λ = Λ' := by
  let := T.topology
  let := T.jacquetTopologicalRing
  ext f
  exact HasSwappedJacquetIntegral.unique m n ψ (pairFunctional ℓ₂ ℓ₁) (h f) (h' f)

variable (h : letI := T.topology; ∃ K : OpenAddSubgroup (Matrix (Fin (m + 1)) (Fin (n + 1)) F.Carrier),
  IsCompact (K : Set (Matrix (Fin (m + 1)) (Fin (n + 1)) F.Carrier)))

/-- The actual induced sections whose Jacquet integral stabilizes. -/
def shahidiTargetJacquetStableDomain : Submodule ℂ (T.ShahidiTargetSpace (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂) :=
  letI := T.topology
  letI := T.jacquetTopologicalRing
  (swappedJacquetStableDomain m n ψ (pairFunctional ℓ₂ ℓ₁) μ h).comap
    (T.shahidiTargetFunction (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂)

@[simp] theorem mem_shahidiTargetJacquetStableDomain (f : T.ShahidiTargetSpace (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂) :
    f ∈ T.shahidiTargetJacquetStableDomain s π₁ π₂ ψ ℓ₁ ℓ₂ μ h ↔
      letI := T.topology; letI := T.jacquetTopologicalRing; ∃ z, HasSwappedJacquetIntegral m n ψ (pairFunctional ℓ₂ ℓ₁) μ
        (T.shahidiTargetEval (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ f) z := Iff.rfl

/-- The linear stabilized Jacquet functional on its actual induced domain. -/
def shahidiTargetJacquetStableFunctional : T.shahidiTargetJacquetStableDomain s π₁ π₂ ψ ℓ₁ ℓ₂ μ h →ₗ[ℂ] ℂ :=
  letI := T.topology
  letI := T.jacquetTopologicalRing
  (swappedJacquetStableFunctional m n ψ (pairFunctional ℓ₂ ℓ₁) μ h).comp
    (LinearMap.codRestrict (swappedJacquetStableDomain m n ψ (pairFunctional ℓ₂ ℓ₁) μ h)
      ((T.shahidiTargetFunction (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂).comp (T.shahidiTargetJacquetStableDomain s π₁ π₂ ψ ℓ₁ ℓ₂ μ h).subtype)
      (fun f => f.property))

/-- The functional takes the unique stabilized value of the defining integrand. -/
theorem shahidiTargetJacquetStableFunctional_spec (f : T.shahidiTargetJacquetStableDomain s π₁ π₂ ψ ℓ₁ ℓ₂ μ h) :
    letI := T.topology; letI := T.jacquetTopologicalRing; HasSwappedJacquetIntegral m n ψ (pairFunctional ℓ₂ ℓ₁) μ
      (T.shahidiTargetEval (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ f.val) (T.shahidiTargetJacquetStableFunctional s π₁ π₂ ψ ℓ₁ ℓ₂ μ h f) := by
  let := T.topology
  let := T.jacquetTopologicalRing
  exact hasSwappedJacquetIntegral_swappedJacquetStableFunctional m n ψ (pairFunctional ℓ₂ ℓ₁) μ h
    ⟨T.shahidiTargetFunction (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ f.val, f.property⟩

/-- Extend to the whole induced space only from a proof that the stable domain
is the whole space. The construction chooses no unsupported integral value. -/
def shahidiTargetJacquetFunctional
    (hall : T.shahidiTargetJacquetStableDomain s π₁ π₂ ψ ℓ₁ ℓ₂ μ h = ⊤) : T.ShahidiTargetSpace (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ →ₗ[ℂ] ℂ :=
  (T.shahidiTargetJacquetStableFunctional s π₁ π₂ ψ ℓ₁ ℓ₂ μ h).comp
    (LinearMap.codRestrict (T.shahidiTargetJacquetStableDomain s π₁ π₂ ψ ℓ₁ ℓ₂ μ h) LinearMap.id
      (fun f => by rw [hall]; trivial))

/-- The conditional total construction has the required stabilization graph. -/
theorem shahidiTargetJacquetFunctional_spec (hall : T.shahidiTargetJacquetStableDomain s π₁ π₂ ψ ℓ₁ ℓ₂ μ h = ⊤) :
    T.IsTargetJacquetFunctional s π₁ π₂ ψ ℓ₁ ℓ₂ μ (T.shahidiTargetJacquetFunctional s π₁ π₂ ψ ℓ₁ ℓ₂ μ h hall) := by
  let := T.topology
  let := T.jacquetTopologicalRing
  intro f
  exact T.shahidiTargetJacquetStableFunctional_spec s π₁ π₂ ψ ℓ₁ ℓ₂ μ h ⟨f, by rw [hall]; trivial⟩

/-- Existence of a total linear Jacquet functional is exactly stabilization
on every induced section. -/
theorem exists_isTargetJacquetFunctional_iff :
    (∃ Λ, T.IsTargetJacquetFunctional s π₁ π₂ ψ ℓ₁ ℓ₂ μ Λ) ↔
      T.shahidiTargetJacquetStableDomain s π₁ π₂ ψ ℓ₁ ℓ₂ μ h = ⊤ := by
  let := T.topology
  let := T.jacquetTopologicalRing
  constructor
  · rintro ⟨Λ, hΛ⟩
    apply top_unique
    intro f _
    exact ⟨Λ f, hΛ f⟩
  · intro hall
    exact ⟨T.shahidiTargetJacquetFunctional s π₁ π₂ ψ ℓ₁ ℓ₂ μ h hall, T.shahidiTargetJacquetFunctional_spec s π₁ π₂ ψ ℓ₁ ℓ₂ μ h hall⟩

end Target

end Langlands.PadicField.TopologicalData
