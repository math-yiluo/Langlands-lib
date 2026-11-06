import Langlands.Cohomology.Lie.HorizontalCohomologyHecke
import Langlands.Cohomology.Lie.HorizontalCohomologyEquivalence

/-! # Original quotient equivalences commute with Hecke integration -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000

namespace Langlands.Cohomology.Lie.Horizontal

universe v w w' ug up

variable {L : Type v} [LieRing L] [LieAlgebra ℂ L]
variable {M : Type w} [AddCommGroup M] [Module ℂ M]
variable [LieRingModule L M] [LieModule ℂ L M]
variable {N : Type w'} [AddCommGroup N] [Module ℂ N]
variable [LieRingModule L N] [LieModule ℂ L N]
variable {G : Type ug} [Group G] {P : Type up} [Group P] [TopologicalSpace P]

variable (H : Submodule ℂ L) (σ : Representation ℂ G L)
variable (ρ : Representation ℂ G M) (τ : Representation ℂ G N)
variable (hσ : ∀ g x y, σ g ⁅x, y⁆ = ⁅σ g x, σ g y⁆)
variable (hρ : ∀ g x m, ρ g ⁅x, m⁆ = ⁅σ g x, ρ g m⁆)
variable (hτ : ∀ g x n, τ g ⁅x, n⁆ = ⁅σ g x, τ g n⁆)
variable (hι : ∀ q, ∀ f ∈ Langlands.HorizontalAlternating.submodule H σ ρ q,
  ∀ y ∈ H, ∀ x : Fin q → L,
    ⁅y, f x⁆ = ∑ i, f (Function.update x i ⁅y, x i⁆))
variable (hκ : ∀ q, ∀ f ∈ Langlands.HorizontalAlternating.submodule H σ τ q,
  ∀ y ∈ H, ∀ x : Fin q → L,
    ⁅y, f x⁆ = ∑ i, f (Function.update x i ⁅y, x i⁆))

local instance heckeEquivalenceSourceCochainGroup (q : ℕ) :
    AddCommGroup (Langlands.HorizontalAlternating.submodule H σ ρ q) :=
  Submodule.addCommGroup _
local instance heckeEquivalenceTargetCochainGroup (q : ℕ) :
    AddCommGroup (Langlands.HorizontalAlternating.submodule H σ τ q) :=
  Submodule.addCommGroup _
local instance heckeEquivalenceSourceCycleGroup (q : ℕ) :
    AddCommGroup (cycles H σ ρ hσ hρ hι q) := Submodule.addCommGroup _
local instance heckeEquivalenceTargetCycleGroup (q : ℕ) :
    AddCommGroup (cycles H σ τ hσ hτ hκ q) := Submodule.addCommGroup _

variable (actionM : (q : ℕ) → Representation ℂ P
  (Langlands.HorizontalAlternating.submodule H σ ρ q))
variable (actionN : (q : ℕ) → Representation ℂ P
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

variable (hSmoothM : ∀ q, Langlands.IsSmooth (actionM q))
variable (hSmoothN : ∀ q, Langlands.IsSmooth (actionN q))

variable [IsTopologicalGroup P] [MeasurableSpace P] [BorelSpace P]
variable (μ : MeasureTheory.Measure P) [μ.IsHaarMeasure]

/-- The original chain equivalence on quotient cohomology commutes with integration. -/
theorem equivCohomology_heckeAction (q : ℕ) (h : Hecke.HeckeAlgebra μ)
    (f : HorizontalCohomology H σ ρ hσ hρ hι q) :
    equivCohomology H σ ρ τ hσ hρ hτ hι hκ
        actionM actionN hActionM hActionN cochainEquiv hEquiv q
        (cohomologyHeckeAction H σ ρ hσ hρ hι actionM hActionM hSmoothM μ q h f) =
      cohomologyHeckeAction H σ τ hσ hτ hκ actionN hActionN hSmoothN μ q h
        (equivCohomology H σ ρ τ hσ hρ hτ hι hκ
          actionM actionN hActionM hActionN cochainEquiv hEquiv q f) :=
  Hecke.integratedAction_intertwiner μ
    (cohomologyRepresentation_isSmooth H σ ρ hσ hρ hι actionM hActionM hSmoothM q)
    (cohomologyRepresentation_isSmooth H σ τ hσ hτ hκ actionN hActionN hSmoothN q)
    (equivCohomology H σ ρ τ hσ hρ hτ hι hκ
      actionM actionN hActionM hActionN cochainEquiv hEquiv q).toIntertwiningMap h f

end Langlands.Cohomology.Lie.Horizontal
