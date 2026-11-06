import Langlands.Cohomology.Lie.HorizontalCohomologyAction
import Langlands.Representation.Smooth.Transfer.SubquotientProof
import Langlands.Representation.Hecke.IntegratedConvolution

/-! # Smooth actions and Hecke integration on horizontal cohomology -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000

namespace Langlands.Cohomology.Lie.Horizontal

open MeasureTheory

universe ul um ug up

variable {L : Type ul} [LieRing L] [LieAlgebra ℂ L]
variable {M : Type um} [AddCommGroup M] [Module ℂ M]
variable [LieRingModule L M] [LieModule ℂ L M]
variable {G : Type ug} [Group G]
variable {P : Type up} [Group P] [TopologicalSpace P]

variable (H : Submodule ℂ L) (σ : Representation ℂ G L) (ρ : Representation ℂ G M)
variable (hσ : ∀ g x y, σ g ⁅x, y⁆ = ⁅σ g x, σ g y⁆)
variable (hρ : ∀ g x m, ρ g ⁅x, m⁆ = ⁅σ g x, ρ g m⁆)
variable (hι : ∀ q, ∀ f ∈ Langlands.HorizontalAlternating.submodule H σ ρ q,
  ∀ y ∈ H, ∀ x : Fin q → L,
    ⁅y, f x⁆ = ∑ i, f (Function.update x i ⁅y, x i⁆))

local notation "C" => Langlands.HorizontalAlternating.submodule H σ ρ
local notation "Z" => cycles H σ ρ hσ hρ hι
local notation "HC" => HorizontalCohomology H σ ρ hσ hρ hι

local instance (q : ℕ) : AddCommGroup (C q) := Submodule.addCommGroup _
local instance (q : ℕ) : AddCommGroup (Z q) := Submodule.addCommGroup _

variable (action : (q : ℕ) → Representation ℂ P
  (Langlands.HorizontalAlternating.submodule H σ ρ q))
variable (hAction : ∀ (q : ℕ) (p : P)
  (f : Langlands.HorizontalAlternating.submodule H σ ρ q),
  differential H σ ρ hσ hρ hι q (action q p f) =
    action (q + 1) p (differential H σ ρ hσ hρ hι q f))

/-- The actual cycle inclusion is equivariant for the restricted action. -/
def cyclesActionInclusion (q : ℕ) :
    (cyclesRepresentation H σ ρ hσ hρ hι action hAction q).IntertwiningMap
      (action q) where
  toLinearMap := (Z q).subtype
  isIntertwining' _ := LinearMap.ext (fun _ => rfl)

/-- The actual differential is an intertwiner for the supplied chain action. -/
def differentialActionIntertwiner (q : ℕ) :
    (action q).IntertwiningMap (action (q + 1)) where
  toLinearMap := differential H σ ρ hσ hρ hι q
  isIntertwining' p := LinearMap.ext (hAction q p)

variable (hSmooth : ∀ q, Langlands.IsSmooth (action q))

include hSmooth

theorem cyclesRepresentation_isSmooth (q : ℕ) :
    Langlands.IsSmooth (cyclesRepresentation H σ ρ hσ hρ hι action hAction q) :=
  Langlands.isSmooth_of_injective
    (cyclesActionInclusion H σ ρ hσ hρ hι action hAction q)
    Subtype.val_injective (hSmooth q)

theorem cohomologyRepresentation_isSmooth (q : ℕ) :
    Langlands.IsSmooth (cohomologyRepresentation H σ ρ hσ hρ hι action hAction q) :=
  Langlands.isSmooth_of_surjective
    (cohomologyClassIntertwiner H σ ρ hσ hρ hι action hAction q)
    (cohomologyClass_surjective H σ ρ hσ hρ hι q)
    (cyclesRepresentation_isSmooth H σ ρ hσ hρ hι action hAction hSmooth q)

section Hecke

variable [IsTopologicalGroup P] [MeasurableSpace P] [BorelSpace P]
variable (μ : Measure P) [μ.IsHaarMeasure]

/-- Integrate the given action on the original horizontal cochains. -/
def cochainHeckeAction (q : ℕ) : Hecke.HeckeAlgebra μ →ₙₐ[ℂ] Module.End ℂ (C q) :=
  Hecke.heckeAction μ (action q) (hSmooth q)

/-- Integrate its restriction to the actual differential kernel. -/
def cyclesHeckeAction (q : ℕ) : Hecke.HeckeAlgebra μ →ₙₐ[ℂ] Module.End ℂ (Z q) :=
  Hecke.heckeAction μ (cyclesRepresentation H σ ρ hσ hρ hι action hAction q)
    (cyclesRepresentation_isSmooth H σ ρ hσ hρ hι action hAction hSmooth q)

/-- Integrate the induced action on the existing quotient by image boundaries. -/
def cohomologyHeckeAction (q : ℕ) : Hecke.HeckeAlgebra μ →ₙₐ[ℂ] Module.End ℂ (HC q) :=
  Hecke.heckeAction μ (cohomologyRepresentation H σ ρ hσ hρ hι action hAction q)
    (cohomologyRepresentation_isSmooth H σ ρ hσ hρ hι action hAction hSmooth q)

include hAction in
theorem differential_heckeAction (q : ℕ) (h : Hecke.HeckeAlgebra μ) (f : C q) :
    differential H σ ρ hσ hρ hι q (cochainHeckeAction H σ ρ action hSmooth μ q h f) =
      cochainHeckeAction H σ ρ action hSmooth μ (q + 1) h
        (differential H σ ρ hσ hρ hι q f) :=
  Hecke.integratedAction_intertwiner μ (hSmooth q) (hSmooth (q + 1))
    (differentialActionIntertwiner H σ ρ hσ hρ hι action hAction q) h f

theorem cyclesInclusion_heckeAction (q : ℕ) (h : Hecke.HeckeAlgebra μ) (f : Z q) :
    (cyclesActionInclusion H σ ρ hσ hρ hι action hAction q)
        (cyclesHeckeAction H σ ρ hσ hρ hι action hAction hSmooth μ q h f) =
      cochainHeckeAction H σ ρ action hSmooth μ q h
        (cyclesActionInclusion H σ ρ hσ hρ hι action hAction q f) :=
  Hecke.integratedAction_intertwiner μ
    (cyclesRepresentation_isSmooth H σ ρ hσ hρ hι action hAction hSmooth q)
    (hSmooth q) (cyclesActionInclusion H σ ρ hσ hρ hι action hAction q) h f

theorem cohomologyClass_heckeAction (q : ℕ) (h : Hecke.HeckeAlgebra μ) (f : Z q) :
    cohomologyClass H σ ρ hσ hρ hι q
        (cyclesHeckeAction H σ ρ hσ hρ hι action hAction hSmooth μ q h f) =
      cohomologyHeckeAction H σ ρ hσ hρ hι action hAction hSmooth μ q h
        (cohomologyClass H σ ρ hσ hρ hι q f) :=
  Hecke.integratedAction_intertwiner μ
    (cyclesRepresentation_isSmooth H σ ρ hσ hρ hι action hAction hSmooth q)
    (cohomologyRepresentation_isSmooth H σ ρ hσ hρ hι action hAction hSmooth q)
    (cohomologyClassIntertwiner H σ ρ hσ hρ hι action hAction q) h f

end Hecke
end Langlands.Cohomology.Lie.Horizontal
