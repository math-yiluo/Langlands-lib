import Langlands.Cohomology.Lie.HorizontalCohomologyHecke
import Langlands.Cohomology.Lie.HorizontalCohomologyIntertwinerLaws
import Langlands.Representation.Hecke.IntertwinerLaws

/-! # Original horizontal quotient maps for the integrated Hecke actions -/

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

local instance heckeTransportSourceCochainGroup (q : ℕ) :
    AddCommGroup (Langlands.HorizontalAlternating.submodule H σ ρ q) :=
  Submodule.addCommGroup _
local instance heckeTransportTargetCochainGroup (q : ℕ) :
    AddCommGroup (Langlands.HorizontalAlternating.submodule H σ τ q) :=
  Submodule.addCommGroup _
local instance heckeTransportSourceCycleGroup (q : ℕ) :
    AddCommGroup (cycles H σ ρ hσ hρ hι q) := Submodule.addCommGroup _
local instance heckeTransportTargetCycleGroup (q : ℕ) :
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

variable (cochainMap : (q : ℕ) → (actionM q).IntertwiningMap (actionN q))
variable (hMap : ∀ (q : ℕ) (f : Langlands.HorizontalAlternating.submodule H σ ρ q),
  differential H σ τ hσ hτ hκ q (cochainMap q f) =
    cochainMap (q + 1) (differential H σ ρ hσ hρ hι q f))
variable (hSmoothM : ∀ q, Langlands.IsSmooth (actionM q))
variable (hSmoothN : ∀ q, Langlands.IsSmooth (actionN q))
variable [IsTopologicalGroup P] [MeasurableSpace P] [BorelSpace P]
variable (μ : MeasureTheory.Measure P) [μ.IsHaarMeasure]

/-- Integrate the original descended chain map, retaining the existing quotient. -/
def mapCohomologyHeckeIntertwiner (q : ℕ) :
    Algebra.LinearIntertwiner
      (cohomologyHeckeAction H σ ρ hσ hρ hι actionM hActionM hSmoothM μ q)
      (cohomologyHeckeAction H σ τ hσ hτ hκ actionN hActionN hSmoothN μ q) :=
  Hecke.heckeActionIntertwiner μ
    (cohomologyRepresentation_isSmooth H σ ρ hσ hρ hι actionM hActionM hSmoothM q)
    (cohomologyRepresentation_isSmooth H σ τ hσ hτ hκ actionN hActionN hSmoothN q)
    (mapCohomologyIntertwiner H σ ρ τ hσ hρ hτ hι hκ
      actionM actionN hActionM hActionN cochainMap hMap q)

/-- Integration does not change the original quotient linear map. -/
theorem mapCohomologyHeckeIntertwiner_toLinearMap (q : ℕ) :
    (mapCohomologyHeckeIntertwiner H σ ρ τ hσ hρ hτ hι hκ
      actionM actionN hActionM hActionN cochainMap hMap hSmoothM hSmoothN μ q).toLinearMap =
    (mapCohomologyIntertwiner H σ ρ τ hσ hρ hτ hι hκ
      actionM actionN hActionM hActionN cochainMap hMap q).toLinearMap := rfl

/-- The integrated map sends a class to the class of its transported cycle. -/
theorem mapCohomologyHeckeIntertwiner_class (q : ℕ) (f : cycles H σ ρ hσ hρ hι q) :
    mapCohomologyHeckeIntertwiner H σ ρ τ hσ hρ hτ hι hκ
        actionM actionN hActionM hActionN cochainMap hMap hSmoothM hSmoothN μ q
        (cohomologyClass H σ ρ hσ hρ hι q f) =
      cohomologyClass H σ τ hσ hτ hκ q
        (mapCyclesIntertwiner H σ ρ τ hσ hρ hτ hι hκ
          actionM actionN hActionM hActionN cochainMap hMap q f) := rfl

/-- A cochain identity law passes to the integrated original quotient map. -/
abbrev mapCohomologyHeckeIntertwiner_id_of_eq
    (selfMap : (q : ℕ) → (actionM q).IntertwiningMap (actionM q))
    (hSelf : ∀ (q : ℕ) (f : Langlands.HorizontalAlternating.submodule H σ ρ q),
      differential H σ ρ hσ hρ hι q (selfMap q f) =
        selfMap (q + 1) (differential H σ ρ hσ hρ hι q f))
    (hEq : ∀ q, selfMap q = Representation.IntertwiningMap.id (actionM q)) (q : ℕ) :=
  Hecke.heckeActionIntertwiner_id_of_eq μ
    (cohomologyRepresentation_isSmooth H σ ρ hσ hρ hι actionM hActionM hSmoothM q)
    (mapCohomologyIntertwiner H σ ρ ρ hσ hρ hρ hι hι
      actionM actionM hActionM hActionM selfMap hSelf q)
    (mapCohomologyIntertwiner_id_of_eq H σ ρ hσ hρ hι actionM hActionM
      selfMap hSelf hEq q)

universe w''
variable {V : Type w''} [AddCommGroup V] [Module ℂ V]
variable [LieRingModule L V] [LieModule ℂ L V]
variable (υ : Representation ℂ G V)
variable (hυ : ∀ g x v, υ g ⁅x, v⁆ = ⁅σ g x, υ g v⁆)
variable (hThirdInsertion : ∀ q, ∀ f ∈ Langlands.HorizontalAlternating.submodule H σ υ q,
  ∀ y ∈ H, ∀ x : Fin q → L,
    ⁅y, f x⁆ = ∑ i, f (Function.update x i ⁅y, x i⁆))
local instance heckeTransportThirdCochainGroup (q : ℕ) :
    AddCommGroup (Langlands.HorizontalAlternating.submodule H σ υ q) :=
  Submodule.addCommGroup _
local instance heckeTransportThirdCycleGroup (q : ℕ) :
    AddCommGroup (cycles H σ υ hσ hυ hThirdInsertion q) := Submodule.addCommGroup _
variable (actionV : (q : ℕ) → Representation ℂ P
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
variable (hSmoothV : ∀ q, Langlands.IsSmooth (actionV q))

/-- A cochain composition law passes to the integrated original quotient maps. -/
abbrev mapCohomologyHeckeIntertwiner_comp_of_eq (q : ℕ) :=
  Hecke.heckeActionIntertwiner_comp_of_eq μ
    (cohomologyRepresentation_isSmooth H σ ρ hσ hρ hι actionM hActionM hSmoothM q)
    (cohomologyRepresentation_isSmooth H σ τ hσ hτ hκ actionN hActionN hSmoothN q)
    (cohomologyRepresentation_isSmooth H σ υ hσ hυ hThirdInsertion
      actionV hActionV hSmoothV q)
    (mapCohomologyIntertwiner H σ ρ τ hσ hρ hτ hι hκ
      actionM actionN hActionM hActionN cochainMap hMap q)
    (mapCohomologyIntertwiner H σ τ υ hσ hτ hυ hκ hThirdInsertion
      actionN actionV hActionN hActionV secondMap hSecond q)
    (mapCohomologyIntertwiner H σ ρ υ hσ hρ hυ hι hThirdInsertion
      actionM actionV hActionM hActionV combinedMap hCombined q)
    (mapCohomologyIntertwiner_comp_of_eq H σ ρ τ hσ hρ hτ hι hκ
      actionM actionN hActionM hActionN cochainMap hMap υ hυ hThirdInsertion
      actionV hActionV secondMap hSecond combinedMap hCombined hEq q)

end Langlands.Cohomology.Lie.Horizontal
