import Langlands.Representation.Dual.Definitions
import Langlands.Representation.Smooth.SmoothPart.Definitions

/-! # The smooth contragredient

The carrier is the smooth-vector submodule of the full algebraic dual.
-/

noncomputable section

namespace Langlands

universe uR uG uV uW

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW}
variable [CommRing R] [Group G] [TopologicalSpace G]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- Smooth functionals on a representation, as a subtype of its algebraic dual. -/
abbrev SmoothDual (ρ : Representation R G V) := ↥(smoothVectors ρ.dual)

/-- The evaluation pairing with smooth functionals. -/
def smoothDualPairing (ρ : Representation R G V) : SmoothDual ρ →ₗ[R] V →ₗ[R] R :=
  (smoothVectors ρ.dual).subtype

variable [IsTopologicalGroup G]

/-- The contragredient action on the smooth functionals. -/
def smoothContragredient (ρ : Representation R G V) : Representation R G (SmoothDual ρ) :=
  smoothPart ρ.dual

variable {ρ : Representation R G V} {σ : Representation R G W}

/-- Pullback of smooth functionals reverses the direction of intertwiners. -/
def contragredientMap (f : ρ.IntertwiningMap σ) :
    (smoothContragredient σ).IntertwiningMap (smoothContragredient ρ) :=
  smoothMap (dualIntertwining f)

/-- Intertwiners from a representation to its double smooth contragredient. -/
abbrev SmoothBidualMap (ρ : Representation R G V) :=
  ρ.IntertwiningMap (smoothContragredient (V := SmoothDual ρ) (smoothContragredient ρ))

/-- Evaluation into the double smooth contragredient of a smooth representation.
This construction does not assert reflexivity. -/
def smoothBidual (hρ : IsSmooth ρ) : SmoothBidualMap ρ :=
  smoothLift hρ
    ((dualIntertwining (V := SmoothDual ρ) (W := Module.Dual R V)
      (smoothInclusion ρ.dual)).comp (bidualIntertwining ρ))

end Langlands
