import Langlands.Representation.Finite.Virtual
import Mathlib.LinearAlgebra.Pi

/-!
# Finite degree-zero Brauer induction

The target is an equality of integer submodules of the genuine split
representation group. It uses actual subgroup induction and scalar rank-one
representations, and assumes none of the asserted generation conclusion.
-/

noncomputable section

namespace Langlands.FiniteRep

universe uG

/-- The complex-valued virtual degree, obtained by evaluating the trace character
at the group identity. -/
def virtualDegree (G : Type uG) [Group G] : VirtualRep ℂ G →ₗ[ℤ] ℂ :=
  (LinearMap.proj (1 : G)).comp (virtualCharacter (k := ℂ) (G := G))

/-- The integer submodule of genuine virtual representations of degree zero. -/
def degreeZeroVirtualReps (G : Type uG) [Group G] :
    Submodule ℤ (VirtualRep ℂ G) :=
  LinearMap.ker (virtualDegree G)

/-- Genuine subgroup inductions of differences of two actual rank-one classes. -/
def degreeZeroBrauerGenerators (G : Type uG) [Group G] [Fintype G] :
    Set (VirtualRep ℂ G) :=
  {x | ∃ (S : Subgroup G) (χ χ' : S →* ℂˣ),
    x = virtualInduce S
      (ofClass (classOf (oneDimensional χ)) -
       ofClass (classOf (oneDimensional χ')))}

/-- The integral span of all induced rank-one differences in the split group. -/
def degreeZeroBrauerSpan (G : Type uG) [Group G] [Fintype G] :
    Submodule ℤ (VirtualRep ℂ G) :=
  Submodule.span ℤ (degreeZeroBrauerGenerators G)

/-- Deligne's finite degree-zero Brauer conclusion, allowing all subgroups:
induced rank-one differences integrally generate exactly the degree-zero kernel. -/
def FiniteDegreeZeroBrauerStatement (G : Type uG) [Group G] [Fintype G] : Prop :=
  degreeZeroBrauerSpan G = degreeZeroVirtualReps G

end Langlands.FiniteRep
