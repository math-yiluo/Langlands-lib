import Langlands.Shimura.Coefficients.Algebraic

/-! # Continuity target for the actual algebraic coefficient action -/

universe u

namespace Langlands.Shimura.Coefficients

open scoped TensorProduct

/-- Naturality of a finite-dimensional algebraic representation forces
continuous orbit maps on points over a topological commutative algebra.
Continuity is a conclusion, with the module topology explicitly selected. -/
def AlgebraicOrbitContinuityStatement : Prop :=
  ∀ (K A W : Type u) [Field K] [Ring A] [Algebra K A]
    [Module.Finite K A] [AddCommGroup W] [Module K W] [Module.Finite K W]
    (σ : AlgebraInvolution K A) (ρ : σ.AlgebraicRepresentation W)
    (S : Type u) [CommRing S] [Algebra K S]
    [TopologicalSpace S] [IsTopologicalRing S],
    letI : TopologicalSpace (S ⊗[K] W) := moduleTopology S (S ⊗[K] W)
    ∀ x : S ⊗[K] W,
      Continuous (fun g : σ.Points S => ρ.act S g x)

end Langlands.Shimura.Coefficients
