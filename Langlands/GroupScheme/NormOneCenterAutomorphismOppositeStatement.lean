import Langlands.GroupScheme.CenterAutomorphisms
import Langlands.GroupScheme.CentralSimpleNormOne
import Mathlib.Algebra.Algebra.Opposite

/-! # Centre-moving norm-one automorphisms and opposite algebras -/

noncomputable section

universe u

namespace Langlands.GroupScheme

/-- A centre-moving automorphism of the actual norm-one group of a central
simple algebra forces an algebra equivalence with its opposite. -/
def NormOneCenterAutomorphismOppositeStatement : Prop :=
  ∀ (K A : Type u) [Field K] [Ring A] [Algebra K A]
    [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    (f : CentralSimpleUnits.normOne K A ≅ CentralSimpleUnits.normOne K A),
    ¬ AutomorphismFixesCenter f → Nonempty (A ≃ₐ[K] Aᵐᵒᵖ)

end Langlands.GroupScheme
