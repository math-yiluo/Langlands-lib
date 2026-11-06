import Langlands.GroupScheme.ComponentGaloisImage
import Mathlib.FieldTheory.KrullTopology

/-! # Krull continuity of the coefficient action on actual components -/

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme.IdentityComponent

open GaloisPointComparison

/-- For an algebraic algebraically closed extension, the coefficient action on
all actual components is trivial on the fixing subgroup of a finite intermediate
field. Its kernel is open, its finite image projection is continuous, and its
action on the actual component space is jointly continuous. -/
def ComponentGaloisKrullContinuityStatement : Prop :=
  ∀ (k L : Type u) [Field k] [Field L] [Algebra k L] [IsAlgClosed L]
    [Algebra.IsAlgebraic k L]
    (H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [IsAffineHom H.X.hom],
    (∃ E : IntermediateField k L,
      FiniteDimensional k E ∧ E.fixingSubgroup ≤ componentGaloisKernel k L H) ∧
    IsOpen (componentGaloisKernel k L H : Set (L ≃ₐ[k] L)) ∧
    Continuous (componentGaloisProjection k L H) ∧
    Continuous (fun p : (L ≃ₐ[k] L) × AlgebraicallyClosedComponents (baseChanged k L H) =>
      allComponentGaloisAction k L H p.1 p.2)

end Langlands.GroupScheme.IdentityComponent
