import Langlands.AlgebraicGeometry.Picard.KernelCartierDuality
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Finite locally free Cartier duality over an affine base -/

universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace Langlands.GroupScheme.Cartier

/-- The actual relative character presheaf of a finite locally free
commutative group scheme has a finite locally free representative. Under
this representation, evaluation gives the canonical biduality isomorphism. -/
def FiniteLocallyFreeCartierDualityStatement : Prop :=
  ∀ (R : CommRingCat.{u}) (G : CommGroupScheme (Spec R)),
    IsFinite G.X.hom → Flat G.X.hom → LocallyOfFinitePresentation G.X.hom →
      ∃ (D : CommGroupScheme (Spec R))
        (dual : additivePoints D.toGrp ≅ characters G)
        (bidual : additivePoints G.toGrp ≅ characters D),
        IsFinite D.X.hom ∧ Flat D.X.hom ∧ LocallyOfFinitePresentation D.X.hom ∧
          ∀ (T : Over (Spec R)) (x : T ⟶ G.X) (y : T ⟶ D.X),
            evaluation (bidual.hom.app (op T) (Additive.ofMul x)) y =
              evaluation (dual.hom.app (op T) (Additive.ofMul y)) x

end Langlands.GroupScheme.Cartier
