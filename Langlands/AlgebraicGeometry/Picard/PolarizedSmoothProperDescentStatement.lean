import Langlands.AlgebraicGeometry.Picard.PresheafLineBundle
import Langlands.AlgebraicGeometry.Picard.Ample
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Sites.Over

/-! # Polarized smooth proper representability descends along affine étale covers -/

universe u v

open CategoryTheory Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- A big étale sheaf with a coherent actual line bundle is represented by a
smooth proper scheme with ample universal bundle if it has such a
representation after a surjective étale cover between affine bases. -/
def PolarizedSmoothProperEtaleDescentStatement : Prop :=
  ∀ (S U : Scheme.{u}), IsAffine S → IsAffine U →
    ∀ (p : U ⟶ S), Etale p → Surjective p →
      ∀ (F : (Over S)ᵒᵖ ⥤ Type v),
        Presieve.IsSheaf (Scheme.etaleTopology.over S) F →
          ∀ (L : PresheafLineBundle F) (M : Over U)
            (e : ((Over.map p).op ⋙ F).RepresentableBy M),
            Smooth M.hom → IsProper M.hom →
              ((L.baseChange p).universal e).IsAmple →
                ∃ (N : Over S) (e' : F.RepresentableBy N),
                  Smooth N.hom ∧ IsProper N.hom ∧ (L.universal e').IsAmple

end Langlands.AlgebraicGeometry.Picard
