import Langlands.AbelianScheme.Basic
import Langlands.GroupScheme.Cartier.Restriction
import Langlands.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Yoneda

/-! # Relative integral endomorphism representability over a noetherian affine base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- The affine-base, H-projective specialization of Kottwitz's relative endomorphism
representability assertion, on all locally noetherian schemes over the base. -/
def RelativeEndomorphismRepresentabilityStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (A : Langlands.AbelianScheme (Spec (CommRingCat.of R))),
    Langlands.AlgebraicGeometry.IsHProjective A.X.hom →
    let ι := ObjectProperty.ι
      (fun T : Over (Spec (CommRingCat.of R)) => IsLocallyNoetherian T.left)
    ∃ (E : Over (Spec (CommRingCat.of R))),
      IsLocallyNoetherian E.left ∧
      Nonempty
        ((ι.op ⋙
            Langlands.GroupScheme.Cartier.relativeHomFunctor
              A.toCommGroupScheme A.toCommGroupScheme ⋙ forget AddCommGrpCat.{u}) ≅
          (ι.op ⋙ yoneda.obj E)) ∧
      ∃ (I : Type u) (P : I → Over (Spec (CommRingCat.of R))),
        (∀ i, Langlands.AlgebraicGeometry.IsHProjective (P i).hom) ∧
        Nonempty (E ≅ Over.mk (Sigma.desc (fun i => (P i).hom)))

end Langlands.AbelianScheme
