import Langlands.AbelianScheme.Basic
import Langlands.GroupScheme.Cartier.Restriction
import Langlands.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Yoneda

/-! # Affine-test relative endomorphism scheme with clopen quasi-compact pieces -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- For every H-projective abelian scheme `A` over a noetherian affine base `Spec R`,
the integral relative endomorphism presheaf of `A`, restricted to affine schemes over
`Spec R`, is represented by a separated, locally finite type, formally unramified scheme
`H` over `Spec R` whose underlying space is covered by pairwise disjoint closed opens,
each quasi-compact over `Spec R`. -/
def AffineHomSchemePiecesStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (A : Langlands.AbelianScheme (Spec (CommRingCat.of R))),
    Langlands.AlgebraicGeometry.IsHProjective A.X.hom →
    let ι := ObjectProperty.ι (fun T : Over (Spec (CommRingCat.of R)) => IsAffine T.left)
    ∃ H : Over (Spec (CommRingCat.of R)),
      IsSeparated H.hom ∧ LocallyOfFiniteType H.hom ∧ FormallyUnramified H.hom ∧
      Nonempty
        ((ι.op ⋙
            Langlands.GroupScheme.Cartier.relativeHomFunctor
              A.toCommGroupScheme A.toCommGroupScheme ⋙ forget AddCommGrpCat.{u}) ≅
          (ι.op ⋙ yoneda.obj H)) ∧
      ∃ (I : Type u) (U : I → H.left.Opens),
        (∀ i, IsClosed (U i : Set H.left)) ∧
        (∀ i, QuasiCompact ((U i).ι ≫ H.hom)) ∧
        Pairwise (Function.onFun Disjoint U) ∧
        (⨆ i, U i) = ⊤

end Langlands.AbelianScheme
