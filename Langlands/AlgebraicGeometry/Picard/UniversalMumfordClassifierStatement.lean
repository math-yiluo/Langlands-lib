import Langlands.AlgebraicGeometry.Picard.RelativePicardZero
import Langlands.AlgebraicGeometry.Picard.UniversalFamilyTriviality
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # A Mumford classifier on a universal rigidified parameter -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- For a universal rigidified pair `(P, L)` of an abelian scheme `A` over an arbitrary base `S`,
there is a morphism `Ψ : A ×_S P ⟶ P` over `S` sending the unit section of the base change
`A_P` to the trivial parameter, such that for every `p : T ⟶ P` the pulled-back family is
geometrically Picard zero exactly when `Ψ` sends every geometric point of `A_P` lying over a
geometric point `t` of `T` (through `p`) to the trivial parameter at `t`. -/
def UniversalMumfordClassifierStatement : Prop :=
  ∀ (S : Scheme.{u}) (A : AbelianScheme S) (P : Over S) (L : RigidifiedFamily A P)
    (hL : RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A) (unitSection_comp A) L),
    ∃ Ψ : ((baseChange P.hom).obj A).X.left ⟶ P.left,
      Ψ ≫ P.hom = ((baseChange P.hom).obj A).X.hom ≫ P.hom ∧
      unitSection ((baseChange P.hom).obj A) ≫ Ψ =
        P.hom ≫ (RigidifiedLineBundle.trivialParameter A.X.hom (unitSection A)
          (unitSection_comp A) L hL).left ∧
      ∀ (T : Over S) (p : T ⟶ P),
        (IsPicardZeroFamily A
            ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
              (unitSection_comp A) p).obj L) ↔
          ∀ (K : Type u) [Field K] [IsAlgClosed K]
            (t : Spec (CommRingCat.of K) ⟶ T.left)
            (y : Spec (CommRingCat.of K) ⟶ ((baseChange P.hom).obj A).X.left),
            y ≫ ((baseChange P.hom).obj A).X.hom = t ≫ p.left →
              y ≫ Ψ = t ≫ T.hom ≫ (RigidifiedLineBundle.trivialParameter A.X.hom
                (unitSection A) (unitSection_comp A) L hL).left)

end Langlands.AbelianScheme
