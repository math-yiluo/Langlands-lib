import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Isomorphism detection on quasi-separated test schemes -/

universe u

open CategoryTheory

namespace Langlands.AlgebraicGeometry

open _root_.AlgebraicGeometry

/-- A morphism `f : P ⟶ Q` of schemes over `S` is an isomorphism over `S`
whenever postcomposition with `f` is a bijection `(T ⟶ P) → (T ⟶ Q)` for every
scheme `T` over `S` whose underlying space is quasi-separated. No hypothesis is
placed on `S`, `P` or `Q`. This proposition is a statement target, not a proof
of the criterion. -/
def QuasiSeparatedTestIsoDetectionStatement : Prop :=
  ∀ (S : Scheme.{u}) (P Q : Over S) (f : P ⟶ Q),
    (∀ (T : Over S) [QuasiSeparatedSpace T.left],
      Function.Bijective (fun (g : T ⟶ P) => g ≫ f)) →
    IsIso f

end Langlands.AlgebraicGeometry
