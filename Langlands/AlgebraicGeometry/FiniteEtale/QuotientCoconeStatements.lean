import Langlands.AlgebraicGeometry.FiniteEtale.Definitions
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.FieldTheory.IsAlgClosed.Basic

open CategoryTheory CategoryTheory.Limits

universe u

namespace Langlands.AlgebraicGeometry.FiniteEtale

open _root_.AlgebraicGeometry

/-- A quotient cocone in actual finite étale covers whose geometric point maps
are surjective and identify exactly the group orbits. -/
def FiniteGroupQuotientCocone {S : Scheme.{u}} {G : Type u} [Group G]
    (D : SingleObj G ⥤ Cover S) (c : Cocone D) : Prop :=
  Nonempty (IsColimit c) ∧
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
    let q := (pointFunctor s).map (c.ι.app (SingleObj.star G))
    Function.Surjective q ∧
      ∀ x y : Fiber s (D.obj (SingleObj.star G)),
        q x = q y ↔ ∃ g : G, y = (pointFunctor s).map (D.map (SingleObj.toEnd G g)) x

/-- Quotient cocones with the geometric orbit property over affine locally
noetherian bases. -/
def AffineFiniteGroupQuotientCocones : Prop :=
  ∀ (S : Scheme.{u}) [IsAffine S] [IsLocallyNoetherian S]
    (G : Type u) [Group G] [Finite G] (D : SingleObj G ⥤ Cover S),
    ∃ c : Cocone D, FiniteGroupQuotientCocone D c

/-- Quotient cocones with the geometric orbit property over arbitrary locally
noetherian bases. -/
def FiniteGroupQuotientCocones : Prop :=
  ∀ (S : Scheme.{u}) [IsLocallyNoetherian S]
    (G : Type u) [Group G] [Finite G] (D : SingleObj G ⥤ Cover S),
    ∃ c : Cocone D, FiniteGroupQuotientCocone D c

end Langlands.AlgebraicGeometry.FiniteEtale
