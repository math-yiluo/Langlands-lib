import Langlands.GroupScheme.SchemeAction
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Orbit maps onto reduced homogeneous schemes are faithfully flat -/

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over an algebraically closed field `k`, let `G` be a group scheme of finite type acting on a
reduced scheme `O` locally of finite type, and let `x` be a rational point of `O`. If every
rational point of `O` is `g • x` for a rational point `g` of `G`, then the orbit map
`g ↦ g • x`, `G ⟶ O`, is flat, surjective and quasi-compact. -/
def OrbitMapFaithfullyFlatStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    (O : Over (Spec (CommRingCat.of k))) [IsReduced O.left] [LocallyOfFiniteType O.hom]
    (a : SchemeAction G O) (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ O),
    (∀ y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ O,
      ∃ g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X, a.act g x = y) →
    Flat (a.act (𝟙 G.X) (toUnit G.X ≫ x)).left ∧
      Surjective (a.act (𝟙 G.X) (toUnit G.X ≫ x)).left ∧
      QuasiCompact (a.act (𝟙 G.X) (toUnit G.X ≫ x)).left

end Langlands.GroupScheme
