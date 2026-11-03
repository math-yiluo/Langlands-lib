import Langlands.GroupScheme.CoordinateKrullDimension
import Langlands.GroupScheme.Rational.MaximalTorusExtension

/-! # Maximal-torus extensions in affine groups locally of finite type -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
local notation "S" => Spec (CommRingCat.of k)

/-- Every closed torus in an affine group locally of finite type over a field
factors through a maximal torus. -/
theorem exists_maximalTorus_extension_of_finiteType
    (G : GroupScheme S) [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {T : CommGroupScheme S} (i : T.toGrp ⟶ G)
    (hT : IsTorus T.toGrp) (hi : IsClosedSubgroup i) :
    ∃ (M : CommGroupScheme S) (j : M.toGrp ⟶ G), IsMaximalTorus j ∧
      ∃ f : T.toGrp ⟶ M.toGrp, f ≫ j = i := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : FiniteRingKrullDim Γ(G.X.left, ⊤) := globalCoordinates_finiteRingKrullDim G
  exact exists_maximalTorus_extension_of_finiteRingKrullDim G i hT hi

/-- A chosen maximal torus containing a given closed torus, with no separate
coordinate-dimension hypothesis. -/
def maximalTorusExtensionOfFiniteType
    (G : GroupScheme S) [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {T : CommGroupScheme S} (i : T.toGrp ⟶ G)
    (hT : IsTorus T.toGrp) (hi : IsClosedSubgroup i) :
    Σ M : CommGroupScheme S, {j : M.toGrp ⟶ G // IsMaximalTorus j ∧
      ∃ f : T.toGrp ⟶ M.toGrp, f ≫ j = i} :=
  let h := exists_maximalTorus_extension_of_finiteType G i hT hi
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec⟩

end Langlands.GroupScheme
