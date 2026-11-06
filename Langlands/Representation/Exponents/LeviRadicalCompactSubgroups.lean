import Langlands.GroupScheme.Rational.UnipotentCompactSubgroups
import Langlands.Representation.Exponents.ArbitraryParabolic

/-! # The rational points of a unipotent radical are a limit of compact subgroups

For a closed subgroup `P` of an affine group scheme `G` over a nonarchimedean local
field and the unipotent radical `U ⟶ P`, the literal image of `U(F)` in `G(F)` has
every compact subset inside a compact subgroup. Hence its conjugation modulus is
trivial on itself.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {G P U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- The canonical topology on the ambient rational points. -/
local instance radicalPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

/-- The literal rational-point image of a unipotent radical of a closed subgroup is a
limit of compact subgroups. -/
theorem isLimitOfCompactSubgroups_pointImage_radical (p : P ⟶ G) (r : U ⟶ P)
    (hp : IsClosedSubgroup p) (hr : IsUnipotentRadical r) :
    Jacquet.Localization.IsLimitOfCompactSubgroups (pointImage (r ≫ p)) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Smooth U.X.hom := hr.smooth
  exact exists_isCompact_subgroup_superset_range_of_isUnipotent (r ≫ p)
    (hr.isClosedSubgroup.comp hp) hr.isUnipotent

/-- The literal rational-point image of a unipotent radical of a closed subgroup is
unimodular. -/
theorem isUnimodularModulus_pointImage_radical [T2Space k]
    [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
    (p : P ⟶ G) (r : U ⟶ P) (hp : IsClosedSubgroup p) (hr : IsUnipotentRadical r) :
    IsUnimodularModulus (pointImage (r ≫ p))
      (isClosed_pointImage_comp p r hp hr.isClosedSubgroup) :=
  isUnimodularModulus_of_isLimitOfCompactSubgroups _ _
    (isLimitOfCompactSubgroups_pointImage_radical p r hp hr)

end Langlands.Aubert.General.RepresentedParabolic
