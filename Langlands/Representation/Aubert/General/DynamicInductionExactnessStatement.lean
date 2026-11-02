import Langlands.Representation.Aubert.General.AlternatingOperator
import Langlands.Representation.Aubert.General.DynamicParabolic
import Langlands.AlgebraicGeometry.PointTopology.RationalPoints
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Exactness of the actual dynamic normalized induction

A proposition definition: for the actual rational points `G(F)` of a connected
reductive group over a nonarchimedean local field, with the pinned point
topology, and for every cocharacter `χ`, the actual normalized induction functor
`SmoothRep ℂ Z(χ)(F) ⥤ SmoothRep ℂ G(F)` of the decomposition
`P(χ)(F) = Z(χ)(F) ⋉ U(χ)(F)` sends short exact sequences of finite-length
representations to short exact sequences. The binders are exactly those of
`DynamicInductionFiniteLengthStatement`. Nothing here proves the assertion.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Aubert.General

universe u uV

/-- **Normalized parabolic induction is exact on finite-length sequences**
(Renard VI.1.1 and VI.1.2, restricted to finite-length objects). For every
nonarchimedean local field `F`, every connected reductive `G` over `F` and every
cocharacter `χ`, the actual normalized induction functor of
`P(χ)(F) = Z(χ)(F) ⋉ U(χ)(F)`, with the pinned point topology on `G(F)`, sends
short exact sequences of finite-length smooth complex representations of
`Z(χ)(F)` to short exact sequences. This is a proposition definition, not its
proof. -/
def DynamicInductionExactnessStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
    ∀ [LocallyCompactSpace (RationalPoint F G.X)] [NonarchimedeanGroup (RationalPoint F G.X)]
      (hU : IsClosed ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))) :
        Set (RationalPoint F G.X))),
      SmoothRep.PreservesFiniteLengthShortExact (normalizedInductionFunctor.{u, uV}
        (dynamic_isSemidirectDecomposition χ (Over.mk (𝟙 (Spec (CommRingCat.of F))))) hU)

end Langlands.Aubert.General
