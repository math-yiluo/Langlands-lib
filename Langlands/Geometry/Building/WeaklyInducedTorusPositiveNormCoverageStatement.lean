import Langlands.Geometry.Building.KPLocalTorusCharacterFiltration
import Langlands.Geometry.Building.KPWeaklyInducedTorus
import Langlands.GroupScheme.Torus.SplittingAssembly

/-! # Positive-depth norm coverage for weakly induced tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Geometry.Building

/-- At each positive depth, the standard subgroup of a weakly induced torus
is the image of the standard subgroup of an induced torus under an actual
homomorphism over the maximal unramified extension. -/
def WeaklyInducedTorusPositiveNormCoverageStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (T : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F))))
    (hT : IsTorus T.toGrp),
    IsWeaklyInducedTorus F T →
    ∀ r : ℝ≥0, 0 < r →
      letI : IsAffine T.X.left := SplittingAssembly.isAffine_of_isTorus T.toGrp hT
      ∃ (S : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F))))
        (hS : IsInducedTorus S) (n : S ⟶ T),
        letI : IsAffine S.X.left := SplittingAssembly.isAffine_of_isTorus S.toGrp hS.isTorus
        (localTorusFiltration F S hS.isTorus r).map
          (rationalPoints.map (CommGroupScheme.groupHom n)) =
            localTorusFiltration F T hT r

end Langlands.Geometry.Building
