import Langlands.Geometry.Building.KPLocalTorusCharacterFiltration
import Langlands.GroupScheme.Torus.SplittingAssembly

/-! # Detection of positive character depths by an induced torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Geometry.Building

/-- Over the maximal unramified extension of a nonarchimedean local field,
a closed embedding of `T` into an induced torus detects the geometric
character congruence of `T` at every positive depth. -/
def TorusInducedEmbeddingPositiveDepthStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (T : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))),
    IsTorus T.toGrp →
    ∃ (S : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F))))
      (hS : IsInducedTorus S) (i : T ⟶ S),
      IsClosedImmersion (CommGroupScheme.groupHom i).hom.hom.left ∧
      ∀ r : ℝ≥0, 0 < r →
        letI : IsAffine S.X.left := SplittingAssembly.isAffine_of_isTorus S.toGrp hS.isTorus
        (localTorusFiltration F S hS.isTorus r).comap
          (rationalPoints.map (CommGroupScheme.groupHom i)) =
            localGeometricCharacterCongruence F T r

end Langlands.Geometry.Building
