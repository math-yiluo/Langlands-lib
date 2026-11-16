import Langlands.Geometry.Building.KPLocalMoyPrasadCommutator
import Langlands.Geometry.Building.KPLocalMoyPrasadIntersectionAssembly
import Langlands.Geometry.Building.KPLocalDoubleRootCommutatorStatement
import Langlands.Geometry.Building.KPLocalMoyPrasadDepthZeroStatement
import Langlands.Geometry.Building.KPLocalMoyPrasadPositiveProductProof
import Langlands.Geometry.Building.KPLocalMoyPrasadDepthZeroProof
import Langlands.Geometry.Building.RankOneDoubledInputCoroot
import Langlands.Geometry.Building.QuasiSplitValuedRankOneCoordinatesProof

/-!
# Conditional assembly of the K-level Moy–Prasad group properties

The full S2 conclusion follows from S1, using the published valued rank-one
coordinates, doubled-root reduction, positive-depth product and depth-zero
intersection proofs. This module assembles those inputs; it does not prove S1.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building.MaximalUnramified

namespace BuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} [IsAffineHom H.X.hom]
    (B : BuildingData F H) (hZ : IsTorus B.centralizer.Z)

/-- All eight S2 clauses for fixed building data, with the remaining prerequisite
proofs as explicit arguments. -/
theorem localMoyPrasadGroupProperties_of_estimates
    (hS1 : QuasiSplitLocalTorusFiltrationStatement.{u})
    (hProd : LocalMoyPrasadPositiveProductStatement.{u})
    (hZ2 : B.LocalTorusDoubleRootCommutatorFriendly hZ)
    (hDZa : ∀ (x : B.Apartment) (mu : cocharacterLattice B.S), IsGenericCocharacter B.i mu →
      B.rootGroupSpan (positiveRelativeRoots B.i mu) ⊓ B.moyPrasad hZ x 0 =
        B.rootFiltrationSpan x (positiveRelativeRoots B.i mu) 0)
    (hDZb : ∀ (x : B.Apartment) (ν : V B.S),
      B.pairingLeviSpan ν ⊓ B.moyPrasad hZ x 0 ≤
        B.centralizerTorusImage hZ 0 ⊔ B.rootFiltrationSpan x (B.zeroPairingRoots ν) 0) :
    LocalMoyPrasadNormality B hZ ∧ LocalMoyPrasadEquivariance B hZ ∧
      LocalMoyPrasadCommutator B hZ ∧ LocalMoyPrasadRootIntersection B hZ ∧
      LocalMoyPrasadIwahoriFactorization B hZ ∧ LocalMoyPrasadLeviIntersection B hZ ∧
      LocalMoyPrasadCentralizerIntersection B hZ ∧ LocalMoyPrasadSeparated B hZ := by
  have hZcomm : B.LocalTorusCommutatorFriendly hZ := (hS1 F H B hZ).1
  have hZr : B.LocalTorusRootCompatible hZ := (hS1 F H B hZ).2.1
  exact ⟨B.localMoyPrasadNormality_of_torus_commutator_bounds hZ hZcomm hZ2 hZr,
    B.localMoyPrasadEquivariance_of_torus_commutator_bounds hZ hZcomm hZ2 hZr,
    B.localMoyPrasadCommutator_of_torus_commutator_bounds hZ hZcomm hZ2 hZr,
    B.intersectionClauses_of_statements hZ hS1 hProd hDZa hDZb⟩

end BuildingData

/-- The global S2 proposition, conditional on S1, the product statement, and
the independent doubled-root and depth-zero estimates for every building. -/
theorem localMoyPrasadGroupProperties_of_pointwise_estimates
    (hS1 : QuasiSplitLocalTorusFiltrationStatement.{u})
    (hProd : LocalMoyPrasadPositiveProductStatement.{u})
    (hEstimates : ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F]
      (H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))) [IsAffineHom H.X.hom]
      (B : BuildingData F H) (hZ : IsTorus B.centralizer.Z),
      B.LocalTorusDoubleRootCommutatorFriendly hZ ∧
        (∀ (x : B.Apartment) (mu : cocharacterLattice B.S), IsGenericCocharacter B.i mu →
          B.rootGroupSpan (positiveRelativeRoots B.i mu) ⊓ B.moyPrasad hZ x 0 =
            B.rootFiltrationSpan x (positiveRelativeRoots B.i mu) 0) ∧
        (∀ (x : B.Apartment) (ν : V B.S),
          B.pairingLeviSpan ν ⊓ B.moyPrasad hZ x 0 ≤
            B.centralizerTorusImage hZ 0 ⊔ B.rootFiltrationSpan x (B.zeroPairingRoots ν) 0)) :
    LocalMoyPrasadGroupPropertiesStatement.{u} := by
  intro F _ _ _ _ H _ B hZ
  obtain ⟨hZ2, hDZa, hDZb⟩ := hEstimates F H B hZ
  exact B.localMoyPrasadGroupProperties_of_estimates hZ hS1 hProd hZ2 hDZa hDZb

/-- The four published prerequisite propositions imply the exact global S2 proposition.
This adapter does not supply proofs of those prerequisites. -/
theorem localMoyPrasadGroupProperties_of_statements
    (hS1 : QuasiSplitLocalTorusFiltrationStatement.{u})
    (hProd : LocalMoyPrasadPositiveProductStatement.{u})
    (hDouble : KPLocalDoubleRootCommutatorStatement.{u})
    (hDZ : LocalMoyPrasadDepthZeroStatement.{u}) :
    LocalMoyPrasadGroupPropertiesStatement.{u} := by
  intro F _ _ _ _ H _ B hZ
  exact B.localMoyPrasadGroupProperties_of_estimates hZ hS1 hProd
    (hDouble F H B hZ) (hDZ F H B hZ).1 (hDZ F H B hZ).2

/-- S1 and the independent doubled-root and depth-zero propositions imply S2,
using the published positive-depth product theorem. -/
theorem localMoyPrasadGroupProperties_of_remaining_statements
    (hS1 : QuasiSplitLocalTorusFiltrationStatement.{u})
    (hDouble : KPLocalDoubleRootCommutatorStatement.{u})
    (hDZ : LocalMoyPrasadDepthZeroStatement.{u}) :
    LocalMoyPrasadGroupPropertiesStatement.{u} :=
  localMoyPrasadGroupProperties_of_statements hS1
    localMoyPrasadPositiveProduct hDouble hDZ

/-- S1 and the doubled-root estimate imply S2, using the published product
and depth-zero intersection theorems. -/
theorem localMoyPrasadGroupProperties_of_torus_statements
    (hS1 : QuasiSplitLocalTorusFiltrationStatement.{u})
    (hDouble : KPLocalDoubleRootCommutatorStatement.{u}) :
    LocalMoyPrasadGroupPropertiesStatement.{u} :=
  localMoyPrasadGroupProperties_of_remaining_statements hS1 hDouble
    localMoyPrasadDepthZero

/-- S1 implies S2, using the published valued rank-one coordinate theorem to
discharge the independent doubled-root estimate. -/
theorem localMoyPrasadGroupProperties_of_torus_filtration
    (hS1 : QuasiSplitLocalTorusFiltrationStatement.{u}) :
    LocalMoyPrasadGroupPropertiesStatement.{u} :=
  localMoyPrasadGroupProperties_of_torus_statements hS1
    (kpLocalDoubleRootCommutator_of_valuedRankOneCoordinates
      quasiSplitValuedRankOneCoordinates)

end Langlands.Geometry.Building.MaximalUnramified
