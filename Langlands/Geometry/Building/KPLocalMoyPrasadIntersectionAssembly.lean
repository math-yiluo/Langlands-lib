import Langlands.Geometry.Building.KPLocalMoyPrasadIntersectionDepthZero
import Langlands.Geometry.Building.KPLocalMoyPrasadPositiveProductStatement
import Langlands.Geometry.Building.KPQuasiSplitLocalTorusFiltrationStatement

/-!
# Clauses 4–8 of the K-level Moy–Prasad group properties from the prerequisite statements

Assembly of clauses 4–8 of `LocalMoyPrasadGroupPropertiesStatement` from three published
propositions and the two depth-zero intersection facts: the commutator clause of
`QuasiSplitLocalTorusFiltrationStatement` (S1) feeds `LocalMoyPrasadPositiveProductStatement`,
whose conclusion is the sign product cover used at positive depth.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building.MaximalUnramified.BuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} [IsAffineHom H.X.hom]
  (B : BuildingData F H) (hZ : IsTorus B.centralizer.Z)

/-- The sign product cover at positive depth, from S1's commutator clause and the conditional
product cover statement `LocalMoyPrasadPositiveProductStatement`. -/
theorem productCover_of_statements
    (hS1 : QuasiSplitLocalTorusFiltrationStatement.{u})
    (hProd : LocalMoyPrasadPositiveProductStatement.{u}) :
    ∀ (x : B.Apartment) (r : ℝ≥0), 0 < r → ∀ mu : cocharacterLattice B.S,
      IsGenericCocharacter B.i mu →
        (B.moyPrasad hZ x r : Set (rationalPoints H)) =
          (B.rootFiltrationSpan x (positiveRelativeRoots B.i (-mu)) r :
              Set (rationalPoints H)) *
            (B.centralizerTorusImage hZ r : Set (rationalPoints H)) *
              (B.rootFiltrationSpan x (positiveRelativeRoots B.i mu) r :
                Set (rationalPoints H)) :=
  hProd F H B hZ (hS1 F H B hZ).1

/-- **Clauses 4–8** of `LocalMoyPrasadGroupPropertiesStatement` for `B`, from S1, the product
cover statement `LocalMoyPrasadPositiveProductStatement` and the two depth-zero intersection
facts. -/
theorem intersectionClauses_of_statements
    (hS1 : QuasiSplitLocalTorusFiltrationStatement.{u})
    (hProd : LocalMoyPrasadPositiveProductStatement.{u})
    (hDZa : ∀ (x : B.Apartment) (mu : cocharacterLattice B.S), IsGenericCocharacter B.i mu →
      B.rootGroupSpan (positiveRelativeRoots B.i mu) ⊓ B.moyPrasad hZ x 0 =
        B.rootFiltrationSpan x (positiveRelativeRoots B.i mu) 0)
    (hDZb : ∀ (x : B.Apartment) (ν : V B.S),
      B.pairingLeviSpan ν ⊓ B.moyPrasad hZ x 0 ≤
        B.centralizerTorusImage hZ 0 ⊔ B.rootFiltrationSpan x (B.zeroPairingRoots ν) 0) :
    LocalMoyPrasadRootIntersection B hZ ∧ LocalMoyPrasadIwahoriFactorization B hZ ∧
      LocalMoyPrasadLeviIntersection B hZ ∧ LocalMoyPrasadCentralizerIntersection B hZ ∧
      LocalMoyPrasadSeparated B hZ := by
  have hPC := B.productCover_of_statements hZ hS1 hProd
  exact ⟨B.rootIntersection_of_covers hZ hPC hDZa,
    B.iwahoriFactorization_of_productCover hZ hPC,
    B.leviIntersection_of_covers hZ hPC hDZb,
    B.centralizerIntersection_of_covers hZ hPC hDZb,
    B.separated_of_productCover hZ hPC⟩

end Langlands.Geometry.Building.MaximalUnramified.BuildingData
