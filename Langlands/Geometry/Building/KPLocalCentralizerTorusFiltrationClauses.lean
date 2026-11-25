import Langlands.Geometry.Building.KPLocalMoyPrasadGroups
import Langlands.Geometry.Building.KPQuasiSplitLocalTorusFiltrationStatement
import Langlands.Geometry.Building.KPLocalCentralizerFiltrationNormalizerStable
import Langlands.Geometry.Building.KPLocalCentralizerFiltrationCommutatorFriendly
import Langlands.Geometry.Building.KPLocalCentralizerFiltrationRootCompatible

/-! # The three clauses of KP Lemma 7.2.3 over `F^ur` in D1's convention

D1 (the module `KPLocalMoyPrasadGroups`) presents the torus `Z` by the single binder
`hZ : IsTorus B.centralizer.Z`
and defines `Z(K)_r = B.centralizerTorusFiltration hZ r` and
`j(Z(K)_r) = B.centralizerTorusImage hZ r`. Clause 3 for D1's filtration is
`centralizerTorusImage_isNormalizerStable` in `KPLocalCentralizerFiltrationNormalizerStable`;
this file collects the three clauses. The last theorem derives the published
S1 statement `QuasiSplitLocalTorusFiltrationStatement` from the coroot formula and the
positive-depth torus action.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open scoped CategoryTheory.MonObj NNReal

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building.MaximalUnramified.BuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} [IsAffineHom H.X.hom]
  (B : BuildingData F H) (hZ : IsTorus B.centralizer.Z)

/-- The three clauses of KP Lemma 7.2.3 over `K` for D1's filtration, assuming the coroot
formula (`KPLocalCorootComponentStatement`) and the positive-depth torus action
(`KPLocalTorusRootCommutatorStatement`). -/
theorem centralizerTorusFiltration_clauses_of_coroot_of_torusRoot
    (hcor : KPLocalCorootComponentStatement.{u})
    (hroot : KPLocalTorusRootCommutatorStatement.{u}) :
    (∀ (x : B.Apartment) (a : relativeRoots B.i) (u u' : rationalPoints H),
      u ∈ B.rootGroup a.1 → u ≠ 1 → u' ∈ B.rootGroup (-a.1) → u' ≠ 1 →
      ∀ r : ℝ≥0, 0 < r → (((r : ℝ) : WithTop ℝ) = x.val a.1 u + x.val (-a.1) u') →
      ∀ (v' v : rationalPoints H) (z : rationalPoints B.centralizer.Z),
        v' ∈ B.rootGroup (-a.1) → v ∈ B.rootGroup a.1 →
        u'⁻¹ * u * u' * u⁻¹ = v' * rationalPoints.map B.centralizer.j z * v →
        z ∈ B.centralizerTorusFiltration hZ r) ∧
    (∀ (x : B.Apartment) (a : relativeRoots B.i) (r s : ℝ≥0),
      ∀ z ∈ B.centralizerTorusImage hZ r, ∀ u ∈ B.filtration x a.1 s,
        z * u * z⁻¹ * u⁻¹ ∈
          B.apartment.filtrationBlock x (fun _ => ((r + s : ℝ≥0) : ℝ)) a.1) ∧
    (∀ n ∈ normalizerPoints B.i, ∀ r : ℝ≥0,
      (B.centralizerTorusImage hZ r).map (MulAut.conj n).toMonoidHom =
        B.centralizerTorusImage hZ r) :=
  ⟨B.centralizerTorusFiltration_isCommutatorFriendly_of_coroot hZ hcor,
    B.centralizerTorusImage_isRootCompatible_of_torusRoot hZ hroot,
    B.centralizerTorusImage_isNormalizerStable hZ⟩

end Langlands.Geometry.Building.MaximalUnramified.BuildingData

namespace Langlands.Geometry.Building

/-- S1 (KP Lemma 7.2.3 over `K = F^ur`, `QuasiSplitLocalTorusFiltrationStatement`) follows
from the coroot formula `KPLocalCorootComponentStatement` and the positive-depth
torus action `KPLocalTorusRootCommutatorStatement`. -/
theorem quasiSplitLocalTorusFiltration_of_coroot_of_torusRoot
    (hcor : KPLocalCorootComponentStatement.{u})
    (hroot : KPLocalTorusRootCommutatorStatement.{u}) :
    QuasiSplitLocalTorusFiltrationStatement.{u} :=
  fun _ _ _ _ _ _ _ B hZ =>
    B.centralizerTorusFiltration_clauses_of_coroot_of_torusRoot hZ hcor hroot

end Langlands.Geometry.Building
