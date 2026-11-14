import Langlands.Geometry.Building.KPUnramifiedComparisonRootHelpers
import Langlands.Geometry.Building.RootValueTorusUniformBlocks
import Langlands.GroupScheme.Rational.RelativeRootSystemProof

/-! # Uniform root fibre depth preimages along a concrete apartment lift -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

private instance nonmultipliableComparisonAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (UnramifiedClosure F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (UnramifiedClosure F)))
  infer_instance

namespace ParahoricBuildingData.UnramifiedComparisonTorus.ApartmentLift

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {P : ParahoricBuildingData G} {t : P.UnramifiedComparisonTorus}
    (L : t.ApartmentLift)

local notation "fK" =>
  CategoryTheory.Functor.map
    (CommGroupScheme.baseChange (algebraBaseMap F (UnramifiedClosure F))) t.f
local notation "aK" a =>
  characterLattice.baseChange (algebraBaseMap F (UnramifiedClosure F)) P.S a

/-- The lower rational points whose extensions lie in the positive upper
restriction fibre at a single uniform depth. -/
def rootFiberDepthPreimage (y : P.Apartment) (a : relativeRoots P.i) (r : ℝ) :
    Subgroup (rationalPoints G) :=
  (L.buildingData.rootFiltrationSpan (L.e y) (L.rootFiber a) r).comap
    (rationalExtend F (UnramifiedClosure F) G)

set_option maxHeartbeats 1000000 in
/-- At depth zero, the filtration is the exact preimage of the entire positive
restriction fibre, including for a multipliable lower root. -/
theorem filtration_zero_eq_rootFiber (y : P.Apartment) (a : relativeRoots P.i) :
    P.filtration y a 0 = L.rootFiberDepthPreimage y a 0 := by
  rw [L.filtration_eq_restrictedDepth y a 0,
    torusRestrictedRootDepthSubgroup_zero_eq_uniform]
  apply congrArg (Subgroup.comap (rationalExtend F (UnramifiedClosure F) G))
  unfold torusUniformRootDepthSubgroup MaximalUnramified.BuildingData.rootFiltrationSpan
  rw [iSup_subtype]
  rfl

/-- At zero depth, a rational point in the upper uniform fibre gives a lower
block by taking the doubled factor to be the identity. -/
theorem block_mem_rootFiber_zero (y : P.Apartment) (a : relativeRoots P.i)
    (g : rationalPoints G)
    (hg : rationalExtend F (UnramifiedClosure F) G g ∈
      L.buildingData.rootFiltrationSpan (L.e y) (L.rootFiber a) 0) :
    g ∈ P.apartment.filtrationBlock y (fun _ => (0 : ℝ)) a.val := by
  have hgF : g ∈ P.filtration y a 0 := by
    rw [L.filtration_zero_eq_rootFiber y a]
    exact hg
  exact P.apartment.mem_filtrationBlock.mpr
    ⟨g, hgF, 1, (P.apartment.doubleFiltration y a 0).one_mem, mul_one g⟩

set_option maxHeartbeats 1000000 in
/-- At a nonmultipliable lower root, the filtration is the exact preimage of
the entire positive restriction fibre at one uniform depth. -/
theorem filtration_eq_rootFiber_of_not_double (y : P.Apartment) (a : relativeRoots P.i)
    (h2a : 2 • a.val ∉ relativeRoots P.i) (r : ℝ) :
    P.filtration y a r =
      (L.buildingData.rootFiltrationSpan (L.e y) (L.rootFiber a) r).comap
        (rationalExtend F (UnramifiedClosure F) G) := by
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  rw [L.filtration_eq_restrictedDepth y a r,
    torusRestrictedRootDepthSubgroup_eq_uniform_of_not_double P.i
      (L.apartment.isRootDatumValuation_of_mem (L.e y).mem)
      P.isMaximalSplitTorus.isSplitSubtorus.1
      (relativeRootSystem F G P.isConnectedReductive P.S P.i P.isMaximalSplitTorus)
      fK (fieldFactorization (t := t)) a.property h2a r]
  apply congrArg (Subgroup.comap (rationalExtend F (UnramifiedClosure F) G))
  unfold torusUniformRootDepthSubgroup MaximalUnramified.BuildingData.rootFiltrationSpan
  rw [iSup_subtype]
  rfl

/-- The block-descent field at a nonmultipliable root follows by taking the
identity as the doubled-root factor. -/
theorem block_mem_rootFiber_of_not_double (y : P.Apartment) (a : relativeRoots P.i)
    (h2a : 2 • a.val ∉ relativeRoots P.i) (s : ℝ≥0) (g : rationalPoints G)
    (hg : rationalExtend F (UnramifiedClosure F) G g ∈
      L.buildingData.rootFiltrationSpan (L.e y) (L.rootFiber a) s) :
    g ∈ P.apartment.filtrationBlock y (fun _ => (s : ℝ)) a.val := by
  have hgF : g ∈ P.filtration y a s := by
    rw [L.filtration_eq_rootFiber_of_not_double y a h2a s]
    exact hg
  exact P.apartment.mem_filtrationBlock.mpr
    ⟨g, hgF, 1, (P.apartment.doubleFiltration y a s).one_mem, mul_one g⟩

end ParahoricBuildingData.UnramifiedComparisonTorus.ApartmentLift

end Langlands.Geometry.Building
