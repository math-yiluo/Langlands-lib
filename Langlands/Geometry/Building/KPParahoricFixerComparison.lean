import Langlands.Geometry.Building.KPParahoric
import Langlands.Geometry.Building.KPZeroNormKernel
import Langlands.Geometry.Building.KPFiltrationTopology
import Langlands.Representation.Plancherel.RationalCharacterTopology

/-!
# Actual parahorics inside norm-one point fixers
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel

namespace Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

namespace ValuationBuildingData

variable (B : ValuationBuildingData G)

/-- V 7 places each actual root filtration in the ambient rational norm kernel. -/
theorem filtration_le_rationalCommonNormKernel
    (hB : B.apartment.IsTopologyCompatible)
    (x : B.Apartment) (a : relativeRoots B.i) (r : ℝ) :
    B.filtration x a r ≤ rationalCommonNormKernel G := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  exact compactSubgroup_le_rationalCommonNormKernel G _
    (B.isCompact_filtration hB x a r)

/-- A nonempty root fixer is contained in the ambient rational norm kernel. -/
theorem rootFixer_le_rationalCommonNormKernel
    (hB : B.apartment.IsTopologyCompatible)
    {Ω : Set B.Apartment} {x : B.Apartment} (hx : x ∈ Ω)
    (a : relativeRoots B.i) :
    B.rootFixer a Ω ≤ rationalCommonNormKernel G := by
  intro g hg
  exact B.filtration_le_rationalCommonNormKernel hB x a 0
    ((B.apartment.mem_rootFixer.mp hg).2 x hx)

/-- The sharp fixer of a nonempty apartment subset lies in the rational norm kernel. -/
theorem sharpFixer_le_rationalCommonNormKernel
    (hB : B.apartment.IsTopologyCompatible)
    {Ω : Set B.Apartment} {x : B.Apartment} (hx : x ∈ Ω) :
    B.sharpFixer Ω ≤ rationalCommonNormKernel G := by
  exact iSup_le fun a => B.rootFixer_le_rationalCommonNormKernel hB hx a

/-- The sharp fixer lies in the norm-one fixer of every point of its apartment subset. -/
theorem sharpFixer_le_compactStabilizer
    (hB : B.apartment.IsTopologyCompatible)
    {Ω : Set B.Apartment} {x : B.Apartment} (hx : x ∈ Ω) :
    B.sharpFixer Ω ≤ B.compactStabilizer (B.apartmentMap x) := by
  apply le_inf (B.sharpFixer_le_rationalCommonNormKernel hB hx)
  exact (B.apartment.sharpFixer_anti (Set.singleton_subset_iff.mpr hx)).trans
    (B.sharpFixer_le_fixer x)

end ValuationBuildingData

namespace ParahoricBuildingData

variable (P : ParahoricBuildingData G)

/-- The full supplied centralizer-zero factor fixes every apartment point and is norm one. -/
theorem map_centralizerZero_le_compactStabilizer (x : P.Apartment) :
    P.centralizerZero.map (rationalPoints.map P.centralizer.j) ≤
      P.compactStabilizer (P.apartmentMap x) := by
  intro g hg
  obtain ⟨z, hz, rfl⟩ := hg
  exact P.map_mem_compactStabilizer
    (P.zeroDatum.centralizerZero_le_rationalCommonNormKernel hz) x

/-- The actual full parahoric lies in the norm-one fixer of every point in its subset. -/
theorem parahoric_le_compactStabilizer
    (hP : P.apartment.IsTopologyCompatible)
    {Ω : Set P.Apartment} {x : P.Apartment} (hx : x ∈ Ω) :
    P.parahoric Ω ≤ P.compactStabilizer (P.apartmentMap x) :=
  sup_le (P.map_centralizerZero_le_compactStabilizer x)
    (P.toValuationBuildingData.sharpFixer_le_compactStabilizer hP hx)

/-- In particular, the point parahoric lies in the norm-one point fixer. -/
theorem parahoricAt_le_compactStabilizer
    (hP : P.apartment.IsTopologyCompatible) (x : P.Apartment) :
    P.parahoricAt x ≤ P.compactStabilizer (P.apartmentMap x) :=
  P.parahoric_le_compactStabilizer hP (Set.mem_singleton x)

/-- The full parahoric of a nonempty apartment subset lies in the ambient norm kernel. -/
theorem parahoric_le_rationalCommonNormKernel
    (hP : P.apartment.IsTopologyCompatible)
    {Ω : Set P.Apartment} {x : P.Apartment} (hx : x ∈ Ω) :
    P.parahoric Ω ≤ rationalCommonNormKernel G :=
  (P.parahoric_le_compactStabilizer hP hx).trans
    (P.apartment.compactStabilizer_le_rationalCommonNormKernel _)

/-- The canonical inclusion of an actual full parahoric into the norm-one point fixer. -/
def parahoricCompactStabilizerHom
    (hP : P.apartment.IsTopologyCompatible)
    {Ω : Set P.Apartment} {x : P.Apartment} (hx : x ∈ Ω) :
    P.parahoric Ω →* P.compactStabilizer (P.apartmentMap x) :=
  (P.parahoric Ω).subtype.codRestrict _
    (fun g => P.parahoric_le_compactStabilizer hP hx g.property)

@[simp] theorem parahoricCompactStabilizerHom_coe
    (hP : P.apartment.IsTopologyCompatible)
    {Ω : Set P.Apartment} {x : P.Apartment} (hx : x ∈ Ω) (g : P.parahoric Ω) :
    (P.parahoricCompactStabilizerHom hP hx g : rationalPoints G) = g := rfl

end ParahoricBuildingData

end Langlands.Geometry.Building
