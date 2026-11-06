import Langlands.Geometry.Analytic.AtlasIntersectionProductKernel
import Langlands.Geometry.Analytic.FiniteChartLocalDomainCover
import Langlands.Geometry.Analytic.SpecialCoverLocalIntersection
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainProductCover

/-! # Compatible actual kernels on a subordinate product cover -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas.FiniteChartGluingData

open CategoryTheory Set PresentedAffinoidAlgebra LocalDomain

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}
  {d : FiniteChartGluingData a} {U V : LocalDomain a}

namespace SubordinateLocalDomainCover

variable (c : d.SubordinateLocalDomainCover U)

/-- Extending the unchanged algebra cover recovers each original local locus. -/
theorem extend_algebraCover_locus (i : Fin c.cover.size) :
    (U.extend (c.algebraCover.obj i)).locus = (c.localDomain i).locus := by
  change a.chart U.index ''
    (U.domain.extend (U.domain.relative (c.cover.obj i) (c.cover.map i))).locus =
      a.chart U.index '' (c.cover.obj i).locus
  rw [Domain.extend_relative_locus]

theorem extend_algebraCover_subset_member (i : Fin c.cover.size) :
    (U.extend (c.algebraCover.obj i)).locus ⊆
      Set.range (a.chart (d.index (c.member i))) := by
  rw [c.extend_algebraCover_locus]
  exact c.localDomain_subset_member i

end SubordinateLocalDomainCover

namespace SubordinateProductIntersection

variable (cU : d.SubordinateLocalDomainCover U)
  (cV : d.SubordinateLocalDomainCover V)

/-- The actual finite full-domain cover of the unchanged affinoid coproduct. -/
def cover :
    Domain.FiniteCover
      (Domain.whole K (AffinoidCoproduct.algebra K U.algebra V.algebra)) :=
  cU.algebraCover.coproductCover cV.algebraCover

/-- The original pair of subordinate indices corresponding to a cover member. -/
def index (k : Fin (cover cU cV).size) :
    Fin cU.cover.size × Fin cV.cover.size :=
  cU.algebraCover.productIndexEquiv cV.algebraCover k

/-- A full intersection of the extended relative domains, with both original
bounded inclusion restrictions retained. -/
def intersection (k : Fin (cover cU cV).size) :
    IntersectionData
      (U.extend (cU.algebraCover.obj (index cU cV k).1))
      (V.extend (cV.algebraCover.obj (index cU cV k).2)) where
  obj := d.localIntersection
    (cU.member (index cU cV k).1) (cV.member (index cU cV k).2)
    _ _ (cU.extend_algebraCover_subset_member _)
    (cV.extend_algebraCover_subset_member _)
  left := d.localIntersectionLeft _ _ _ _ _ _
  right := d.localIntersectionRight _ _ _ _ _ _
  locus_eq := d.localIntersection_locus _ _ _ _ _ _

/-- The quotient of a product-cover member is the actual local intersection,
using its two unchanged factor algebras. -/
def quotientMap (k : Fin (cover cU cV).size) :
    BoundedAlgHom K ((cover cU cV).obj k).algebra
      (intersection cU cV k).obj.algebra :=
  ProductIntersection.quotientMap _ _ (intersection cU cV k)

theorem quotientMap_isAdmissibleEpi (hspecial : d.IsSpecialCover)
    (k : Fin (cover cU cV).size) :
    (quotientMap cU cV k).IsAdmissibleEpi := by
  apply ProductIntersection.quotientMap_isAdmissibleEpi
  exact d.localIntersection_tensor_isAdmissibleEpi _ _ _ _ _ _
    (hspecial.2 _ _)

/-- The actual ring kernel, with no radicalization or replacement by point data. -/
def ideal (k : Fin (cover cU cV).size) : Ideal ((cover cU cV).obj k).algebra :=
  RingHom.ker (quotientMap cU cV k).toAlgHom.toRingHom

theorem isClosed_ideal (k : Fin (cover cU cV).size) :
    IsClosed (ideal cU cV k : Set ((cover cU cV).obj k).algebra) :=
  isClosed_eq (quotientMap cU cV k).continuous continuous_const

/-- The closed local kernels agree on every actual product-cover overlap. -/
theorem idealCompatible (hspecial : d.IsSpecialCover) :
    (cover cU cV).IdealCompatible (ideal cU cV) := by
  intro i j
  exact ProductIntersection.closedIdealMap_kernel_eq (intersection cU cV j)
    (((cover cU cV).obj i).inter ((cover cU cV).obj j))
    (((cover cU cV).obj i).interLeft ((cover cU cV).obj j))
    (((cover cU cV).obj i).interRight ((cover cU cV).obj j))
    (quotientMap_isAdmissibleEpi cU cV hspecial i)
    (quotientMap_isAdmissibleEpi cU cV hspecial j)

/-- The explicit closed global ideal of sections satisfying all local kernels. -/
def globalIdeal : Ideal (AffinoidCoproduct.algebra K U.algebra V.algebra) :=
  (cover cU cV).idealContraction (ideal cU cV)

theorem isClosed_globalIdeal :
    IsClosed (globalIdeal cU cV :
      Set (AffinoidCoproduct.algebra K U.algebra V.algebra)) :=
  (cover cU cV).isClosed_idealContraction _ (isClosed_ideal cU cV)

end SubordinateProductIntersection
end Langlands.Analytic.IndexedAffinoidAtlas.FiniteChartGluingData
