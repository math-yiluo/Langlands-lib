import Langlands.Geometry.Analytic.SpecialCoverIntersectionKernels
import Langlands.Geometry.Analytic.GeneralizedAffinoid.ClosedQuotientBaseChange
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteDomainIdealDescentStatement

/-! # The closed global intersection quotient and its local comparisons -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra.ClosedQuotient

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B R : PresentedAffinoidAlgebra K} (f : BoundedAlgHom K A B)
  (J : Ideal A) [IsClosed (J : Set A)] (φ : BoundedAlgHom K B R)
  (hker : RingHom.ker φ.toAlgHom.toRingHom = f.closedIdealMap J)
  (hφ : φ.IsAdmissibleEpi)

local instance : IsClosed (f.closedIdealMap J : Set B) := f.isClosed_closedIdealMap J

/-- An effective closed local kernel identifies the actual base-changed global
quotient with the given admissible local quotient, with bounded inverse. -/
def baseChangeEquivOfAdmissibleEpi :
    BoundedAlgEquiv K (AffinoidPushout.algebra (map A J) f) R :=
  (pushoutEquiv f J).trans
    (equivOfAdmissibleEpi B (f.closedIdealMap J) φ hker hφ)

theorem baseChangeEquivOfAdmissibleEpi_comp_rightMap :
    (baseChangeEquivOfAdmissibleEpi f J φ hker hφ).toBoundedAlgHom.comp
      (AffinoidPushout.rightMap (map A J) f) = φ := by
  change (equivOfAdmissibleEpi B (f.closedIdealMap J) φ hker hφ).toBoundedAlgHom.comp
    ((pushoutToChangedQuotient f J).comp (AffinoidPushout.rightMap (map A J) f)) = φ
  rw [pushoutToChangedQuotient_comp_rightMap]
  exact lift_comp_map B (f.closedIdealMap J) φ (fun a ha =>
    (show a ∈ RingHom.ker φ.toAlgHom.toRingHom from hker ▸ ha))

end Langlands.Analytic.PresentedAffinoidAlgebra.ClosedQuotient

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : PresentedAffinoidAlgebra K}

/-- A whole-spectrum cover pulls back directly to a whole-spectrum cover, using
the actual pushout domains rather than a changed presentation of the whole. -/
def pullbackWhole (c : FiniteCover (Domain.whole K A)) (q : BoundedAlgHom K A B) :
    FiniteCover (Domain.whole K B) where
  size := c.size
  obj i := Domain.pullback q (c.obj i)
  map i := ⟨(Domain.pullback q (c.obj i)).baseMap, BoundedAlgHom.comp_id _⟩
  covers x _ := c.covers (BanachSpectrum.comap q.toBoundedRingHom x) (Set.mem_univ _)

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover

namespace Langlands.Analytic.IndexedAffinoidAtlas.FiniteChartGluingData.SubordinateProductIntersection

open CategoryTheory Set PresentedAffinoidAlgebra LocalDomain

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}
  {d : FiniteChartGluingData a} {U V : LocalDomain a}
  (cU : d.SubordinateLocalDomainCover U) (cV : d.SubordinateLocalDomainCover V)

local instance : IsClosed (globalIdeal cU cV :
    Set (AffinoidCoproduct.algebra K U.algebra V.algebra)) :=
  isClosed_globalIdeal cU cV

/-- The actual presented quotient by the explicit closed contraction ideal. -/
def algebra : PresentedAffinoidAlgebra K :=
  ClosedQuotient.algebra
    (AffinoidCoproduct.algebra K U.algebra V.algebra) (globalIdeal cU cV)

/-- The actual bounded global quotient map, including its original norm. -/
def globalMap :
    BoundedAlgHom K (AffinoidCoproduct.algebra K U.algebra V.algebra) (algebra cU cV) :=
  ClosedQuotient.map _ (globalIdeal cU cV)

theorem globalMap_isAdmissibleEpi : (globalMap cU cV).IsAdmissibleEpi :=
  ClosedQuotient.map_isAdmissibleEpi _ _

/-- The global quotient is covered by the actual inverse-image product domains. -/
def quotientCover : Domain.FiniteCover (Domain.whole K (algebra cU cV)) :=
  (cover cU cV).pullbackWhole (globalMap cU cV)

/-- This is the only use of general ideal effectiveness in the local comparison. -/
theorem localKernel_eq
    (heffect : Domain.FiniteCover.IdealEffectivenessStatement.{u})
    (hspecial : d.IsSpecialCover) (i : Fin (cover cU cV).size) :
    ((cover cU cV).obj i).baseMap.closedIdealMap (globalIdeal cU cV) =
      ideal cU cV i := by
  have h := heffect K _ _ (cover cU cV) (ideal cU cV)
    (isClosed_ideal cU cV) (idealCompatible cU cV hspecial) i
  have hmap : ((cover cU cV).map i).restriction = ((cover cU cV).obj i).baseMap := by
    have hmap := ((cover cU cV).map i).comp_baseMap
    change ((cover cU cV).map i).restriction.comp (BoundedAlgHom.id K _) = _ at hmap
    simpa only [BoundedAlgHom.comp_id] using hmap
  rw [hmap] at h
  exact h

/-- Conditional only on the still separate ideal-effectiveness theorem, each
local piece of the constructed quotient is the actual local intersection. -/
def localEquiv
    (heffect : Domain.FiniteCover.IdealEffectivenessStatement.{u})
    (hspecial : d.IsSpecialCover) (i : Fin (cover cU cV).size) :
    BoundedAlgEquiv K ((quotientCover cU cV).obj i).algebra
      (intersection cU cV i).obj.algebra :=
  ClosedQuotient.baseChangeEquivOfAdmissibleEpi
    ((cover cU cV).obj i).baseMap (globalIdeal cU cV) (quotientMap cU cV i)
    (localKernel_eq cU cV heffect hspecial i).symm
    (quotientMap_isAdmissibleEpi cU cV hspecial i)

variable (heffect : Domain.FiniteCover.IdealEffectivenessStatement.{u})
  (hspecial : d.IsSpecialCover) (i : Fin (cover cU cV).size)

theorem localEquiv_comp_pullbackMap :
    (localEquiv cU cV heffect hspecial i).toBoundedAlgHom.comp
      (Domain.pullbackMap (globalMap cU cV) ((cover cU cV).obj i)) =
        quotientMap cU cV i :=
  ClosedQuotient.baseChangeEquivOfAdmissibleEpi_comp_rightMap _ _ _ _ _

/-- The comparison retains the entire original structural map from the
coproduct, beyond equality of induced spectrum maps. -/
theorem localEquiv_comp_baseMap :
    (localEquiv cU cV heffect hspecial i).toBoundedAlgHom.comp
      (((quotientCover cU cV).obj i).baseMap.comp (globalMap cU cV)) =
        (quotientMap cU cV i).comp ((cover cU cV).obj i).baseMap := by
  change (localEquiv cU cV heffect hspecial i).toBoundedAlgHom.comp
    ((Domain.pullback (globalMap cU cV) ((cover cU cV).obj i)).baseMap.comp
      (globalMap cU cV)) = _
  rw [← Domain.pullbackMap_comp_baseMap]
  exact congrArg (fun h => h.comp ((cover cU cV).obj i).baseMap)
    (localEquiv_comp_pullbackMap cU cV heffect hspecial i)

theorem localEquiv_comp_leftMap :
    (localEquiv cU cV heffect hspecial i).toBoundedAlgHom.comp
      (((quotientCover cU cV).obj i).baseMap.comp
        ((globalMap cU cV).comp (AffinoidCoproduct.leftMap K U.algebra V.algebra))) =
      ((intersection cU cV i).left ≫
        U.extendInclusion (cU.algebraCover.obj (index cU cV i).1)).restriction := by
  change ((localEquiv cU cV heffect hspecial i).toBoundedAlgHom.comp
    (((quotientCover cU cV).obj i).baseMap.comp (globalMap cU cV))).comp
      (AffinoidCoproduct.leftMap K U.algebra V.algebra) = _
  rw [localEquiv_comp_baseMap, BoundedAlgHom.comp_assoc]
  change (quotientMap cU cV i).comp
    (((cU.algebraCover.obj (index cU cV i).1).product
      (cV.algebraCover.obj (index cU cV i).2)).baseMap.comp
        (AffinoidCoproduct.leftMap K U.algebra V.algebra)) = _
  rw [← Domain.productLeftMap_comp_baseMap]
  change ((ProductIntersection.quotientMap _ _ (intersection cU cV i)).comp
    ((cU.algebraCover.obj (index cU cV i).1).productLeftMap
      (cV.algebraCover.obj (index cU cV i).2))).comp _ = _
  rw [ProductIntersection.quotientMap_comp_productLeftMap]
  rfl

theorem localEquiv_comp_rightMap :
    (localEquiv cU cV heffect hspecial i).toBoundedAlgHom.comp
      (((quotientCover cU cV).obj i).baseMap.comp
        ((globalMap cU cV).comp (AffinoidCoproduct.rightMap K U.algebra V.algebra))) =
      ((intersection cU cV i).right ≫
        V.extendInclusion (cV.algebraCover.obj (index cU cV i).2)).restriction := by
  change ((localEquiv cU cV heffect hspecial i).toBoundedAlgHom.comp
    (((quotientCover cU cV).obj i).baseMap.comp (globalMap cU cV))).comp
      (AffinoidCoproduct.rightMap K U.algebra V.algebra) = _
  rw [localEquiv_comp_baseMap, BoundedAlgHom.comp_assoc]
  change (quotientMap cU cV i).comp
    (((cU.algebraCover.obj (index cU cV i).1).product
      (cV.algebraCover.obj (index cU cV i).2)).baseMap.comp
        (AffinoidCoproduct.rightMap K U.algebra V.algebra)) = _
  rw [← Domain.productRightMap_comp_baseMap]
  change ((ProductIntersection.quotientMap _ _ (intersection cU cV i)).comp
    ((cU.algebraCover.obj (index cU cV i).1).productRightMap
      (cV.algebraCover.obj (index cU cV i).2))).comp _ = _
  rw [ProductIntersection.quotientMap_comp_productRightMap]
  rfl

end Langlands.Analytic.IndexedAffinoidAtlas.FiniteChartGluingData.SubordinateProductIntersection
