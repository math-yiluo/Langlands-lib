import Langlands.Geometry.Analytic.AtlasIntersectionMapFactorization
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainProduct
import Langlands.Geometry.Analytic.GeneralizedAffinoid.AdmissiblePushoutKernel

/-! # Compatible quotient kernels on products of local full domains -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas.LocalDomain.ProductIntersection

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}
  {U V : LocalDomain a}
  (S : Domain K U.algebra) (T : Domain K V.algebra)
  (d : IntersectionData (U.extend S) (V.extend T))

/-- The actual local intersection quotient of the product-domain algebra. -/
def quotientMap : BoundedAlgHom K (S.product T).algebra d.obj.algebra :=
  (AffinoidCoproduct.lift K d.obj.algebra S.algebra T.algebra
    d.left.restriction d.right.restriction).comp (S.productToCoproductMap T)

@[simp]
theorem quotientMap_comp_productLeftMap :
    (quotientMap S T d).comp (S.productLeftMap T) = d.left.restriction := by
  rw [quotientMap, BoundedAlgHom.comp_assoc,
    Domain.productToCoproductMap_comp_productLeftMap]
  exact AffinoidCoproduct.lift_comp_leftMap K d.obj.algebra S.algebra T.algebra _ _

@[simp]
theorem quotientMap_comp_productRightMap :
    (quotientMap S T d).comp (S.productRightMap T) = d.right.restriction := by
  rw [quotientMap, BoundedAlgHom.comp_assoc,
    Domain.productToCoproductMap_comp_productRightMap]
  exact AffinoidCoproduct.lift_comp_rightMap K d.obj.algebra S.algebra T.algebra _ _

theorem quotientMap_comp_productCoproductMap :
    (quotientMap S T d).comp (S.productCoproductMap T) = d.presentationMap := by
  rw [quotientMap, BoundedAlgHom.comp_assoc,
    Domain.productToCoproductMap_comp_productCoproductMap, BoundedAlgHom.comp_id]
  rfl

/-- Admissibility is transferred from the genuine completed-tensor map by
the constructed bounded product comparison. -/
theorem quotientMap_isAdmissibleEpi
    (h : (CompletedTensorAlgebra.lift d.left.restriction
      d.right.restriction).IsAdmissibleEpi) :
    (quotientMap S T d).IsAdmissibleEpi := by
  apply BoundedAlgHom.IsAdmissibleEpi.of_comp (quotientMap S T d)
    (S.productCoproductMap T)
  rw [quotientMap_comp_productCoproductMap]
  apply BoundedAlgHom.IsAdmissibleEpi.of_comp d.presentationMap
    (AffinoidCoproduct.fromCompletedTensor K S.algebra T.algebra)
  change ((AffinoidCoproduct.lift K d.obj.algebra S.algebra T.algebra
    d.left.restriction d.right.restriction).comp
      (AffinoidCoproduct.fromCompletedTensor K S.algebra T.algebra)).IsAdmissibleEpi
  exact (AffinoidCoproduct.lift_comp_fromCompletedTensor K S.algebra T.algebra
    d.left.restriction d.right.restriction).symm ▸ h

/-- The two genuine factor maps determine a map out of the product algebra. -/
theorem product_hom_ext (R : PresentedAffinoidAlgebra K)
    (f g : BoundedAlgHom K (S.product T).algebra R)
    (hl : f.comp (S.productLeftMap T) = g.comp (S.productLeftMap T))
    (hr : f.comp (S.productRightMap T) = g.comp (S.productRightMap T)) : f = g := by
  have h : f.comp (S.productCoproductMap T) = g.comp (S.productCoproductMap T) := by
    apply AffinoidCoproduct.hom_ext K R S.algebra T.algebra
    · simpa only [BoundedAlgHom.comp_assoc,
        Domain.productCoproductMap_comp_leftMap] using hl
    · simpa only [BoundedAlgHom.comp_assoc,
        Domain.productCoproductMap_comp_rightMap] using hr
  have h' := congrArg (fun q : BoundedAlgHom K
      (AffinoidCoproduct.algebra K S.algebra T.algebra) R =>
        q.comp (S.productToCoproductMap T)) h
  simpa only [BoundedAlgHom.comp_assoc,
    Domain.productCoproductMap_comp_productToCoproductMap, BoundedAlgHom.comp_id] using h'

variable {S T d}
  {S' : Domain K U.algebra} {T' : Domain K V.algebra}
  (d' : IntersectionData (U.extend S') (V.extend T'))
  (E : Domain K (AffinoidCoproduct.algebra K U.algebra V.algebra))
  (p : E ⟶ S.product T) (p' : E ⟶ S'.product T')

/-- After any common full-domain restriction of two product pieces, the first
quotient base change receives the other intersection with its complete maps. -/
theorem exists_factor_to_baseChange :
    ∃ θ : BoundedAlgHom K d'.obj.algebra
        (AffinoidPushout.algebra (quotientMap S T d) p.restriction),
      θ.comp (quotientMap S' T' d') =
        (AffinoidPushout.rightMap (quotientMap S T d) p.restriction).comp
          p'.restriction := by
  let q := quotientMap S T d
  let R := AffinoidPushout.algebra q p.restriction
  let l := AffinoidPushout.leftMap q p.restriction
  let r := AffinoidPushout.rightMap q p.restriction
  have hbase : (r.comp p'.restriction).comp (S'.product T').baseMap =
      (l.comp q).comp (S.product T).baseMap := by
    rw [BoundedAlgHom.comp_assoc, p'.comp_baseMap, AffinoidPushout.condition,
      BoundedAlgHom.comp_assoc, p.comp_baseMap]
  have hU : ((r.comp p'.restriction).comp (S'.productLeftMap T')).comp S'.baseMap =
      l.comp (d.left ≫ U.extendInclusion S).restriction := by
    rw [BoundedAlgHom.comp_assoc, Domain.productLeftMap_comp_baseMap,
      ← BoundedAlgHom.comp_assoc, hbase, BoundedAlgHom.comp_assoc,
      ← Domain.productLeftMap_comp_baseMap]
    change (l.comp ((quotientMap S T d).comp (S.productLeftMap T))).comp
      S.baseMap = _
    rw [quotientMap_comp_productLeftMap]
    rfl
  have hV : ((r.comp p'.restriction).comp (S'.productRightMap T')).comp T'.baseMap =
      l.comp (d.right ≫ V.extendInclusion T).restriction := by
    rw [BoundedAlgHom.comp_assoc, Domain.productRightMap_comp_baseMap,
      ← BoundedAlgHom.comp_assoc, hbase, BoundedAlgHom.comp_assoc,
      ← Domain.productRightMap_comp_baseMap]
    change (l.comp ((quotientMap S T d).comp (S.productRightMap T))).comp
      T.baseMap = _
    rw [quotientMap_comp_productRightMap]
    rfl
  obtain ⟨θ, hθl, hθr⟩ := d'.exists_factor_of_witness
    (U.extendInclusion S') (V.extendInclusion T')
    (d.left ≫ U.extendInclusion S) (d.right ≫ V.extendInclusion T) R
    ((r.comp p'.restriction).comp (S'.productLeftMap T'))
    ((r.comp p'.restriction).comp (S'.productRightMap T')) l hU hV
  refine ⟨θ, ?_⟩
  apply product_hom_ext S' T' R
  · rw [BoundedAlgHom.comp_assoc, quotientMap_comp_productLeftMap]
    exact hθl
  · rw [BoundedAlgHom.comp_assoc, quotientMap_comp_productRightMap]
    exact hθr

/-- The overlap quotient obtained from the second product piece maps into the
one obtained from the first, over the unchanged overlap algebra. -/
theorem exists_baseChangeMap :
    ∃ φ : BoundedAlgHom K
        (AffinoidPushout.algebra (quotientMap S' T' d') p'.restriction)
        (AffinoidPushout.algebra (quotientMap S T d) p.restriction),
      φ.comp (AffinoidPushout.rightMap (quotientMap S' T' d') p'.restriction) =
        AffinoidPushout.rightMap (quotientMap S T d) p.restriction := by
  obtain ⟨θ, hθ⟩ := exists_factor_to_baseChange d' E p p'
  exact ⟨AffinoidPushout.lift _ _ _ θ
      (AffinoidPushout.rightMap (quotientMap S T d) p.restriction) hθ,
    AffinoidPushout.lift_comp_rightMap _ _ _ _ _ _⟩

/-- The two overlap quotients have the same exact ring kernel, without an
inverse-map assumption or any assertion of ideal effectiveness. -/
theorem baseChange_kernel_eq :
    RingHom.ker (AffinoidPushout.rightMap (quotientMap S T d)
        p.restriction).toAlgHom.toRingHom =
      RingHom.ker (AffinoidPushout.rightMap (quotientMap S' T' d')
        p'.restriction).toAlgHom.toRingHom := by
  obtain ⟨φ, hφ⟩ := exists_baseChangeMap d' E p p'
  obtain ⟨ψ, hψ⟩ := exists_baseChangeMap d E p' p
  ext b
  change AffinoidPushout.rightMap (quotientMap S T d) p.restriction b = 0 ↔
    AffinoidPushout.rightMap (quotientMap S' T' d') p'.restriction b = 0
  constructor
  · intro hb
    have h := congrArg (fun q : BoundedAlgHom K E.algebra
      (AffinoidPushout.algebra (quotientMap S' T' d') p'.restriction) => q b) hψ
    exact h.symm.trans ((congrArg ψ hb).trans (map_zero _))
  · intro hb
    have h := congrArg (fun q : BoundedAlgHom K E.algebra
      (AffinoidPushout.algebra (quotientMap S T d) p.restriction) => q b) hφ
    exact h.symm.trans ((congrArg φ hb).trans (map_zero _))

/-- Admissible local intersection quotients have equal closed extensions of
their actual kernels on every common full-domain restriction. -/
theorem closedIdealMap_kernel_eq
    (h : (quotientMap S T d).IsAdmissibleEpi)
    (h' : (quotientMap S' T' d').IsAdmissibleEpi) :
    p.restriction.closedIdealMap (RingHom.ker (quotientMap S T d).toAlgHom.toRingHom) =
      p'.restriction.closedIdealMap
        (RingHom.ker (quotientMap S' T' d').toAlgHom.toRingHom) := by
  rw [← AffinoidPushout.ker_rightMap _ _ h,
    ← AffinoidPushout.ker_rightMap _ _ h']
  exact baseChange_kernel_eq d' E p p'

end Langlands.Analytic.IndexedAffinoidAtlas.LocalDomain.ProductIntersection
