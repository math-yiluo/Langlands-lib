import Langlands.Geometry.Analytic.AtlasIntersectionCoverSaturation

/-! # Transport from unchanged domains to their local extensions -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas.LocalDomain

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}
  {U V : LocalDomain a}

/-- Returning an extended domain to its original containing algebra recovers
the literal original locus. The algebra and base map are unchanged. -/
@[simp]
theorem extendInclusion_relativeDomain_locus (U : LocalDomain a)
    (S : Domain K U.algebra) :
    (U.extendInclusion S).relativeDomain.locus = S.locus := by
  change U.ambientMap ⁻¹' (U.extend S).locus = S.locus
  rw [extend_locus]
  exact Set.preimage_image_eq _ U.isEmbedding_ambientMap.injective

/-- Products of the relative extension inclusions retain the original
full product locus in the unchanged coproduct. -/
theorem extendInclusion_product_locus
    (S : Domain K U.algebra) (T : Domain K V.algebra) :
    ((U.extendInclusion S).relativeDomain.product
      (V.extendInclusion T).relativeDomain).locus = (S.product T).locus := by
  rw [Domain.product_locus, Domain.product_locus,
    extendInclusion_relativeDomain_locus, extendInclusion_relativeDomain_locus]

/-- An arbitrary bounded pullback preserves this literal product-locus
identification; no condition on the candidate map is needed. -/
theorem pullback_extendInclusion_product_locus {Q : PresentedAffinoidAlgebra K}
    (q : BoundedAlgHom K (AffinoidCoproduct.algebra K U.algebra V.algebra) Q)
    (S : Domain K U.algebra) (T : Domain K V.algebra) :
    (Domain.pullback q ((U.extendInclusion S).relativeDomain.product
      (V.extendInclusion T).relativeDomain)).locus =
      (Domain.pullback q (S.product T)).locus := by
  rw [Domain.pullback_locus, Domain.pullback_locus, extendInclusion_product_locus]

namespace FiniteIntersectionData

/-- Local comparisons on literal products of domains in the unchanged
input algebras give finite recognition data after extension to the atlas.
Saturation is derived from the comparisons, rather than supplied. -/
def ofExtendedProductCover {Q : PresentedAffinoidAlgebra K}
    (q : BoundedAlgHom K (AffinoidCoproduct.algebra K U.algebra V.algebra) Q)
    (c : Domain.FiniteCover (Domain.whole K Q))
    (S : Fin c.size → Domain K U.algebra) (T : Fin c.size → Domain K V.algebra)
    (piece : Fin c.size → LocalDomain a)
    (left : ∀ i, piece i ⟶ U.extend (S i))
    (right : ∀ i, piece i ⟶ V.extend (T i))
    (e : ∀ i, BoundedAlgEquiv K (c.obj i).algebra (piece i).algebra)
    (hf : ∀ i, (e i).toBoundedAlgHom.comp ((c.obj i).baseMap.comp
      (q.comp (AffinoidCoproduct.leftMap K U.algebra V.algebra))) =
        (left i).restriction.comp (S i).baseMap)
    (hg : ∀ i, (e i).toBoundedAlgHom.comp ((c.obj i).baseMap.comp
      (q.comp (AffinoidCoproduct.rightMap K U.algebra V.algebra))) =
        (right i).restriction.comp (T i).baseMap)
    (hpiece : ∀ i, (piece i).locus =
      (U.extend (S i)).locus ∩ (V.extend (T i)).locus)
    (hcover : ∀ i, (c.obj i).locus = (Domain.pullback q ((S i).product (T i))).locus)
    (hunion : (⋃ i, (piece i).locus) = U.locus ∩ V.locus) :
    FiniteIntersectionData U V Q
      (q.comp (AffinoidCoproduct.leftMap K U.algebra V.algebra))
      (q.comp (AffinoidCoproduct.rightMap K U.algebra V.algebra)) :=
  ofProductCover q c (fun i => U.extend (S i)) (fun i => V.extend (T i))
    piece (fun i => U.extendInclusion (S i)) (fun i => V.extendInclusion (T i))
    (fun i => left i ≫ U.extendInclusion (S i))
    (fun i => right i ≫ V.extendInclusion (T i)) e hf hg hpiece
    (fun i => (hcover i).trans (pullback_extendInclusion_product_locus q (S i) (T i)).symm)
    hunion

end FiniteIntersectionData
end Langlands.Analytic.IndexedAffinoidAtlas.LocalDomain
