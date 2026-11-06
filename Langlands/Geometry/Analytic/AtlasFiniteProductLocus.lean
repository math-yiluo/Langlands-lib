import Langlands.Geometry.Analytic.AtlasDomainExtensionTransport

/-! # Literal intersection unions from two finite full-domain covers -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas.LocalDomain

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}
  {U V : LocalDomain a}

/-- A finite cover of the unchanged algebra covers exactly the ambient
locus after extending every member through the original local domain. -/
theorem iUnion_extend_finiteCover (U : LocalDomain a)
    (c : Domain.FiniteCover (Domain.whole K U.algebra)) :
    (⋃ i, (U.extend (c.obj i)).locus) = U.locus := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact (U.extendInclusion (c.obj i)).subset hi
  · intro hx
    obtain ⟨z, rfl⟩ := U.range_ambientMap.symm ▸ hx
    obtain ⟨i, hi⟩ := c.covers z (Set.mem_univ z)
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    rw [extend_locus]
    exact ⟨z, hi, rfl⟩

/-- All pairs of members of two finite full-domain covers cover the literal
intersection of the two original ambient loci, including empty covers. -/
theorem iUnion_extend_inter_finiteCover
    (cU : Domain.FiniteCover (Domain.whole K U.algebra))
    (cV : Domain.FiniteCover (Domain.whole K V.algebra))
    {n : ℕ} (index : Fin n ≃ Fin cU.size × Fin cV.size) :
    (⋃ i, (U.extend (cU.obj (index i).1)).locus ∩
      (V.extend (cV.obj (index i).2)).locus) = U.locus ∩ V.locus := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact ⟨(U.extendInclusion _).subset hi.1, (V.extendInclusion _).subset hi.2⟩
  · rintro ⟨hxU, hxV⟩
    rw [← iUnion_extend_finiteCover U cU] at hxU
    rw [← iUnion_extend_finiteCover V cV] at hxV
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxU
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxV
    refine Set.mem_iUnion.mpr ⟨index.symm (i, j), ?_⟩
    simpa only [index.apply_symm_apply, Set.mem_inter_iff] using And.intro hi hj

namespace FiniteIntersectionData

/-- Finite product-cover comparisons supply both the union and saturation
fields of full intersection recognition. Neither is an additional input. -/
def ofFiniteExtendedProductCover {Q : PresentedAffinoidAlgebra K}
    (q : BoundedAlgHom K (AffinoidCoproduct.algebra K U.algebra V.algebra) Q)
    (cU : Domain.FiniteCover (Domain.whole K U.algebra))
    (cV : Domain.FiniteCover (Domain.whole K V.algebra))
    (c : Domain.FiniteCover (Domain.whole K Q))
    (index : Fin c.size ≃ Fin cU.size × Fin cV.size)
    (piece : Fin c.size → LocalDomain a)
    (left : ∀ i, piece i ⟶ U.extend (cU.obj (index i).1))
    (right : ∀ i, piece i ⟶ V.extend (cV.obj (index i).2))
    (e : ∀ i, BoundedAlgEquiv K (c.obj i).algebra (piece i).algebra)
    (hf : ∀ i, (e i).toBoundedAlgHom.comp ((c.obj i).baseMap.comp
      (q.comp (AffinoidCoproduct.leftMap K U.algebra V.algebra))) =
        (left i).restriction.comp (cU.obj (index i).1).baseMap)
    (hg : ∀ i, (e i).toBoundedAlgHom.comp ((c.obj i).baseMap.comp
      (q.comp (AffinoidCoproduct.rightMap K U.algebra V.algebra))) =
        (right i).restriction.comp (cV.obj (index i).2).baseMap)
    (hpiece : ∀ i, (piece i).locus =
      (U.extend (cU.obj (index i).1)).locus ∩
        (V.extend (cV.obj (index i).2)).locus)
    (hcover : ∀ i, (c.obj i).locus =
      (Domain.pullback q
        ((cU.obj (index i).1).product (cV.obj (index i).2))).locus) :
    FiniteIntersectionData U V Q
      (q.comp (AffinoidCoproduct.leftMap K U.algebra V.algebra))
      (q.comp (AffinoidCoproduct.rightMap K U.algebra V.algebra)) :=
  ofExtendedProductCover q c
    (fun i => cU.obj (index i).1) (fun i => cV.obj (index i).2)
    piece left right e hf hg hpiece hcover
    ((Set.iUnion_congr fun i => hpiece i).trans
      (iUnion_extend_inter_finiteCover cU cV index))

end FiniteIntersectionData
end Langlands.Analytic.IndexedAffinoidAtlas.LocalDomain
