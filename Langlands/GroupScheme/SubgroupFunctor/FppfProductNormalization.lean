import Langlands.GroupScheme.SubgroupFunctor.FppfProductLaws
import Langlands.GroupScheme.Reductive.FppfProductUnipotent

/-! # Normalization through represented fppf products -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S : Scheme.{u}} {G P D : GroupScheme S}
    {F N A : SubgroupFunctor G} {i : P ⟶ G} {d : D ⟶ G}

/-- An fppf-local subgroup normalized by both factors is normalized by
their represented fppf product. -/
theorem IsFppfProduct.normalizes (hi : IsFppfProduct F N i)
    (hA : A.IsFppfLocal) (hF : A.IsNormalizedBy F)
    (hN : A.IsNormalizedBy N) : A.IsNormalizedBy (range i) := by
  intro T g x hg hx
  obtain ⟨V, v, hf, hs, hl, p, n, hp, hn, he⟩ :=
    (hi.mem_range_iff T g).mp hg
  apply hA T V v hf hs hl
  rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, he]
  have hm := hF V p (n * (v ≫ x) * n⁻¹) hp
    (hN V n (v ≫ x) hn (A.comp_mem v hx))
  convert hm using 1
  group

/-- A represented fppf product is normalized whenever both factors are. -/
theorem IsFppfProduct.isNormalizedBy (hd : IsFppfProduct F N d)
    (hF : F.IsNormalizedBy A) (hN : N.IsNormalizedBy A) :
    (range d).IsNormalizedBy A := by
  intro T g x hg hx
  obtain ⟨V, v, hf, hs, hl, p, n, hp, hn, he⟩ :=
    (hd.mem_range_iff T x).mp hx
  apply hd.isFppfLocal T V v hf hs hl
  apply (hd.mem_range_iff V _).mpr
  rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, he]
  have hm := FppfLocallyInProduct.of_mul
    (hF V (v ≫ g) p (A.comp_mem v hg) hp)
    (hN V (v ≫ g) n (A.comp_mem v hg) hn)
  convert hm using 1
  group

/-- A subgroup is normalized by any subgroup contained in it. -/
theorem isNormalizedBy_of_le (h : F ≤ N) : N.IsNormalizedBy F := by
  intro T g x hg hx
  exact (N.carrier T).mul_mem ((N.carrier T).mul_mem (h T hg) hx)
    ((N.carrier T).inv_mem (h T hg))

/-- Normality inside a monic ambient subgroup follows from relative
normalization of the composite image. -/
theorem isNormal_range_of_isNormalizedBy_comp (q : D ⟶ P) (i : P ⟶ G)
    [Mono i.hom.hom]
    (hn : (range (q ≫ i)).IsNormalizedBy (range i)) :
    (range q).IsNormal := by
  intro T g x _ hx
  obtain ⟨y, rfl⟩ := mem_range.mp hx
  obtain ⟨z, hz⟩ := mem_range.mp
    (hn T (g ≫ i.hom.hom) (y ≫ (q ≫ i).hom.hom)
      (mem_range.mpr ⟨g, rfl⟩) (mem_range.mpr ⟨y, rfl⟩))
  apply mem_range.mpr
  refine ⟨z, ?_⟩
  apply (cancel_mono i.hom.hom).1
  simpa only [Grp.comp_hom_hom, Category.assoc, MonObj.mul_comp,
    GrpObj.inv_comp] using hz

end Langlands.GroupScheme.SubgroupFunctor
