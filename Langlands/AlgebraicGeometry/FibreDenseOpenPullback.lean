import Langlands.AlgebraicGeometry.FibreGenericPoints
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Pullback and intersection of fibre-dense opens -/

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology

namespace Langlands.AlgebraicGeometry

variable {X Y S T : Scheme.{u}}

namespace FibreGenerizationDense

/-- Fibrewise generization density implies density in the total space. -/
theorem dense {f : X ⟶ S} {U : Set X} (hU : FibreGenerizationDense f U) : Dense U := by
  intro x
  obtain ⟨y, hy, _, hyx⟩ := hU x
  exact closure_mono (Set.singleton_subset_iff.mpr hy) hyx.mem_closure

/-- The two fibrewise generizations can be taken successively for open subsets. -/
theorem inter {f : X ⟶ S} {U V : X.Opens}
    (hU : FibreGenerizationDense f (U : Set X)) (hV : FibreGenerizationDense f (V : Set X)) :
    FibreGenerizationDense f (↑(U ⊓ V) : Set X) := by
  intro x
  obtain ⟨y, hy, hfy, hyx⟩ := hU x
  obtain ⟨z, hz, hfz, hzy⟩ := hV y
  exact ⟨z, ⟨hzy.mem_open U.isOpen hy, hz⟩, hfz.trans hfy, hzy.trans hyx⟩

/-- Fibrewise generization density is preserved under arbitrary base change. -/
theorem preimage_of_isPullback {f : X ⟶ S} {g : T ⟶ S} {p : Y ⟶ X} {q : Y ⟶ T}
    (H : IsPullback p q f g) {U : Set X} (hU : FibreGenerizationDense f U) :
    FibreGenerizationDense q (p ⁻¹' U) := by
  intro x
  let t := q x
  let s := g t
  let b : q.fiber t ⟶ f.fiber s :=
    pullback.map _ _ _ _ p (Spec.map (g.residueFieldMap t)) g H.w.symm (by simp [s])
  have hb : b ≫ f.fiberι s = q.fiberι t ≫ p := by
    exact pullback.lift_fst ..
  have hPB : IsPullback b (q.fiberToSpecResidueField t) (f.fiberToSpecResidueField s)
      (Spec.map (g.residueFieldMap t)) := isPullback_fiberToSpecResidueField_of_isPullback H t
  have : Flat (Spec.map (g.residueFieldMap t)) := by
    rw [Flat.SpecMap_iff]
    let := (g.residueFieldMap t).hom.toAlgebra
    change (algebraMap (S.residueField s) (T.residueField t)).Flat
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have : Flat b := MorphismProperty.of_isPullback hPB.flip inferInstance
  have hpx : f.fiberι s (b (q.asFiber x)) = p x := by
    rw [← Scheme.Hom.comp_apply, hb, Scheme.Hom.comp_apply, Scheme.Hom.fiberι_asFiber]
  obtain ⟨y, hy, hfy, hyx⟩ := hU (p x)
  have hsy : f y = s := by
    rw [hfy, ← hpx]
    exact (f.fiberHomeo s (b (q.asFiber x))).2
  let y' := (f.fiberHomeo s).symm ⟨y, hsy⟩
  have hy' : f.fiberι s y' = y := f.fiberι_fiberHomeo_symm s _
  have hsp : y' ⤳ b (q.asFiber x) := (f.fiberι s).isEmbedding.specializes_iff.mp (by
    rw [hy', hpx]
    exact hyx)
  obtain ⟨z, hz, hzb⟩ := Flat.generalizingMap b hsp
  refine ⟨q.fiberι t z, ?_, (q.fiberHomeo t z).2, ?_⟩
  · change p (q.fiberι t z) ∈ U
    rw [← Scheme.Hom.comp_apply, ← hb, Scheme.Hom.comp_apply, hzb, hy']
    exact hy
  · change q.fiberι (q x) z ⤳ x
    simpa only [Scheme.Hom.fiberι_asFiber] using hz.map (q.fiberι (q x)).continuous

/-- Fibrewise density pulls back along a map over the base that is generalizing. -/
theorem preimage_of_generalizing {f : X ⟶ S} {g : Y ⟶ X} {U : Set X}
    (hg : GeneralizingMap g) (hU : FibreGenerizationDense f U) :
    FibreGenerizationDense (g ≫ f) (g ⁻¹' U) := by
  intro x
  obtain ⟨y, hy, hfy, hyx⟩ := hU (g x)
  obtain ⟨z, hzx, hgz⟩ := hg hyx
  exact ⟨z, by simpa only [Set.mem_preimage, hgz] using hy,
    by simp only [Scheme.Hom.comp_apply, hgz, hfy], hzx⟩

end FibreGenerizationDense

end Langlands.AlgebraicGeometry
