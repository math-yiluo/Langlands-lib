import Langlands.AlgebraicGeometry.PointTopology.FilteredRingPointTopologicalStatement
import Langlands.AlgebraicGeometry.PointTopology.FilteredRingPointProof
import Langlands.AlgebraicGeometry.PointTopology.FilteredRingPointOpenProof

/-!
# Topological comparison for actual filtered scheme points
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- Local finite presentation supplies the actual point bijection; continuous
open transitions transport the stated stage properties to its final topology. -/
theorem filteredRingPointTopologicalComparison :
    FilteredRingPointTopologicalComparison.{u} := by
  intro R _ J _ _ F c hc X hfp τ
  have hpoints := (filteredRingPointComparison R J F c hc X).2 hfp
  let := ringPointColimitTopology R F X τ
  let := ringPointCoconeTopology R F X τ c
  let e := ringPointColimitHomeomorph R F X τ c hpoints.2.2
  refine ⟨⟨e, fun _ => rfl⟩, ?_⟩
  intro hT
  have hstages := filteredRingPointOpenStages R J F X τ hT
  have hopen (i : J) : @IsOpenMap _ _ (τ i) (ringPointCoconeTopology R F X τ c)
      (fun p : RingPoint R X (F.obj i) => p.changeRing (c.ι.app i).hom) := by
    let := τ i
    change IsOpenMap (e ∘ ringPointColimitι R F X i)
    exact e.isOpenMap.comp (hstages.1 i)
  refine ⟨hopen, ?_, ?_, ?_⟩
  · intro hlocal
    refine ⟨?_⟩
    intro p U hU
    obtain ⟨i, q, rfl⟩ := hpoints.1 p
    let := τ i
    let := hlocal i
    have hcont := ringPointCoconeTopology_continuous_ι R F X τ c i
    obtain ⟨K, hKq, hKU, hKc⟩ := local_compact_nhds (hcont.continuousAt hU)
    exact ⟨(fun q : RingPoint R X (F.obj i) => q.changeRing (c.ι.app i).hom) '' K,
      (hopen i).image_mem_nhds hKq, Set.image_subset_iff.mpr hKU, hKc.image hcont⟩
  · intro S hS hcover hsecond
    let : Countable S := hS.to_subtype
    let τS (i : S) : TopologicalSpace (RingPoint R X (F.obj i.val)) := τ i.val
    let secondS (i : S) : SecondCountableTopology (RingPoint R X (F.obj i.val)) :=
      hsecond i.val i.property
    let f : (Σ i : S, RingPoint R X (F.obj i.val)) → RingPoint R X c.pt :=
      fun p => p.2.changeRing (c.ι.app p.1.val).hom
    have hf : IsOpenQuotientMap f := by
      refine ⟨?_, ?_, ?_⟩
      · intro p
        obtain ⟨i, hi, q, hq⟩ := hcover p
        exact ⟨⟨⟨i, hi⟩, q⟩, hq⟩
      · exact continuous_sigma (fun i => ringPointCoconeTopology_continuous_ι R F X τ c i.val)
      · exact isOpenMap_sigma.mpr (fun i => hopen i.val)
    exact hf.secondCountableTopology
  · intro hinj
    have hemb (i : J) : @IsOpenEmbedding _ _ (τ i) (ringPointCoconeTopology R F X τ c)
        (fun p : RingPoint R X (F.obj i) => p.changeRing (c.ι.app i).hom) := by
      let := τ i
      change IsOpenEmbedding (e ∘ ringPointColimitι R F X i)
      exact e.isOpenEmbedding.comp (hstages.2.2 hinj i)
    refine ⟨hemb, ?_⟩
    intro ht2
    refine ⟨?_⟩
    intro p q hpq
    obtain ⟨i, pi, hpi⟩ := hpoints.1 p
    obtain ⟨j, pj, hpj⟩ := hpoints.1 q
    have hpi' :
        (pi.changeRing (F.map (IsFiltered.leftToMax i j)).hom).changeRing
          (c.ι.app (IsFiltered.max i j)).hom = p := by
      change ringPointColimitMap R F X c (ringPointColimitι R F X (IsFiltered.max i j)
        (pi.changeRing (F.map (IsFiltered.leftToMax i j)).hom)) = p
      rw [ringPointColimitι_changeRing]
      exact hpi
    have hpj' :
        (pj.changeRing (F.map (IsFiltered.rightToMax i j)).hom).changeRing
          (c.ι.app (IsFiltered.max i j)).hom = q := by
      change ringPointColimitMap R F X c (ringPointColimitι R F X (IsFiltered.max i j)
        (pj.changeRing (F.map (IsFiltered.rightToMax i j)).hom)) = q
      rw [ringPointColimitι_changeRing]
      exact hpj
    let := τ (IsFiltered.max i j)
    let := ht2 (IsFiltered.max i j)
    have hne : pi.changeRing (F.map (IsFiltered.leftToMax i j)).hom ≠
        pj.changeRing (F.map (IsFiltered.rightToMax i j)).hom := by
      intro h
      apply hpq
      exact hpi'.symm.trans
        ((congrArg (fun z => z.changeRing (c.ι.app (IsFiltered.max i j)).hom) h).trans hpj')
    obtain ⟨U, V, hU, hV, hpU, hqV, hUV⟩ :=
      separated_by_isOpenEmbedding (hemb (IsFiltered.max i j)) hne
    exact ⟨U, V, hU, hV, by rwa [hpi'] at hpU, by rwa [hpj'] at hqV, hUV⟩

end Langlands.AlgebraicGeometry.PointTopology
