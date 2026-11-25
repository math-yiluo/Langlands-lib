/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Sober
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Topology.Irreducible

/-!
# Generic neighborhoods in a finite scheme stratification

## References

* Stacks Project, Tags 0BA8, 01IS, 004V, 004W, 004X, 01JR, 01JY and 01IQ
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A finite stratification has neighborhoods of all component generic points inside their
stratum images. The actual pullback retains the stratum's scheme structure: its first
projection is a surjective closed immersion, and its second projection is an open immersion.
The union of the neighborhoods is a dense open containing all component generic points. -/
theorem exists_stratification_generic_neighborhoods
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (s : FiniteLocallyClosedStratification X) :
    (irreducibleComponents X).Finite ∧
      ∃ (η : irreducibleComponents X → X)
        (j : irreducibleComponents X → Fin s.n)
        (W : irreducibleComponents X → X.Opens),
        (∀ C : irreducibleComponents X,
          IsGenericPoint (η C) C.val ∧
          (∀ x : X, IsGenericPoint x C.val → x = η C) ∧
          η C ∈ Set.range (s.immersion (j C)) ∧
          (∀ k : Fin s.n, η C ∈ Set.range (s.immersion k) → k = j C) ∧
          η C ∈ W C ∧
          (W C : Set X) ⊆ Set.range (s.immersion (j C)) ∧
          Surjective (pullback.fst (W C).ι (s.immersion (j C))) ∧
          IsClosedImmersion (pullback.fst (W C).ι (s.immersion (j C))) ∧
          IsOpenImmersion (pullback.snd (W C).ι (s.immersion (j C)))) ∧
        Dense ((⨆ C, W C : X.Opens) : Set X) ∧
        (∀ C : irreducibleComponents X, η C ∈ (⨆ D, W D : X.Opens)) := by
  classical
  have : IsNoetherian X := ⟨⟩
  have hfin : (irreducibleComponents X).Finite :=
    finite_irreducibleComponents_of_isNoetherian
  let η (C : irreducibleComponents X) : X := (genericPoints.ofComponent C).val
  have hη (C : irreducibleComponents X) : IsGenericPoint (η C) C.val :=
    genericPoints.isGenericPoint_ofComponent C
  have hstratum (C : irreducibleComponents X) : ∃ k, η C ∈ s.stratum k := by
    have hmem : η C ∈ ⋃ k, s.stratum k := by
      rw [s.iUnion_stratum_eq_univ]
      exact Set.mem_univ _
    exact Set.mem_iUnion.mp hmem
  choose j hj using hstratum
  have hW (C : irreducibleComponents X) :
      ∃ W : X.Opens, η C ∈ W ∧ (W : Set X) ⊆ Set.range (s.immersion (j C)) := by
    obtain ⟨O, F, hO, hF, hOF⟩ := s.isLocallyClosed_stratum (j C)
    have hηOF : η C ∈ O ∩ F := hOF ▸ hj C
    have hCF : C.val ⊆ F := ((hη C).mem_closed_set_iff hF).mp hηOF.2
    let others : Set (Set X) := irreducibleComponents X \ {C.val}
    have hclosed : IsClosed (⋃ D ∈ others, D) :=
      hfin.sdiff.isClosed_biUnion fun D hD => isClosed_of_mem_irreducibleComponents D hD.1
    let V : X.Opens := ⟨(⋃ D ∈ others, D)ᶜ, hclosed.isOpen_compl⟩
    have hηV : η C ∈ V := by
      intro hmem
      obtain ⟨D, hD, hηD⟩ := Set.mem_iUnion₂.mp hmem
      have hCD : C.val ⊆ D := ((hη C).mem_closed_set_iff
        (isClosed_of_mem_irreducibleComponents D hD.1)).mp hηD
      have hDC : D = C.val := (C.property.2 hD.1.1 hCD).antisymm hCD
      exact hD.2 (Set.mem_singleton_iff.mpr hDC)
    have hVC : (V : Set X) ⊆ C.val := by
      intro x hx
      by_contra hxC
      apply hx
      exact Set.mem_iUnion₂.mpr ⟨irreducibleComponent x,
        ⟨irreducibleComponent_mem_irreducibleComponents x, by
          intro heq
          exact hxC ((Set.mem_singleton_iff.mp heq) ▸ mem_irreducibleComponent)⟩,
        mem_irreducibleComponent⟩
    refine ⟨V ⊓ ⟨O, hO⟩, ⟨hηV, hηOF.1⟩, ?_⟩
    intro x hx
    rw [s.range_immersion, hOF]
    exact ⟨hx.2, hCF (hVC hx.1)⟩
  choose W hηW hWrange using hW
  refine ⟨hfin, η, j, W, ?_, ?_, ?_⟩
  · intro C
    have himm : IsImmersion (s.immersion (j C)) := s.isImmersion (j C)
    have hsurj : Surjective (pullback.fst (W C).ι (s.immersion (j C))) := by
      constructor
      intro w
      have hw : (W C).ι w ∈
          Set.range (pullback.fst (W C).ι (s.immersion (j C)) ≫ (W C).ι) := by
        rw [IsOpenImmersion.range_pullback_to_base_of_left]
        exact ⟨⟨w, rfl⟩, hWrange C w.property⟩
      obtain ⟨z, hz⟩ := hw
      refine ⟨z, (W C).ι.isEmbedding.injective ?_⟩
      simpa only [Scheme.Hom.comp_apply] using hz
    have hclosed : IsClosedImmersion (pullback.fst (W C).ι (s.immersion (j C))) :=
      IsClosedImmersion.of_isPreimmersion _ (by
        rw [Set.range_eq_univ.mpr hsurj.surj]
        exact isClosed_univ)
    refine ⟨hη C, fun x hx => hx.eq (hη C), ?_, ?_, hηW C, hWrange C,
      hsurj, hclosed, inferInstance⟩
    · rw [s.range_immersion]
      exact hj C
    · intro k hk
      by_contra hne
      exact Set.disjoint_left.mp (s.pairwise_disjoint_stratum hne)
        ((s.range_immersion k) ▸ hk) (hj C)
  · intro x
    let C : irreducibleComponents X :=
      ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
    have hηU : η C ∈ (⨆ D, W D : X.Opens) :=
      TopologicalSpace.Opens.mem_iSup.mpr ⟨C, hηW C⟩
    have hCU : C.val ⊆ closure ((⨆ D, W D : X.Opens) : Set X) := by
      rw [← (hη C).def]
      exact closure_mono (Set.singleton_subset_iff.mpr hηU)
    exact hCU mem_irreducibleComponent
  · intro C
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨C, hηW C⟩

end AlgebraicGeometry.Scheme
