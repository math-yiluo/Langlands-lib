import Langlands.AlgebraicGeometry.PointTopology.SchemePointStratificationStatement

/-! # Support and factorization of scheme points along a closed stratum -/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- The support and factorization criteria for actual points of an arbitrary scheme along a
closed subscheme and its open complement, with disjointness over nonzero value rings and
coverage over local Artinian rings and fields (Conrad, Remark 3.3). -/
theorem schemePointStratification : SchemePointStratificationStatement.{u} := by
  intro R S _ _ _ X Z i _ p
  let U : X.left.Opens := i.left.ker.support.compl
  have hclosed : (i.left.ker.support : Set X.left) = Set.range i.left := by
    rw [Scheme.Hom.support_ker, i.left.isClosedEmbedding.isClosed_range.closure_eq]
  have hopen : (U : Set X.left) = (Set.range i.left)ᶜ := congrArg Set.compl hclosed
  let f : Spec (CommRingCat.of S) ⟶ X.left := p.left
  have hsupport : Set.range f ⊆ Set.range i.left ↔
      i.left.ker.comap f ≤ (Spec (CommRingCat.of S)).nilradical := by
    rw [← Scheme.IdealSheafData.vanishingIdeal_top,
      ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal,
      Scheme.IdealSheafData.support_comap, ← hclosed]
    change Set.range f ⊆ ↑i.left.ker.support ↔
      Set.univ ⊆ f ⁻¹' ↑i.left.ker.support
    constructor
    · intro h s _
      exact h ⟨s, rfl⟩
    · rintro h _ ⟨s, rfl⟩
      exact h (Set.mem_univ s)
  have hfactorClosed :
      (∃ z : RingPoint R Z S, z ≫ i = p) ↔ i.left.ker.comap p.left = ⊥ := by
    rw [← le_bot_iff, ← Scheme.IdealSheafData.le_map_iff_comap_le,
      Scheme.IdealSheafData.map_bot]
    constructor
    · rintro ⟨z, rfl⟩
      exact z.left.le_ker_comp i.left
    · intro h
      let z := IsClosedImmersion.lift i.left p.left h
      have hz : z ≫ i.left = p.left := IsClosedImmersion.lift_fac _ _ _
      refine ⟨Over.homMk z ?_, RingPoint.ext R hz⟩
      rw [← Over.w i, ← Category.assoc, hz]
      exact Over.w p
  have hfactorOpen : (∃ q : RingPoint R (openOver R X U) S, openPointMap R X S U q = p) ↔
      Set.range p.left ⊆ (Set.range i.left)ᶜ := by
    rw [← hopen]
    constructor
    · rintro ⟨q, rfl⟩
      exact (openPointEquiv R X S U q).property
    · intro h
      exact ⟨openPointLift R X S U p h, openPointMap_lift R X S U p h⟩
  have hcoverage [Subsingleton (PrimeSpectrum S)] [Nonempty (PrimeSpectrum S)] :
      Set.range p.left ⊆ Set.range i.left ∨
        ∃ q : RingPoint R (openOver R X U) S, openPointMap R X S U q = p := by
    let s : PrimeSpectrum S := Classical.choice inferInstance
    by_cases hs : p.left s ∈ Set.range i.left
    · left
      rintro _ ⟨t, rfl⟩
      rw [Subsingleton.elim (α := PrimeSpectrum S) t s]
      exact hs
    · right
      apply hfactorOpen.mpr
      rintro _ ⟨t, rfl⟩
      rw [Subsingleton.elim (α := PrimeSpectrum S) t s]
      exact hs
  refine ⟨hsupport, hfactorClosed, hfactorOpen, ?_, ?_, ?_⟩
  · intro hS h
    let s : PrimeSpectrum S := Classical.choice inferInstance
    obtain ⟨z, hz⟩ := h.1
    have hclosedPoint : p.left s ∈ Set.range i.left := by
      rw [← hz]
      exact ⟨z.left s, rfl⟩
    exact (hfactorOpen.mp h.2 ⟨s, rfl⟩) hclosedPoint
  · intro hlocal hartinian
    exact hcoverage
  · intro hfield
    let := hfield.toField
    refine hcoverage.imp (fun h ↦ hfactorClosed.mpr ?_) id
    have hJ := hsupport.mp h
    rw [Scheme.nilradical_eq_bot] at hJ
    exact le_bot_iff.mp hJ

end Langlands.AlgebraicGeometry.PointTopology
