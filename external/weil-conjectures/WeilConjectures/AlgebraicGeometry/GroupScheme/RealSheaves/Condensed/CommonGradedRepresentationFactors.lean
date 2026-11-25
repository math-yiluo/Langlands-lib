/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RepresentationTheory.Filtration
import WeilConjectures.RepresentationTheory.CompositionFactors
import WeilConjectures.AlgebraicGeometry.GroupScheme.RealSheaves.Condensed.FilteredRepresentationFactors

/-!
# Comparing representations with the same graded pieces

This is the common-refinement comparison in paragraph 3 of
`lemma-tensor-exterior-powers-filtered-representations--3`.
-/

@[expose] public section

set_option autoImplicit false

namespace RealSheaves.Condensed

universe u v w z

/-- Choose a composition series in every common graded piece. Refinement matches both sets of
composition factors with the same disjoint union; compose the two bijections and their factor
isomorphisms. Every irreducible subquotient occurs in a composition series, so these same
bijections also give both constituent inclusions.
Source: `lemma-tensor-exterior-powers-filtered-representations--3`, proof paragraph 3, comparison of
the two refinements (blueprint: lem-mg-common-graded-representation-factors).
-/
theorem commonGradedRepresentationFactors
    {k : Type u} [Field k] {W : Type w} [Group W]
    {V V' : Type v} [AddCommGroup V] [Module k V]
    [AddCommGroup V'] [Module k V']
    [FiniteDimensional k V] [FiniteDimensional k V']
    {ρ : Representation k W V} {σ : Representation k W V'}
    {ι : Type z} {X : ι → Type v}
    [∀ i, AddCommGroup (X i)] [∀ i, Module k (X i)]
    [∀ i, FiniteDimensional k (X i)]
    (τ : ∀ i, Representation k W (X i))
    (hρ : Representation.HasGradedPieces ρ (fun i ↦ Representation.EquivTo (τ i)))
    (hσ : Representation.HasGradedPieces σ (fun i ↦ Representation.EquivTo (τ i))) :
    (Representation.ConstituentsLE ρ σ ∧ Representation.ConstituentsLE σ ρ) ∧
      ∀ (c : ρ.CompositionSeries) (d : σ.CompositionSeries),
        ∃ e : Fin c.length ≃ Fin d.length,
          ∀ j, Nonempty ((c.factor j).Equiv (d.factor (e j))) := by
  classical
  let t := fun i ↦ ((τ i).exists_compositionSeries).some
  have hc (c : ρ.CompositionSeries) (d : σ.CompositionSeries) :
      ∃ e : Fin c.length ≃ Fin d.length,
        ∀ j, Nonempty ((c.factor j).Equiv (d.factor (e j))) := by
    obtain ⟨e, he⟩ := filteredRepresentationFactors τ hρ t c
    obtain ⟨f, hf⟩ := filteredRepresentationFactors τ hσ t d
    refine ⟨e.trans f.symm, fun j ↦ ⟨(he.1 j).some.trans ?_⟩⟩
    have h := (hf.1 (f.symm (e j))).some.symm
    rw [f.apply_symm_apply] at h
    exact h
  obtain ⟨c⟩ := ρ.exists_compositionSeries
  obtain ⟨d⟩ := σ.exists_compositionSeries
  obtain ⟨e, he⟩ := hc c d
  have hρσ : Representation.ConstituentsLE ρ σ := by
    intro U S hS
    obtain ⟨F, h0, hn, hF⟩ := c.exists_chain
    obtain ⟨i, hi⟩ := Subrepresentation.exists_equiv_of_isIrreducible_subquotient h0 hn hF hS
    obtain ⟨f, hf⟩ := Representation.CompositionSeries.jordanHolder
      (Representation.CompositionSeries.ofChain h0 hn hF) c
    exact ⟨_, _, d.isIrreducible_factor (e (f i)),
      ⟨hi.some.trans ((hf i).some.trans (he (f i)).some)⟩⟩
  have hσρ : Representation.ConstituentsLE σ ρ := by
    intro U S hS
    obtain ⟨F, h0, hn, hF⟩ := d.exists_chain
    obtain ⟨i, hi⟩ := Subrepresentation.exists_equiv_of_isIrreducible_subquotient h0 hn hF hS
    obtain ⟨f, hf⟩ := Representation.CompositionSeries.jordanHolder
      (Representation.CompositionSeries.ofChain h0 hn hF) d
    refine ⟨_, _, c.isIrreducible_factor (e.symm (f i)),
      ⟨hi.some.trans ((hf i).some.trans ?_)⟩⟩
    have h := (he (e.symm (f i))).some.symm
    rw [e.apply_symm_apply] at h
    exact h
  exact ⟨⟨hρσ, hσρ⟩, hc⟩

end RealSheaves.Condensed
