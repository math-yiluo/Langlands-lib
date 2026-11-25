/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.AlgebraicGeometry.AffineSpace.PolynomialMap
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line

/-!
# Sending a point of an open of the affine line to infinity

Let `U ⊆ 𝔸¹` be a nonempty open over a finite field `k₀`. There is a morphism
`H : U ⟶ ℙ¹_{k₀}` over `k₀`, quasi-finite, separated, of finite type and quasi-compact, which
is finite and étale over an open `W ∋ ∞` of `ℙ¹` with finite complement
(`AlgebraicGeometry.exists_toProjectiveLine_isFinite_etale_near_infinity`): it is
`x ↦ [1 : P(x)]` for a monic irreducible polynomial `P` whose zeros lie in `U`.

## Implementation details

Instead of a homography `τ` with `τ(s) = ∞` for a rational point `s`, which may need a
constant field extension, a closed point of `U` is sent to `∞` by a finite map which is étale
near `∞`.
-/

@[expose] public section

open CategoryTheory Polynomial

universe u

namespace AlgebraicGeometry

open affineLine ProjectiveLine in
/-- **A point of `U` sent to `∞` by a map finite and étale near `∞`.** Let `U` be a nonempty
open of the affine line over a finite field `k`, given by an open immersion
`j: U ⟶ 𝔸¹_k` over `k`. There are a morphism `H: U ⟶ ℙ¹_k` over `k` which is separated,
locally quasi-finite, locally of finite type and quasi-compact, and an open `W` of `ℙ¹_k`
containing `∞` (that is, `W` and the affine chart cover `ℙ¹_k`) with finite complement such that
`H` is finite and étale over `W`. -/
theorem exists_toProjectiveLine_isFinite_etale_near_infinity {k : Type u} [Field k] [Finite k]
    {U : Scheme.{u}} [U.Over (Spec (.of k))] [Nonempty U] (j : U ⟶ affineLine k)
    [IsOpenImmersion j] [j.IsOver (Spec (.of k))] :
    ∃ H : U ⟶ ProjectiveLine (Spec (.of k)), H.IsOver (Spec (.of k)) ∧ IsSeparated H ∧
      LocallyQuasiFinite H ∧ LocallyOfFiniteType H ∧ QuasiCompact H ∧
      ∃ W : (ProjectiveLine (Spec (.of k))).Opens,
        (affineChart (Spec (.of k))).opensRange ⊔ W = ⊤ ∧
        ((W : Set (ProjectiveLine (Spec (.of k))))ᶜ).Finite ∧
        IsFinite (H ∣_ W) ∧ Etale (H ∣_ W) := by
  obtain ⟨x⟩ := ‹Nonempty U›
  obtain ⟨P, _, V, hV0, hVf, hVj, hVet⟩ :=
    exists_isFinite_polynomialMap_etale j.opensRange ⟨j x, Set.mem_range_self x⟩
  have : IsLocallyNoetherian (affineLine k) :=
    LocallyOfFiniteType.isLocallyNoetherian (affineLine k ↘ Spec (.of k))
  have : IsLocallyNoetherian (ProjectiveLine (Spec (.of k))) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))
  have hcov (y : ProjectiveLine (Spec (.of k))) :
      y ∈ (affineChart (Spec (.of k))).opensRange ⊔ (infinityChart (Spec (.of k))).opensRange := by
    rw [opensRange_affineChart_sup_opensRange_infinityChart]
    trivial
  refine ⟨j ≫ polynomialMap P ≫ infinityChart _, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, infinityChart _ ''ᵁ V, ?_, ?_,
    (morphismRestrict_comp_comp_image_iff @IsFinite j _ _ hVj).mpr inferInstance,
    (morphismRestrict_comp_comp_image_iff @Etale j _ _ hVj).mpr hVet⟩
  · -- `∞` is the image of the origin, which lies in `V`
    rw [eq_top_iff]
    intro y _
    by_cases hy : y ∈ (affineChart _).opensRange
    · exact Or.inl hy
    obtain ⟨a, rfl⟩ := (hcov y).resolve_left hy
    have ha : a ∉ (affineLine k).basicOpen (AffineSpace.coord (Spec (.of k)) PUnit.unit) := by
      rw [← infinityChart_preimage_opensRange_affineChart]
      exact hy
    exact Or.inr ⟨a, (hV0.ge (Set.mem_univ a)).resolve_left ha, rfl⟩
  · -- outside `W` lie the image of the finite complement of `V` and the point `[0: 1]`
    refine (((finite_compl_basicOpen_coord k).image (affineChart _)).union
      (hVf.image (infinityChart _))).subset fun y hy ↦ ?_
    by_cases hy' : y ∈ (infinityChart _).opensRange
    · obtain ⟨a, rfl⟩ := hy'
      exact Or.inr ⟨a, fun ha ↦ hy ⟨a, ha, rfl⟩, rfl⟩
    · obtain ⟨b, rfl⟩ := (hcov y).resolve_right hy'
      refine Or.inl ⟨b, fun hb ↦ hy' ?_, rfl⟩
      rw [← affineChart_preimage_opensRange_infinityChart] at hb
      exact hb

end AlgebraicGeometry
