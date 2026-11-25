/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.GenericFiniteness
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Finite étale charts of reduced schemes over a finite field

A nonempty reduced scheme `X` of finite type over a finite field `k₀` contains a nonempty open
`W` with a finite étale surjective morphism `W ⟶ O` onto an open `O` of an affine space `𝔸ᵈ`
over `k₀`: the smooth locus of `X` is dense (`k₀` being perfect), a smooth point has an étale
neighbourhood over `𝔸ᵈ`
(`AlgebraicGeometry.Scheme.Hom.exists_etale_to_affineSpace_of_mem_smoothLocus`), and an étale
morphism to an irreducible scheme is finite over a nonempty open
(`AlgebraicGeometry.Scheme.Hom.exists_isFinite_preimage_of_etale`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **Finite étale charts.** A nonempty reduced scheme `X` of finite type over a field `k₀`
with perfect `k₀` has a nonempty open `j : W ⟶ X` with a finite étale surjective morphism
`π : W ⟶ O` onto an open `O` of `𝔸ᵈ_{k₀}`, compatible with the structure morphisms. -/
theorem exists_isFinite_etale_to_affineSpace {k₀ : Type u} [Field k₀] [PerfectField k₀]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k₀)) [IsReduced X] [Nonempty X]
    [LocallyOfFiniteType f] :
    ∃ (W : Scheme.{u}) (j : W ⟶ X) (d : ℕ)
      (O : 𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k₀)).Opens) (π : W ⟶ O.toScheme),
      IsOpenImmersion j ∧ Nonempty W ∧ IsFinite π ∧ Etale π ∧ Surjective π ∧
      π ≫ O.ι ≫ 𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀) =
        j ≫ f := by
  obtain ⟨x, hx⟩ := f.dense_smoothLocus_of_perfectField.nonempty
  obtain ⟨d, U, V, hU, hV, -, hxV, hVU, e, he, hge⟩ :=
    f.exists_etale_to_affineSpace_of_mem_smoothLocus hx
  have : IsAffine V.toScheme := hV
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  let e' := e ≫ AffineSpace.map (ULift.{u} (Fin d)) U.ι
  have : Etale e' := inferInstance
  have : QuasiCompact e' := inferInstance
  have : IsSeparated e' := inferInstance
  obtain ⟨O, hO, hW, hfin⟩ := e'.exists_isFinite_preimage_of_etale
  set W := e' ⁻¹ᵁ O
  have : Nonempty W := hW.to_subtype
  have : IsFinite (e' ∣_ O) := hfin
  have hirr : IrreducibleSpace O.toScheme := by
    have : IsIrreducible (O : Set 𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k₀))) :=
      ⟨hO, (IrreducibleSpace.isIrreducible_univ _).isPreirreducible.open_subset O.isOpen
        (Set.subset_univ _)⟩
    exact Subtype.irreducibleSpace this
  have hsurj : Surjective (e' ∣_ O) := by
    refine ⟨fun y ↦ ?_⟩
    have hcl : IsClopen (Set.range (e' ∣_ O)) :=
      ⟨(e' ∣_ O).isClosedMap.isClosed_range, (e' ∣_ O).isOpenMap.isOpen_range⟩
    have : Set.range (e' ∣_ O) = Set.univ :=
      hcl.eq_univ (Set.range_nonempty _)
    exact (this.symm ▸ Set.mem_univ y : y ∈ Set.range (e' ∣_ O))
  refine ⟨W, W.ι ≫ V.ι, d, O, e' ∣_ O, inferInstance, inferInstance, inferInstance,
    inferInstance, hsurj, ?_⟩
  rw [reassoc_of% morphismRestrict_ι, Category.assoc]
  simp only [e', Category.assoc, AffineSpace.map_over]
  rw [reassoc_of% hge, Scheme.Hom.resLE_comp_ι]

end AlgebraicGeometry
