/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module
public import WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Quasi-finite separated morphisms are finite away from a closed subset

`AlgebraicGeometry.Scheme.Hom.exists_isFinite_morphismRestrict`: a quasi-compact, separated,
locally quasi-finite morphism of finite type over a qcqs base is finite over the complement of
the closed image of the boundary in a Zariski main theorem compactification. This is the first
step towards a stratification over which a quasi-compact étale morphism is finite, the input to
[Stacks 03SA] left open in
`AlgebraicGeometry.Scheme.isConstructibleSheaf_etaleLowerShriek_constantSheaf_of_stratification`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- **Quasi-finite separated morphisms are finite away from a closed subset.** Factor
`f = p ∘ j` with `j` a quasi-compact open immersion and `p` finite (Zariski's main theorem).
Over the complement `V` of the closed image `Z = p(T ∖ j(X))`, the preimage of `V` in `T` lies in
`j(X)`, so the restriction of `f` to `V` is that of `p`, hence finite. This is the first step of a
stratification of the base over which a quasi-compact étale morphism is finite. -/
theorem Hom.exists_isFinite_morphismRestrict {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyQuasiFinite f] [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f]
    [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (T : Scheme.{u}) (j : X ⟶ T) (p : T ⟶ S) (_ : IsOpenImmersion j) (_ : IsFinite p)
      (_ : j ≫ p = f) (V : S.Opens),
      (V : Set S) = (p.base '' (Set.range j.base)ᶜ)ᶜ ∧ IsFinite (f ∣_ V) := by
  obtain ⟨T, j, p, hj, -, hp, rfl⟩ := f.exists_isOpenImmersion_isFinite_of_locallyQuasiFinite
  have hZ : IsClosed (p.base '' (Set.range j.base)ᶜ) :=
    p.isClosedMap _ j.isOpenEmbedding.isOpen_range.isClosed_compl
  let V : S.Opens := ⟨_, hZ.isOpen_compl⟩
  refine ⟨T, j, p, hj, hp, rfl, V, rfl, ?_⟩
  rw [morphismRestrict_comp]
  have : IsIso (j ∣_ p ⁻¹ᵁ V) := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨inferInstance, ⟨fun y ↦ ?_⟩⟩
    have hy : y.1 ∈ Set.range j.base := by
      by_contra h
      exact y.2 ⟨y.1, h, rfl⟩
    obtain ⟨x, hx⟩ := hy
    refine ⟨⟨x, ?_⟩, Subtype.ext ?_⟩
    · change j.base x ∈ p ⁻¹ᵁ V
      rw [hx]
      exact y.2
    · rw [morphismRestrict_base_coe]
      exact hx
  infer_instance

end AlgebraicGeometry.Scheme
