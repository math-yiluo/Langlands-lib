/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.ConstructibleSheaf.Refinement
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# The stratification attached to an open subset of a closed subscheme

Let `X` be a noetherian scheme, `ι : Z ⟶ X` a closed immersion and `V ⊆ Z` an open subset. The
three locally closed subsets `X ∖ Z`, `V` and `Z ∖ V` form a stratification of `X`
(`AlgebraicGeometry.Scheme.Stratification.ofClosedImmersionOpens`), with the open subscheme
`X ∖ Z`, the open subscheme `V` of `Z` and the reduced closed subscheme on `Z ∖ V` as schemes.
On a noetherian scheme every locally closed subset is constructible
(`IsLocallyClosed.isConstructible_of_noetherianSpace`).

-/

@[expose] public section

open CategoryTheory Topology

universe u

namespace AlgebraicGeometry.Scheme

variable {X Z : Scheme.{u}} (ι : Z ⟶ X) [IsClosedImmersion ι] (V : Z.Opens)

/-- The open complement `X ∖ Z` of a closed immersion `ι : Z ⟶ X`. -/
noncomputable def openComplementOfIsClosedImmersion : X.Opens :=
  ⟨(Set.range ι.base)ᶜ, ι.isClosedEmbedding.isClosed_range.isOpen_compl⟩

/-- The image of an open `V ⊆ Z` under a closed immersion is `ι(Z) ∖ ι(Z ∖ V)`. -/
lemma image_opens_eq (V : Z.Opens) :
    ι.base '' (V : Set Z) = Set.range ι.base \ ι.base '' (V : Set Z)ᶜ := by
  rw [← Set.image_univ, ← Set.image_sdiff ι.isClosedEmbedding.injective]
  simp

/-- The stratification `X = (X ∖ Z) ⊔ V ⊔ (Z ∖ V)` attached to a closed immersion `ι : Z ⟶ X`
of noetherian schemes and an open `V ⊆ Z`. -/
noncomputable def Stratification.ofClosedImmersionOpens [IsNoetherian X] :
    Stratification X where
  n := 3
  stratum := ![(Set.range ι.base)ᶜ, ι.base '' V, ι.base '' (V : Set Z)ᶜ]
  isLocallyClosed_stratum i := by
    fin_cases i
    · exact (ι.isClosedEmbedding.isClosed_range.isOpen_compl).isLocallyClosed
    · dsimp
      rw [image_opens_eq]
      exact ι.isClosedEmbedding.isClosed_range.isLocallyClosed.inter
        (ι.isClosedEmbedding.isClosedMap _ V.isOpen.isClosed_compl).isOpen_compl.isLocallyClosed
    · exact (ι.isClosedEmbedding.isClosedMap _ V.isOpen.isClosed_compl).isLocallyClosed
  isConstructible_stratum i := by
    fin_cases i
    · exact ι.isClosedEmbedding.isClosed_range.isOpen_compl.isConstructible_of_noetherianSpace
    · dsimp
      rw [image_opens_eq]
      exact ι.isClosedEmbedding.isClosed_range.isConstructible_of_noetherianSpace.sdiff
        (ι.isClosedEmbedding.isClosedMap _
          V.isOpen.isClosed_compl).isConstructible_of_noetherianSpace
    · exact (ι.isClosedEmbedding.isClosedMap _
        V.isOpen.isClosed_compl).isConstructible_of_noetherianSpace
  iUnion_stratum_eq_univ := by
    apply Set.eq_univ_of_forall
    intro x
    simp only [Set.mem_iUnion]
    by_cases hx : x ∈ Set.range ι.base
    · obtain ⟨z, rfl⟩ := hx
      by_cases hz : z ∈ V
      · exact ⟨1, by simpa using ⟨z, hz, rfl⟩⟩
      · exact ⟨2, by simpa using ⟨z, hz, rfl⟩⟩
    · exact ⟨0, by simpa using hx⟩
  pairwise_disjoint_stratum := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij <;>
      simp only [Function.onFun, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Fin.mk_one,
        Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val, Set.disjoint_left,
        Set.mem_compl_iff, Set.mem_range, not_exists, Set.mem_image, SetLike.mem_coe, not_and,
        not_forall, not_not, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
        ι.isClosedEmbedding.injective.eq_iff, exists_eq] <;>
      first | tauto | (intro a ha x hx h; subst h; contradiction)
  domain := ![(openComplementOfIsClosedImmersion ι).toScheme, V.toScheme,
    (IdealSheafData.vanishingIdeal ⟨(V : Set Z)ᶜ, V.isOpen.isClosed_compl⟩).subscheme]
  immersion i := match i with
    | 0 => (openComplementOfIsClosedImmersion ι).ι
    | 1 => V.ι ≫ ι
    | 2 => V.closedComplement ≫ ι
  isImmersion i := by fin_cases i <;> dsimp <;> infer_instance
  range_immersion i := by
    fin_cases i
    · simp [openComplementOfIsClosedImmersion]
    · simp [Set.range_comp]
    · simp [Set.range_comp]

end AlgebraicGeometry.Scheme
