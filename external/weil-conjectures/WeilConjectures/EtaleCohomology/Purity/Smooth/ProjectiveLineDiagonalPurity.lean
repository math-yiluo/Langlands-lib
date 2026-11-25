/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalPurity
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ProjectiveLineDiagonalIntegrals

/-!
# Purity for the diagonal of the projective line `ℙ(Option (ULift (Fin 1)); S)`

The model `ℙ(Option (ULift (Fin 1)); S)` of the projective line, used by the trace
`AlgebraicGeometry.Etale.projectiveLineTrace`, is smooth of relative dimension one and covered
by its two standard charts `𝔸¹_S ⟶ ℙ¹_S`. Hence its diagonal `ℙ¹_S ⟶ ℙ¹_S ×_S ℙ¹_S` is a
regular immersion of codimension one satisfying the purity hypothesis
(`AlgebraicGeometry.Etale.supportedTatePure_diagonal_of_cover`), and so is the diagonal
`ℙ¹_S ⟶ ℙ¹_{ℙ¹_S}` (`AlgebraicGeometry.ProjectiveSpace.diagonal`) for which the two diagonal
integrals are stated.

## Main statements

- `AlgebraicGeometry.Etale.isRegularImmersion_projectiveSpaceDiagonal_line`
- `AlgebraicGeometry.Etale.supportedTatePure_projectiveSpaceDiagonal_line`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace ProjectiveSpace

/-- The coordinates of a standard chart of `ℙ(Option (ULift (Fin 1)); S)` are indexed by a
singleton. -/
instance uniqueNeOption (i : Option (ULift.{u} (Fin 1))) :
    Unique {j : Option (ULift.{u} (Fin 1)) // j ≠ i} where
  default := ⟨i.elim (some ⟨0⟩) fun _ ↦ none, by cases i <;> simp⟩
  uniq := by
    rintro ⟨a, ha⟩
    refine Subtype.ext ?_
    rcases i with _ | ⟨⟨i, hi⟩⟩ <;> rcases a with _ | ⟨⟨a, ha'⟩⟩
    · exact absurd rfl ha
    · simp only [Option.elim_none, Option.some.injEq, ULift.up.injEq]
      exact Fin.ext (by omega)
    · rfl
    · exact absurd (by congr; omega) ha

/-- The projective line `ℙ(Option (ULift (Fin 1)); S) ⟶ S` is smooth of relative dimension one:
on the standard open `D₊(Tᵢ)` it is the affine line `𝔸¹_S`. -/
instance smoothOfRelativeDimension_one_option (S : Scheme.{u}) :
    SmoothOfRelativeDimension 1 (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S) := by
  refine smoothOfRelativeDimension_of_forall_exists_mem _ 1 fun y ↦ ?_
  have : y ∈ (⊤ : (ℙ(Option (ULift.{u} (Fin 1)); S)).Opens) := trivial
  rw [← ProjectiveSpace.iSup_standardOpen, TopologicalSpace.Opens.mem_iSup] at this
  obtain ⟨i, hi⟩ := this
  refine ⟨_, hi, ?_⟩
  rw [← ProjectiveSpace.standardOpenIso_hom_over]
  have h : Nat.card {j : Option (ULift.{u} (Fin 1)) // j ≠ i} = 1 := Nat.card_unique
  have := AffineSpace.smoothOfRelativeDimension_over {j : Option (ULift.{u} (Fin 1)) // j ≠ i} S
  rw [h] at this
  exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)

/-- The standard chart `𝔸¹_S ⟶ ℙ(Option (ULift (Fin 1)); S)` onto `D₊(Tᵢ)`. -/
noncomputable def optionChart (S : Scheme.{u}) (i : Option (ULift.{u} (Fin 1))) :
    𝔸(ULift.{u} (Fin 1); S) ⟶ ℙ(Option (ULift.{u} (Fin 1)); S) :=
  AffineSpace.reindex (fun _ : {j : Option (ULift.{u} (Fin 1)) // j ≠ i} ↦
      (⟨0⟩ : ULift.{u} (Fin 1))) S ≫
    (standardOpenIso (Option (ULift.{u} (Fin 1))) S i).inv ≫
      (standardOpen (Option (ULift.{u} (Fin 1))) S i).ι

/-- The standard charts are open immersions. -/
instance (S : Scheme.{u}) (i : Option (ULift.{u} (Fin 1))) : IsOpenImmersion (optionChart S i) := by
  rw [optionChart]
  infer_instance

/-- The standard charts are morphisms over `S`. -/
@[reassoc (attr := simp)]
lemma optionChart_over (S : Scheme.{u}) (i : Option (ULift.{u} (Fin 1))) :
    optionChart S i ≫ ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S = 𝔸(ULift.{u} (Fin 1); S) ↘ S := by
  rw [optionChart, Category.assoc, Category.assoc, standardOpenIso_inv_ι_over,
    AffineSpace.reindex_over]

/-- The two standard charts cover `ℙ(Option (ULift (Fin 1)); S)`. -/
lemma exists_optionChart_apply (S : Scheme.{u}) (x : ℙ(Option (ULift.{u} (Fin 1)); S)) :
    ∃ i y, (optionChart S i).base y = x := by
  have : x ∈ (⊤ : (ℙ(Option (ULift.{u} (Fin 1)); S)).Opens) := trivial
  rw [← ProjectiveSpace.iSup_standardOpen, TopologicalSpace.Opens.mem_iSup] at this
  obtain ⟨i, hi⟩ := this
  obtain ⟨z, rfl⟩ : x ∈ Set.range (standardOpen (Option (ULift.{u} (Fin 1))) S i).ι := by
    rwa [Scheme.Opens.range_ι]
  refine ⟨i, (inv (AffineSpace.reindex (fun _ : {j : Option (ULift.{u} (Fin 1)) // j ≠ i} ↦
      (⟨0⟩ : ULift.{u} (Fin 1))) S ≫
    (standardOpenIso (Option (ULift.{u} (Fin 1))) S i).inv)).base z, ?_⟩
  rw [optionChart, ← Category.assoc, ← Scheme.Hom.comp_apply, ← Category.assoc, IsIso.inv_hom_id,
    Category.id_comp]

end ProjectiveSpace

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] (S : Scheme.{u}) [HasInvertibleExponent Λ S]

/-- **Purity for the diagonal** `ℙ¹_S ⟶ ℙ¹_S ×_S ℙ¹_S` of the model
`ℙ(Option (ULift (Fin 1)); S)` of the projective line: it is covered by its two standard
charts. -/
theorem supportedTatePure_diagonal_projectiveSpace_line :
    haveI : HasInvertibleExponent Λ
        (pullback (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S) (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)) :=
      .of_hom (pullback.fst _ _ ≫ ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)
    SupportedTatePure Λ 1 (pullback.diagonal (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)) :=
  supportedTatePure_diagonal_of_cover Λ (ULift.{u} (Fin 1)) _ (ProjectiveSpace.optionChart S)
    (ProjectiveSpace.optionChart_over S) (ProjectiveSpace.exists_optionChart_apply S)

/-- The diagonal `ℙ¹_S ⟶ ℙ¹_{ℙ¹_S}` of the model `ℙ(Option (ULift (Fin 1)); S)` is a regular
immersion of codimension one. -/
instance isRegularImmersion_projectiveSpaceDiagonal_line :
    IsRegularImmersion 1 (ProjectiveSpace.diagonal (Option (ULift.{u} (Fin 1))) S) :=
  isRegularImmersion_projectiveSpaceDiagonal S

/-- **Purity for the diagonal** `ℙ¹_S ⟶ ℙ¹_{ℙ¹_S}` of the model `ℙ(Option (ULift (Fin 1)); S)`,
the hypothesis of the two diagonal integrals
(`AlgebraicGeometry.Etale.projectiveLineTrace_diagonal`). -/
theorem supportedTatePure_projectiveSpaceDiagonal_line :
    SupportedTatePure Λ 1 (ProjectiveSpace.diagonal (Option (ULift.{u} (Fin 1))) S) :=
  haveI : HasInvertibleExponent Λ
      (pullback (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S) (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)) :=
    .of_hom (pullback.fst _ _ ≫ ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)
  supportedTatePure_projectiveSpaceDiagonal Λ S
    (supportedTatePure_diagonal_projectiveSpace_line Λ S)

end Etale

end AlgebraicGeometry
