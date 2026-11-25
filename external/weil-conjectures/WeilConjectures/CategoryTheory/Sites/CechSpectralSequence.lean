/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.ExactCouple.DoubleComplex
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

/-!
# The Čech-to-derived spectral sequence as the spectral sequence of a double complex

When abelian sheaves have enough injectives, the Čech-to-derived spectral sequence of a covering
is the first spectral sequence `HomologicalComplex₂.exists_spectralSequence` of the double
complex `CategoryTheory.Sheaf.exists_cechDoubleComplex`.

## Main statements

- `CategoryTheory.Sheaf.exists_cechToDerivedSpectralSequence_of_enoughInjectives`: the
  Čech-to-derived spectral sequence when abelian sheaves have enough injectives and all
  universes agree.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [HasFiniteWidePullbacks C]
  [HasSheafify J AddCommGrpCat.{v}]

/-- **The Čech-to-derived spectral sequence, with enough injectives.** The variant of
`Sheaf.exists_cechToDerivedSpectralSequence` where, instead of the site being essentially small,
abelian sheaves on `C` are assumed to have enough injectives, the covering is indexed by
`ι : Type v` and cohomology is computed in `AddCommGrpCat.{v}`.

It is the first spectral sequence of the double complex `Sheaf.exists_cechDoubleComplex`.

(blueprint: `lemma-coherent-base-change-invertible-sheaves--1`, `lem-sc-cech-spectral`) -/
theorem Sheaf.exists_cechToDerivedSpectralSequence_of_enoughInjectives
    [HasExt.{v} (Sheaf J AddCommGrpCat.{v})] [EnoughInjectives (Sheaf J AddCommGrpCat.{v})]
    (F : Sheaf J AddCommGrpCat.{v}) (X : C)
    {ι : Type v} {U : ι → C} (π : ∀ i, U i ⟶ X) (hπ : Sieve.ofArrows U π ∈ J X) :
    ∃ E : E₂CohomologicalSpectralSequenceNat AddCommGrpCat.{v},
      (∀ p q : ℕ, Nonempty ((E.page 2).X (p, q) ≅
        ((cechComplexFunctor fun i ↦ Over.mk (π i)).obj
          ((Over.forget X).op ⋙ F.cohomologyPresheaf q)).homology p)) ∧
      E.AbutsTo fun n ↦ F.H' n X := by
  obtain ⟨D, hcol, htot⟩ := F.exists_cechDoubleComplex X π hπ
  obtain ⟨E, hE₂, hE⟩ := D.exists_spectralSequence
  refine ⟨E, fun p q ↦ ?_, hE.of_iso fun n ↦ (htot n).some⟩
  obtain ⟨e⟩ := hE₂ p q
  exact ⟨e ≪≫ (HomologicalComplex.homologyFunctor _ _ p).mapIso (hcol q).some⟩

end CategoryTheory
