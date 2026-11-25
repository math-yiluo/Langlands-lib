/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.InjectiveEtaleModuleCechH1
import WeilConjectures.AlgebraicGeometry.EtaleSectionsSurjectiveOfCechH1
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Degree-one abelian cohomology of injective module sheaves

Source: Stacks Project, Lemma 03FD
(blueprint: lem-weil-pbc-henselian-finite-pushforward-h1-injective-vanishing).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- An injective module sheaf has zero degree-one cohomology after forgetting scalars.

Source: Stacks Project, Lemma 03FD, especially the second paragraph of its proof.
(blueprint: lem-weil-pbc-henselian-finite-pushforward-h1-injective-vanishing)

Proof: Regard a sheaf of Λ-modules as a module over the constant ring sheaf Λ on the
small etale site. This equivalence preserves injectivity and the underlying abelian
sheaf. The proof of 03FD shows that every injective module sheaf is acyclic for abelian
section cohomology: the free module Cech complex is exact, so Hom into the injective
has zero positive cohomology; the Cech vanishing criterion applies to every cover.
Evaluate at the terminal etale object Y. The identification of this derived section
cohomology with Sheaf.H (Ext out of the constant integer sheaf) gives the conclusion.
No claim that the underlying abelian sheaf is itself injective is needed. -/
theorem subsingleton_H_one_of_injective_module_sheaf
    (Y : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective J] :
    Subsingleton (Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
      AddCommGrpCat.{u + 1})).obj J) 1) := by
  let F := (sheafCompose Y.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj J
  let T : Y.Etale := Scheme.Etale.mk (𝟙 Y)
  have hT : Limits.IsTerminal T := MorphismProperty.Over.mkIdTerminal _ Y
  apply Sheaf.subsingleton_H_one_of_surjective F hT
  intro E Q ι π w hS
  let S := ShortComplex.mk ι π w
  apply Scheme.surjective_sections_of_cech_h1_vanishing Y S hS T
    (fun I V f ↦ Sieve.ofArrows V f ∈ Y.smallEtaleTopology T)
  · intro I V f hf
    exact hf
  · intro I V f hf
    refine ⟨I, V, f, hf, ?_⟩
    intro i
    exact ⟨i, 𝟙 (V i), Category.id_comp _⟩
  · intro I V f hf
    exact Scheme.isZero_cech_H_one_of_injective_module_sheaf Y Λ J T V f hf

end AlgebraicGeometry.Etale
