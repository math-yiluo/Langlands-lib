/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.ConstructibleSheaf.Refinement

@[expose] public section
universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry Scheme
namespace AlgebraicGeometry
/-- Extraction of a finite trivializing datum over the spectrum of a field.
Source: Stacks Project, Definition 03RU and the proof of Lemma 09Z6.
(blueprint: lem-weil-pbc-constructible-field-finite-separable-constant-step1) -/
theorem constructible_field_finite_separable_constant_datum
    (k : Type u) [Field k]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (G : Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ))
    (hG : Scheme.IsConstructibleEtaleModuleSheaf G) :
    ∃ d : LocallyConstantDatum G, ∀ i : d.cover.I₀,
      ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
        Nonempty ((G.over (d.cover.etalePrecoverageToEtale i)) ≅
          (constantSheaf
            ((Spec (CommRingCat.of k)).smallEtaleTopology.over
              (d.cover.etalePrecoverageToEtale i))
            (ModuleCat.{u + 1} Λ)).obj M) := by
  classical
  obtain ⟨S, hS⟩ := hG
  let x : Spec (CommRingCat.of k) := IsLocalRing.closedPoint k
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp
    (S.iUnion_stratum_eq_univ ▸ Set.mem_univ x)
  have hrange : Set.range (S.immersion j) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    rw [S.range_immersion j]
    exact Subsingleton.elim x y ▸ hj
  have : IsImmersion (S.immersion j) := S.isImmersion j
  have : IsFiniteLocallyConstantSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (S.immersion j)).obj G) :=
    (finite_locally_constant_module_values_iff _).1.mp (hS j)
  have : IsFiniteLocallyConstantSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝟙 (Spec (CommRingCat.of k)))).obj G) :=
    IsFiniteLocallyConstantSheaf.upperStar_of_range_subset
      (𝟙 (Spec (CommRingCat.of k))) (S.immersion j) (by rw [hrange]; exact Set.subset_univ _) G
  have hfinite : IsFiniteLocallyConstantSheaf G :=
    IsFiniteLocallyConstantSheaf.of_iso
      ((Etale.upperStarId (ModuleCat.{u + 1} Λ) (Spec (CommRingCat.of k))).app G)
  exact (finite_locally_constant_module_values_iff G).1.mpr hfinite
end AlgebraicGeometry
