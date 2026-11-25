/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CechResolutionDoubleComplex
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
import WeilConjectures.CategoryTheory.InjectiveCechTotalSections
import WeilConjectures.CategoryTheory.ResolutionSectionCohomology

/-!
# Total cohomology of the Čech resolution double complex

Source: blueprint lemma-coherent-base-change-invertible-sheaves--1, Step 3; Stacks Project Tags 03AW
and 03F6.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Limits

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasFiniteWidePullbacks C] [HasSheafify J AddCommGrpCat.{v}]
  [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]

/-- The total Čech complex of an injective resolution computes sheaf cohomology.

Source: blueprint lemma-coherent-base-change-invertible-sheaves--1, Step 3, and
lem-sc-cech-spectral, Step 2; Stacks Project Tags 03AW and 03F6.
Proof: augment every Čech row by I^q(X), using restrictions of sections. The
sheaf condition identifies degree-zero row cohomology with I^q(X). Since I^q
is injective, positive row cohomology vanishes by injective Čech acyclicity
(03AW). To apply the chosen-product formulation, use the canonical
comparison with the Mathlib Čech complex: its degree maps come from the unique
projection-compatible isomorphisms of fibre products, and commute with the
alternating differential. Here the sheaf values and the Hom sets are in the same universe, so the
free abelian representables used in that proof have the required size.
Naturality of restriction in the differential I^q → I^(q+1) gives a chain map
from I(X) to the total complex. Filter its mapping cone by resolution degree.
Each row of the cone is exact by the augmented-row calculation. The augmentation
occupies Čech degree -1, so the cone is bounded below. In each total degree the
filtration is finite; its row spectral sequence is
zero, so the cone is acyclic. The augmentation is consequently a
quasi-isomorphism. Finally the sheafification/free-abelian Yoneda adjunction
identifies evaluation at X with Hom from the free abelian sheaf on X. Computing
Ext with I gives H^n(I(X)) ≅ F.H' n X. Compose this with the inverse of the
homology isomorphism of the augmentation.
(blueprint: lem-sc-cech-resolution-total) -/
theorem Sheaf.cechResolutionDoubleComplex_total
    {F : Sheaf J AddCommGrpCat.{v}} (I : InjectiveResolution F) (X : C)
    {ι : Type v} {U : ι → C} (π : ∀ i, U i ⟶ X)
    (hπ : Sieve.ofArrows U π ∈ J X) (n : ℕ) :
    Nonempty (((Sheaf.cechResolutionDoubleComplex I X π).total
      (ComplexShape.up ℕ)).homology n ≅ F.H' n X) := by
  obtain ⟨e⟩ := injective_cech_total_sections I.cocomplex
    (fun q ↦ inferInstance) X π hπ n
  obtain ⟨f⟩ := Sheaf.resolution_section_cohomology I X n
  exact ⟨e ≪≫ f⟩

end CategoryTheory
