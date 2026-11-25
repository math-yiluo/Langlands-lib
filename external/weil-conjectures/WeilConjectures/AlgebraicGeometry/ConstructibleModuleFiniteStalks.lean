/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
import WeilConjectures.AlgebraicGeometry.FieldPointFactorsThroughImmersion
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# Finite geometric stalks of constructible module sheaves

Source: Stacks Project, proof of Lemma 095N (line 12412 ff.), using Definitions 03RU and
03RW and Lemma 03Q1 (blueprint: lem-weil-pbc-constructible-module-finite-stalks).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- If a sheaf of modules on the small étale site is constructible, each geometric stalk is
finite, and hence finitely generated as a module over the finite coefficient ring.

Proof: choose the stratum containing the image of the geometric point and lift that point
through its immersion. The finite-value trivialization makes the stratum pullback finite
locally constant, so its stalk at the lifted point is finitely generated. The module-valued
pullback-stalk isomorphism transfers finite generation to the original stalk. A finitely
generated module over a finite ring is a finite set.

Source: Stacks Project, proof of Lemma 095N (line 12412 ff.), using Definitions 03RU and
03RW and Lemma 03Q1 (blueprint: lem-weil-pbc-constructible-module-finite-stalks).
-/
theorem constructibleModule_finite_geometric_stalk
    {T : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleEtaleModuleSheaf F)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ T) :
    Finite (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F) ∧
      Module.Finite Λ (((pointSmallEtale s).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).obj F) := by
  obtain ⟨S, hS⟩ := hF
  have ht : s.base (default : Spec (.of Ω)) ∈ ⋃ k, S.stratum k := by
    rw [S.iUnion_stratum_eq_univ]
    exact Set.mem_univ _
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp ht
  rw [← S.range_immersion k] at hk
  obtain ⟨z, hz⟩ := hk
  have : IsImmersion (S.immersion k) := S.isImmersion k
  obtain ⟨s', hs', _⟩ :=
    ((fieldPoint_factorsThrough_immersion (S.immersion k) z).2 Ω s hz.symm).1
  have hG := (finite_locally_constant_module_values_iff
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) (S.immersion k)).obj F)).1.mp (hS k)
  have hfin := hG.toIsFiniteSheaf.isFinitelyGenerated_sheafFiber Ω s'
  have e := (Etale.upperStarCompSheafFiberIso
    (ModuleCat.{u + 1} Λ) (S.immersion k) s').app F
  have hstalk := hfin.of_iso e
  rw [hs'] at hstalk
  have : Module.Finite Λ (((pointSmallEtale s).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).obj F) :=
    (ModuleCat.isFinitelyGenerated_iff _).mp hstalk
  exact ⟨Module.finite_of_finite Λ, inferInstance⟩

end AlgebraicGeometry.Scheme
