/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions

import WeilConjectures.AlgebraicGeometry.AffineFreeFiniteStalkGeneration
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleSurjectivityLocus
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleFiniteStalks
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparisonExtension
import WeilConjectures.AlgebraicGeometry.FreeEtaleModuleShriekComparison
import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekConstantConstructible
import WeilConjectures.Topology.SpectralConstructibleFiniteIntersection
import WeilConjectures.ConstructibleSheaf.Monoidal

/-!
# Finite affine free covers with zero cokernel

Source: Stacks Project, Tag 095N, finite selection in the constructible topology.
(blueprint: lem-weil-pbc-constructible-module-finite-zero-cokernel).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Finite affine free covers can be chosen with zero cokernel.

Proof plan (from Stacks Project, Tag 095N): represent the finitely many elements of each
finite geometric stalk by sections on pointed affine etale neighbourhoods, and map the
corresponding sheafified free modules to `F`.  The cokernel of each finite family is
constructible; its support is constructible, and enlarging a family shrinks that support.
Every point is omitted by one family.  Quasi-compactness of the constructible topology
gives finitely many families with empty intersection of supports.  Their concatenation has
zero geometric stalks in its cokernel, and conservativity of geometric stalks makes that
cokernel a zero object.
(blueprint: lem-weil-pbc-constructible-module-finite-zero-cokernel) -/
theorem exists_affine_free_etale_zero_cokernel
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleEtaleModuleSheaf F) :
    let P : X.Etale → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) := fun W =>
      (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ)
    ∃ (n : ℕ) (U : Fin n → X.Etale), (∀ i, IsAffine (U i).left) ∧
      ∃ g : (∐ fun i : Fin n => P (U i)) ⟶ F,
        Nonempty (IsZero (cokernel g)) := by
  classical
  let P : X.Etale → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) := fun W =>
    (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ)
  let I := Σ W : {W : X.Etale // IsAffine W.left}, P W.val ⟶ F
  let g (S : Finset I) : (∐ fun i : S => P i.val.1.val) ⟶ F :=
    Sigma.desc (fun i : S => i.val.2)
  let E (S : Finset I) : Set X := {x | ¬ Function.Surjective
    (((pointSmallEtale (X.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).map (g S))}
  have hP (W : X.Etale) (hW : IsAffine W.left) : IsConstructibleSheaf (P W) := by
    have : IsAffine W.left := hW
    obtain ⟨e⟩ := free_etale_module_shriek_comparison X Λ W
    have hc := isConstructibleEtaleModuleSheaf_etaleLowerShriek_constant
      (X := X) (U := W.left) W.hom (ModuleCat.of Λ Λ)
    have := (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp hc
    exact IsConstructibleSheaf.of_iso e.symm
  have hE (S : Finset I) : Topology.IsConstructible (E S) := by
    let e := (Fintype.equivFin S).symm
    let H : Fin (Fintype.card S) → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
      fun i => P (e i).val.1.val
    have : ∀ i : Fin (Fintype.card S), IsConstructibleSheaf (H i) :=
      fun i => hP _ (e i).val.1.property
    have := Abelian.hasFiniteBiproducts
      (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    have := IsConstructibleSheaf.biproduct H
    have := IsConstructibleSheaf.of_iso
      (biproduct.isoCoproduct H ≪≫ Sigma.reindex e (fun i : S => P i.val.1.val))
    exact isConstructible_module_stalk_nonsurjective _ F
      ((isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr inferInstance) hF (g S)
  have hEmpty : (⋂ S : Finset I, E S) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨S, hS⟩ := exists_finset_affine_free_stalk_surjective X Λ F x
      (constructibleModule_finite_geometric_stalk F hF _ (X.algClosurePoint x)).2
    exact Set.mem_iInter.mp hx S hS
  have : SpectralSpace X := {}
  obtain ⟨A, hA⟩ := finite_subfamily_iInter_eq_empty_of_isConstructible X
    (Finset I) E hE hEmpty
  let S : Finset I := A.biUnion id
  let e := Fintype.equivFin S
  let U : Fin (Fintype.card S) → X.Etale := fun i => (e.symm i).val.1.val
  let d : (∐ fun i : Fin (Fintype.card S) => P (U i)) ⟶ F :=
    (Sigma.reindex e.symm (fun i : S => P i.val.1.val)).hom ≫ g S
  have hd : Epi (g S) := by
    constructor
    intro Z a b hab
    apply sheafHom_ext_of_sheafFiber_map_algClosurePoint
    intro x
    obtain ⟨K, hK, hxK⟩ : ∃ K ∈ A, x ∉ E K := by
      by_contra hn
      have hx : x ∈ ⋂ K ∈ A, E K := by
        simp only [Set.mem_iInter]
        intro K hK
        by_contra hxK
        exact hn ⟨K, hK, hxK⟩
      rw [hA] at hx
      exact hx
    have hKS : K ⊆ S := fun i hi => Finset.mem_biUnion.mpr ⟨K, hK, hi⟩
    let t : (∐ fun i : K => P i.val.1.val) ⟶ (∐ fun i : S => P i.val.1.val) :=
      Sigma.desc (fun i : K => Sigma.ι (fun j : S => P j.val.1.val)
        ⟨i.val, hKS i.property⟩)
    have ht : t ≫ g S = g K := by
      apply Sigma.hom_ext
      intro i
      simp [t, g]
    let Q := (pointSmallEtale (X.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} Λ)
    have hsurj : Function.Surjective (Q.map (g K)) := not_not.mp hxK
    have : Epi (Q.map (g K)) := (ModuleCat.epi_iff_surjective _).mpr hsurj
    change Q.map a = Q.map b
    apply (cancel_epi (Q.map (g K))).mp
    rw [← ht, ← Q.map_comp, ← Q.map_comp, Category.assoc, Category.assoc, hab]
  have : Epi d := inferInstance
  exact ⟨Fintype.card S, U, fun i => (e.symm i).val.1.property,
    d, ⟨isZero_cokernel_of_epi d⟩⟩

end AlgebraicGeometry.Scheme
