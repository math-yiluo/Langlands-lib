/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Homology.Homotopy

import WeilConjectures.AlgebraicGeometry.FieldComplexSingleCohomology
import Mathlib.Algebra.Homology.SingleHomology
import WeilConjectures.AlgebraicGeometry.Modules.FreeComplex
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules
private theorem negative_single_nonnegative_homology_zero
    {R : CommRingCat.{u}} (A : (Spec R).Modules) (q : ℕ) :
    IsZero (((CochainComplex.singleFunctor (Spec R).Modules (-1 : ℤ)).obj A).homology
      (q : ℤ)) := by
  exact CochainComplex.isZero_of_isLE _ (-1) q (by omega)

private theorem no_equiv_negative_single
    {R : CommRingCat.{u}} (A B : (Spec R).Modules) (hA : ¬ IsZero A) (i : ℕ) :
    ¬ Nonempty (HomotopyEquiv
      ((CochainComplex.singleFunctor (Spec R).Modules (-1 : ℤ)).obj A)
      ((CochainComplex.singleFunctor (Spec R).Modules (i : ℤ)).obj B)) := by
  rintro ⟨e⟩
  have hz := CochainComplex.isZero_of_isGE
    ((CochainComplex.singleFunctor (Spec R).Modules (i : ℤ)).obj B) i (-1) (by omega)
  have hz' := hz.of_iso (e.toHomologyIso (-1))
  exact hA (hz'.of_iso
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) (-1) A).symm)

private theorem counterexample_to_single_field_homology {R : CommRingCat.{u}} (hR : IsField R) :
    ∃ P : CochainComplex (Spec R).Modules ℤ,
      (∀ q : ℕ, q ≠ 0 → IsZero (P.homology (q : ℤ))) ∧
      (P.homology (0 : ℤ)).IsFiniteLocallyFreeOfRank 0 ∧
      ¬ Nonempty (HomotopyEquiv P
        ((CochainComplex.singleFunctor (Spec R).Modules (0 : ℤ)).obj
          (SheafOfModules.free (R := (Spec R).ringCatSheaf) (ULift.{u} (Fin 0))))) := by
  let := hR.toField
  let A := SheafOfModules.free (R := (Spec R).ringCatSheaf) (ULift.{u} (Fin 1))
  let P := (CochainComplex.singleFunctor (Spec R).Modules (-1 : ℤ)).obj A
  have hA := finrank_moduleSpecΓFunctor_obj_free hR (Iso.refl A)
  have : Module.Finite R ((moduleSpecΓFunctor (R := R)).obj A) := hA.2
  have hAnonzero : ¬ IsZero A := by
    intro hz
    have heq := (isZero_iff_finrank_moduleSpecΓFunctor_obj_eq_zero hR A).mp hz
    simp only [Fintype.card_ulift, Fintype.card_fin] at hA
    omega
  have hz : IsZero (P.homology (0 : ℤ)) :=
    negative_single_nonnegative_homology_zero A 0
  have hzΓ := (moduleSpecΓFunctor (R := R)).map_isZero hz
  have : Subsingleton ((moduleSpecΓFunctor (R := R)).obj (P.homology (0 : ℤ))) :=
    ModuleCat.subsingleton_of_isZero hzΓ
  have : Module.Finite R ((moduleSpecΓFunctor (R := R)).obj (P.homology (0 : ℤ))) :=
    inferInstance
  refine ⟨P, fun q _ ↦ negative_single_nonnegative_homology_zero A q, ?_, ?_⟩
  · apply (isFiniteLocallyFreeOfRank_iff_finrank_moduleSpecΓFunctor_obj hR _ 0).mpr
    exact Module.finrank_zero_of_subsingleton
  · exact no_equiv_negative_single A _ hAnonzero 0

private theorem nonempty_iso_free_of_field_rank
    {R : CommRingCat.{u}} (hR : IsField R) (M : (Spec R).Modules) (r : ℕ)
    (hrank : M.IsFiniteLocallyFreeOfRank r) :
    Nonempty (M ≅ SheafOfModules.free (R := (Spec R).ringCatSheaf)
      (ULift.{u} (Fin r))) := by
  let := hR.toField
  let := hrank
  obtain ⟨ι, U, hU, e⟩ := IsFiniteLocallyFreeOfRank.exists_restrict_iso_free M (r := r)
  obtain ⟨x⟩ : Nonempty (Spec R) := inferInstance
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1
    (hU.ge (Set.mem_univ x) : x ∈ ⨆ j, U j)
  have : Subsingleton (Spec (.of R)) := inferInstance
  have htop : U j = ⊤ := by
    refine eq_top_iff.2 fun y _ ↦ ?_
    rwa [Subsingleton.elim y x]
  have ej := e j
  rw [htop] at ej
  have : IsIso (⊤ : (Spec R).Opens).ι :=
    inferInstanceAs (IsIso (Spec R).topIso.hom)
  exact ⟨isoFreeOfRestrictIso M _ ej.some⟩

/-- Field-complex splitting into the sole finite locally free cohomology.
Source: blueprint lemma-coherent-base-change-invertible-sheaves--3, proof step 4.
(blueprint: new-field-complex-homotopy-normal-form).

Proof: Combine negative and nonnegative vanishing to obtain vanishing in all
integer degrees other than i. Contract the complex onto H^i(P) using
homotopyEquiv_single_cohomology_of_field. The rank-r locally free trivializing
cover of H^i(P) has a member containing the unique point of Spec R. That open is
top, so its inclusion is an isomorphism; isoFreeOfRestrictIso identifies H^i(P)
with the free sheaf of rank r. Apply the single functor to this isomorphism and
compose its homotopy equivalence with the contraction. The negative-degree
hypothesis is essential, as the retained counterexample to the old signature
shows; neither boundedness nor a positive rank is needed. -/
theorem homotopyEquiv_of_single_field_homology
    {R : CommRingCat.{u}} (hR : IsField R)
    (P : CochainComplex (Spec R).Modules ℤ)
    (i r : ℕ) (hzero : ∀ q : ℕ, q ≠ i → IsZero (P.homology q))
    (hnegative : ∀ q : ℤ, q < 0 → IsZero (P.homology q))
    (hrank : (P.homology i).IsFiniteLocallyFreeOfRank r) :
    Nonempty (HomotopyEquiv P
      ((CochainComplex.singleFunctor (Spec R).Modules (i : ℤ)).obj
        (SheafOfModules.free (R := (Spec R).ringCatSheaf) (ULift.{u} (Fin r))))) := by
  have hzeroInt : ∀ q : ℤ, q ≠ (i : ℤ) → IsZero (P.homology q) := by
    intro q hq
    by_cases hn : q < 0
    · exact hnegative q hn
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ q)
      exact hzero n (by exact_mod_cast hq)
  obtain ⟨e⟩ := homotopyEquiv_single_cohomology_of_field hR P (i : ℤ) hzeroInt
  obtain ⟨eH⟩ := nonempty_iso_free_of_field_rank hR (P.homology i) r hrank
  exact ⟨e.trans (HomotopyEquiv.ofIso
    ((CochainComplex.singleFunctor (Spec R).Modules (i : ℤ)).mapIso eH))⟩
end AlgebraicGeometry.Scheme.Modules
