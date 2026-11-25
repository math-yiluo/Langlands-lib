/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Homotopy
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.RingTheory.SimpleModule.InjectiveProjective
import WeilConjectures.CategoryTheory.SplitCategoryNullHomotopy

/-! # Contraction of a field complex onto its single cohomology

Source: blueprint lemma-coherent-base-change-invertible-sheaves--3, proof step 4, vector-space
splitting argument.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

private theorem projective_of_field {R : CommRingCat.{u}} (hR : IsField R)
    (M : (Spec R).Modules) : Projective M := by
  let := hR.toField
  have := isEquivalence_moduleSpecΓFunctor hR
  have := Module.projective_of_isSemisimpleRing R
    ((moduleSpecΓFunctor (R := R)).obj M)
  exact (moduleSpecΓFunctor (R := R)).projective_of_map_projective inferInstance

private theorem injective_of_field {R : CommRingCat.{u}} (hR : IsField R)
    (M : (Spec R).Modules) : Injective M := by
  let := hR.toField
  have := isEquivalence_moduleSpecΓFunctor hR
  have := Module.injective_of_isSemisimpleRing R
    ((moduleSpecΓFunctor (R := R)).obj M)
  apply (moduleSpecΓFunctor (R := R)).injective_of_map_injective
  exact Module.injective_object_of_injective_module R
    ((moduleSpecΓFunctor (R := R)).obj M)

/-- A complex of module sheaves on a field spectrum contracts onto its sole cohomology.

Source: blueprint lemma-coherent-base-change-invertible-sheaves--3, proof step 4, as recorded in
`lem-pc-finite-free-single-field-fibre`, proof step 2.
(blueprint: new-field-complex-single-cohomology).

Proof: The additive global-sections equivalence with R-vector spaces reflects
projective and injective objects. All vector spaces are projective and injective,
so all module sheaves on Spec R are as well. Split the homology quotient by
s : H^j(P) → Z^j(P), and extend its quotient map across the cycles inclusion
to r : P^j → H^j(P). The identities s π = id and inclusion r = π give
chain maps a : P → H^j(P)[-j] and b : H^j(P)[-j] → P.
The reverse composite b a is the identity. The composite a b induces identity
on degree-j homology, by cancelling the epimorphism π and the monomorphism
inclusion, and on all other homology, because those objects are zero.
Hence a b - id induces zero on all homology. Apply the split-category
null-homotopy lemma and convert its null homotopy to a homotopy from a b
to id. No boundedness, finite dimension, positive rank or nonzero homology
is needed. -/
theorem homotopyEquiv_single_cohomology_of_field
    {R : CommRingCat.{u}} (hR : IsField R)
    (P : CochainComplex (Spec R).Modules ℤ) (j : ℤ)
    (hzero : ∀ q : ℤ, q ≠ j → IsZero (P.homology q)) :
    Nonempty (HomotopyEquiv P
      ((CochainComplex.singleFunctor (Spec R).Modules j).obj (P.homology j))) := by
  classical
  have (M : (Spec R).Modules) : Projective M := projective_of_field hR M
  have (M : (Spec R).Modules) : Injective M := injective_of_field hR M
  let s := Projective.factorThru (𝟙 (P.homology j)) (P.homologyπ j)
  let r := Injective.factorThru (P.homologyπ j) (P.iCycles j)
  have hs : s ≫ P.homologyπ j = 𝟙 _ := by simp [s]
  have hr : P.iCycles j ≫ r = P.homologyπ j := by simp [r]
  let a := HomologicalComplex.mkHomToSingle r (fun i _ ↦ by
    rw [← P.toCycles_i i j, Category.assoc, hr, P.toCycles_comp_homologyπ])
  let b := HomologicalComplex.mkHomFromSingle (s ≫ P.iCycles j) (fun k _ ↦ by
    simp only [Category.assoc, P.iCycles_d, comp_zero])
  have hab : ∀ q : ℤ, HomologicalComplex.homologyMap (a ≫ b) q = 𝟙 _ := by
    intro q
    by_cases hq : q = j
    · subst q
      rw [← cancel_epi (P.homologyπ j), HomologicalComplex.homologyπ_naturality]
      have hc : HomologicalComplex.cyclesMap (a ≫ b) j =
          P.homologyπ j ≫ s := by
        rw [← cancel_mono (P.iCycles j), HomologicalComplex.cyclesMap_i]
        simp [a, b, Category.assoc, reassoc_of% hr]
      simp only [hc, Category.assoc, hs, Category.comp_id]
    · exact (hzero q hq).eq_of_src _ _
  obtain ⟨h⟩ := CochainComplex.nonempty_nullHomotopy_of_homologyMap_zero
    (a ≫ b - 𝟙 P) (fun q ↦ by
      rw [HomologicalComplex.homologyMap_sub, hab,
        HomologicalComplex.homologyMap_id, sub_self])
  refine ⟨⟨a, b, Homotopy.equivSubZero.symm h, Homotopy.ofEq ?_⟩⟩
  apply HomologicalComplex.Hom.ext
  funext q
  by_cases hq : q = j
  · subst q
    simp [a, b, Category.assoc, reassoc_of% hr, reassoc_of% hs]
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ q hq).eq_of_src _ _

end AlgebraicGeometry.Scheme.Modules
