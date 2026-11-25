/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.IsSeparatedOfSurjectiveUniversallyClosed
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Closed subsets proper over a base: structures, subsets, and images

Source: Stacks Project, Cohomology of Schemes, Lemmas 0CYL, 0CYN, and 0CYQ
(blueprint: lem-weil-pbc-closed-subset-proper-over-base-properties).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Closed subset properness is independent of the chosen closed subscheme structure,
passes to closed subsets, and is preserved by images under morphisms over the base.
Source: Stacks Project, Cohomology of Schemes, Lemmas 0CYL, 0CYN, and 0CYQ.
(blueprint: lem-weil-pbc-closed-subset-proper-over-base-properties)

Proof:
1. Put `R = Z_red`, with its canonical closed immersion `i : R ⟶ X` and image `Z`.
   For any closed immersion `i'` with image `Z`, the reduced-source kernel criterion
   `IdealSheafData.le_ker_iff_range_subset_support` and the closed-immersion lifting
   property give `a : R ⟶ Z'` with `a ≫ i' = i` (Stacks Tag 0356).
2. The factor `a` is a closed immersion because its composite with `i'` is one.
   It is surjective because `i` and `i'` have the same image and `i'` is injective.
   If `R ⟶ S` is proper, separatedness descends along `a` by Tag 09MQ (4),
   and universal closedness by Tag 03GN. Local finite type follows by composition.
   Conversely, properness of `Z' ⟶ S` implies properness of `R ⟶ S` by composition
   with the proper closed immersion `a`. This proves both structure equivalences.
3. For `Y ≤ Z`, the reduced structure on `Y` factors into `R` by the same kernel
   criterion. The factor is a closed immersion, so its composite to `S` is proper.
4. For the image assertion, `h = i ≫ g` is proper because its composite with the
   separated map `f'` is proper. Its range is closed and equals `g '' Z`.
   The source of `h` is reduced, so its kernel is the vanishing ideal of this range.
   Thus its scheme-theoretic image is the reduced induced structure of that range,
   and `isProper_imageι_comp` (Tag 0AH6) proves it proper over `S`.
-/
theorem closed_subset_proper_over_base_properties
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (Z : TopologicalSpace.Closeds X) :
    (IsClosedSubsetProperOver f Z ↔
        ∃ (Z' : Scheme.{u}) (i' : Z' ⟶ X) (_ : IsClosedImmersion i'),
          Set.range i'.base = (Z : Set X) ∧ IsProper (i' ≫ f)) ∧
    (IsClosedSubsetProperOver f Z ↔
      ∀ (Z' : Scheme.{u}) (i' : Z' ⟶ X) [IsClosedImmersion i'],
        Set.range i'.base = (Z : Set X) → IsProper (i' ≫ f)) ∧
    (∀ (Y : TopologicalSpace.Closeds X), Y ≤ Z →
      IsClosedSubsetProperOver f Z → IsClosedSubsetProperOver f Y) ∧
    (∀ {X' : Scheme.{u}} (g : X ⟶ X') (f' : X' ⟶ S)
      [LocallyOfFiniteType f'] [IsSeparated f'],
      g ≫ f' = f → IsClosedSubsetProperOver f Z →
      ∃ W : TopologicalSpace.Closeds X',
        (W : Set X') = g '' (Z : Set X) ∧ IsClosedSubsetProperOver f' W) := by
  classical
  let R := (IdealSheafData.vanishingIdeal Z).subscheme
  let i : R ⟶ X := (IdealSheafData.vanishingIdeal Z).subschemeι
  have hi : Set.range i.base = (Z : Set X) := by
    change Set.range (IdealSheafData.vanishingIdeal Z).subschemeι = _
    rw [IdealSheafData.range_subschemeι, IdealSheafData.coe_support_vanishingIdeal]
  have factor (Z' : Scheme.{u}) (i' : Z' ⟶ X) [IsClosedImmersion i']
      (hr : Set.range i'.base = (Z : Set X)) :
      ∃ a : R ⟶ Z', a ≫ i' = i := by
    have hk : i'.ker ≤ i.ker := by
      rw [IdealSheafData.le_ker_iff_range_subset_support]
      simpa [i'.support_ker, hr] using Set.Subset.trans hi.le subset_closure
    exact ⟨IsClosedImmersion.lift i' i hk, IsClosedImmersion.lift_fac _ _ _⟩
  have proper_iff (Z' : Scheme.{u}) (i' : Z' ⟶ X) [IsClosedImmersion i']
      (hr : Set.range i'.base = (Z : Set X)) :
      IsClosedSubsetProperOver f Z ↔ IsProper (i' ≫ f) := by
    obtain ⟨a, ha⟩ := factor Z' i' hr
    have : IsClosedImmersion (a ≫ i') := by rw [ha]; infer_instance
    have : IsClosedImmersion a := IsClosedImmersion.of_comp_isClosedImmersion a i'
    have has : Surjective a := by
      constructor
      intro z
      have hz : i' z ∈ Set.range i.base := by
        rw [hi, ← hr]
        exact Set.mem_range_self z
      obtain ⟨r, hri⟩ := hz
      refine ⟨r, i'.isClosedEmbedding.injective ?_⟩
      exact (congrArg (fun k : R ⟶ X ↦ k r) ha).trans hri
    have hac : a ≫ i' ≫ f = i ≫ f := by rw [← Category.assoc, ha]
    constructor
    · intro hp
      have : IsProper (i ≫ f) := hp
      have : IsProper (a ≫ i' ≫ f) := by rw [hac]; infer_instance
      have : IsSeparated (i' ≫ f) :=
        isSeparated_of_surjective_universallyClosed (i ≫ f) (i' ≫ f) a hac
      have : UniversallyClosed (i' ≫ f) :=
        UniversallyClosed.of_comp_surjective a (i' ≫ f)
      exact {}
    · intro hp
      have : IsProper (i' ≫ f) := hp
      change IsProper (i ≫ f)
      rw [← hac]
      infer_instance
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · intro hp
      exact ⟨R, i, inferInstance, hi, hp⟩
    · rintro ⟨Z', i', hci, hr, hp⟩
      exact (proper_iff Z' i' hr).mpr hp
  · constructor
    · intro hp Z' i' _ hr
      exact (proper_iff Z' i' hr).mp hp
    · intro hp
      exact hp R i hi
  · intro Y hYZ hp
    let j := (IdealSheafData.vanishingIdeal Y).subschemeι
    have hj : Set.range j.base = (Y : Set X) := by simp [j]
    have hk : i.ker ≤ j.ker := by
      rw [IdealSheafData.le_ker_iff_range_subset_support]
      simpa [i.support_ker, hi, hj] using Set.Subset.trans hYZ subset_closure
    let a := IsClosedImmersion.lift i j hk
    have ha : a ≫ i = j := IsClosedImmersion.lift_fac _ _ _
    have : IsClosedImmersion (a ≫ i) := by rw [ha]; infer_instance
    have : IsClosedImmersion a := IsClosedImmersion.of_comp_isClosedImmersion a i
    have : IsProper (i ≫ f) := hp
    change IsProper (j ≫ f)
    rw [← ha, Category.assoc]
    infer_instance
  · intro X' g f' _ _ hgf hp
    let h := i ≫ g
    have : IsProper (h ≫ f') := by
      change IsProper (i ≫ g ≫ f')
      rw [hgf]
      exact hp
    have : IsProper h := IsProper.of_comp h f'
    have himage : Set.range h.base = g '' (Z : Set X) := by
      change Set.range (i ≫ g).base = _
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hi]
    let W : TopologicalSpace.Closeds X' := ⟨Set.range h.base, h.isClosedMap.isClosed_range⟩
    have hW : (W : Set X') = g '' (Z : Set X) := himage
    have hker : h.ker = IdealSheafData.vanishingIdeal W := by
      rw [h.ker_eq_vanishingIdeal]
      congr 1
      apply TopologicalSpace.Closeds.ext
      exact h.isClosedMap.isClosed_range.closure_eq
    refine ⟨W, hW, ?_⟩
    have hpim := (isProper_imageι_comp h f').1
    change IsProper ((IdealSheafData.vanishingIdeal W).subschemeι ≫ f')
    rw [← hker]
    exact hpim

end AlgebraicGeometry.Scheme
