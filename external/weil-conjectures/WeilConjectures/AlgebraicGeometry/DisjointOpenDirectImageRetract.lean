/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.CategoryTheory.Retract
import WeilConjectures.SixFunctors.Etale.LowerShriek.Proper

/-! # A disjoint open component gives a direct-image retract

Source: `lem-weil-pbc-finite-module-generic-reflection`, proof step 2,
the finite product of sections on disjoint pieces.
(blueprint: lem-weil-pbc-disjoint-open-direct-image-retract)
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The direct image of a component of a finite disjoint open partition is a retract
of the full direct image. No finite-morphism or local-constancy hypothesis is needed.

Source: `lem-weil-pbc-finite-module-generic-reflection`, proof step 2;
Stacks Project Tag 0A5D, the direct-factor argument refined for module coefficients.
(blueprint: lem-weil-pbc-disjoint-open-direct-image-retract)

Proof: The complement of W i is the union of the other opens, so W i is closed.
For its inclusion j, the comparison c from extension by zero j_! to direct image
j_* is therefore invertible. Put H = j^* F. Let L be j_! adjoint to j^* and R be
j^* adjoint to j_*. The comparison at H equals the composite of the counit of L
at F and the unit of R at F: transpose both sides under the two adjunctions;
the triangle identities and the comparison's characterization give the identity
on H. Consequently c inverse followed by L's counit is a section of R's unit.
This gives a retract of F onto j_* H. Apply f_* to the retract, and transport
through the composition isomorphism f_* j_* H isomorphic to (j followed by f)_* H.
If the ith piece is empty, the same adjunction argument applies to its zero sheaf.
An empty partition has no index i, so the assertion is vacuous in that case. -/
theorem nonempty_retract_lowerStar_of_disjoint_open_partition
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (n : ℕ) (W : Fin n → X.Opens) (hcover : (⨆ j, W j) = ⊤)
    (hdisjoint : Pairwise (fun j k ↦ Disjoint (W j) (W k)))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (i : Fin n) :
    Nonempty (Retract
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) ((W i).ι ≫ f)).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (W i).ι).obj F))
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F)) := by
  classical
  have hcompl : (W i : Set X)ᶜ = ⋃ j : {j : Fin n // j ≠ i}, (W j.1 : Set X) := by
    ext x
    constructor
    · intro hx
      have hx' : x ∈ (⨆ j, W j) := by rw [hcover]; trivial
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
      have hji : j ≠ i := by rintro rfl; exact hx hj
      exact Set.mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩
    · intro hx hi
      obtain ⟨⟨j, hji⟩, hj⟩ := Set.mem_iUnion.mp hx
      have hd := disjoint_iff.mp (hdisjoint hji)
      have hx : x ∈ W j ⊓ W i := ⟨hj, hi⟩
      rw [hd] at hx
      exact hx
  have hclosed : IsClosed (W i : Set X) := by
    rw [← isOpen_compl_iff, hcompl]
    exact isOpen_iUnion fun j ↦ (W j.1).isOpen
  let j := (W i).ι
  let A := ModuleCat.{u + 1} Λ
  let H := (Etale.upperStar A j).obj F
  let L := Etale.openImmersionLowerShriekUpperStarAdjunction A j
  let R := Etale.upperStarLowerStarAdjunction A j
  let c := (Etale.openImmersionLowerShriekToLowerStar A j).app H
  have hc : IsIso (Etale.openImmersionLowerShriekToLowerStar A j) :=
    Etale.isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range A j
      (by simpa [j, Scheme.Opens.range_ι] using hclosed)
  let := hc
  have hfac : L.counit.app F ≫ R.unit.app F = c := by
    apply Etale.openImmersionLowerShriek_lowerStar_hom_ext
    simp only [Functor.map_comp, Category.assoc]
    rw [← Category.assoc, L.right_triangle_components]
    dsimp only [Functor.comp_obj, Functor.id_obj]
    simp only [Category.id_comp]
    rw [R.left_triangle_components]
    exact (Etale.unit_map_openImmersionLowerShriekToLowerStar_app_counit A j H).symm
  let e : Retract ((Etale.lowerStar A j).obj H) F :=
    { i := inv c ≫ L.counit.app F
      r := R.unit.app F
      retract := by rw [Category.assoc, hfac, IsIso.inv_hom_id] }
  let ef := e.map (Etale.lowerStar A f)
  let q := (Etale.lowerStarComp A j f).app H
  refine ⟨{ i := q.inv ≫ ef.i, r := ef.r ≫ q.hom, retract := ?_ }⟩
  change (q.inv ≫ ef.i) ≫ (ef.r ≫ q.hom) = 𝟙 _
  rw [Category.assoc, ← Category.assoc ef.i, ef.retract, Category.id_comp,
    q.inv_hom_id]

end AlgebraicGeometry.Scheme
