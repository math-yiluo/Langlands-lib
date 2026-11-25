/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism

/-! # Transporting a finite open partition across a thickening

Source: Stacks Project Tag 04DF; step 2 of finite splitting closed immersion descent.
(blueprint: lem-weil-pbc-finite-open-partition-thickening-transport)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Transport a finite disjoint open covering across a surjective closed immersion.

Source: Stacks Project Tag 04DF; step 2 of
`lem-weil-pbc-finite-splitting-closed-immersion-descent`.
(blueprint: lem-weil-pbc-finite-open-partition-thickening-transport)

Proof: A surjective closed immersion induces a homeomorphism on points. Take
V_j to be the image of W_j under this homeomorphism. Injectivity and
surjectivity transport disjointness and the covering equality. The complement
of each V_j is the union of the other opens, so V_j is also closed. Its open
immersion into P is thus a closed immersion, hence finite. The preimage of
V_j under p is exactly W_j. Restricting p to these opens gives a_j; it is a
base change of p, up to the canonical open-subscheme isomorphism, hence a
surjective closed immersion. Its inclusion equation is the restriction
square. For n=0 the covering equality forces both spaces empty, and there
are no component assertions. -/
theorem exists_finite_open_partition_thickening_transport
    {P' P : Scheme.{u}} (p : P' ⟶ P) [IsClosedImmersion p] [Surjective p]
    (n : ℕ) (W : Fin n → P'.Opens)
    (hcover : (⨆ j, W j) = ⊤)
    (hdisj : Pairwise (fun j k ↦ Disjoint (W j) (W k))) :
    ∃ V : Fin n → P.Opens,
      (⨆ j, V j) = ⊤ ∧ Pairwise (fun j k ↦ Disjoint (V j) (V k)) ∧
      ∀ j, IsFinite (V j).ι ∧
        ∃ a : (W j).toScheme ⟶ (V j).toScheme,
          IsClosedImmersion a ∧ Surjective a ∧ a ≫ (V j).ι = (W j).ι ≫ p := by
  classical
  let e := (IsUniversalHomeomorphism.homeomorph p).opensCongr
  let V : Fin n → P.Opens := fun j ↦ e (W j)
  have hVcover : (⨆ j, V j) = ⊤ := by
    change (⨆ j, e (W j)) = ⊤
    rw [← e.map_iSup, hcover, e.map_top]
  have hVdisj : Pairwise (fun j k ↦ Disjoint (V j) (V k)) := by
    intro j k hjk
    rw [disjoint_iff, ← e.map_inf, (hdisj hjk).eq_bot, e.map_bot]
  refine ⟨V, hVcover, hVdisj, fun j ↦ ?_⟩
  have hclosed : IsClosed (V j : Set P) := by
    have hcompl : (V j : Set P)ᶜ = ⋃ k : {k : Fin n // k ≠ j}, (V k : Set P) := by
      ext x
      constructor
      · intro hx
        have hxcover : x ∈ ⨆ k, V k := by rw [hVcover]; trivial
        obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hxcover
        exact Set.mem_iUnion.mpr ⟨⟨k, fun hkj ↦ hx (hkj ▸ hk)⟩, hk⟩
      · intro hx
        obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
        intro hxj
        exact (Set.disjoint_left.mp (TopologicalSpace.Opens.coe_disjoint.mpr (hVdisj k.2))) hk hxj
    rw [← isOpen_compl_iff, hcompl]
    exact isOpen_iUnion (fun k ↦ (V k).isOpen)
  have : IsClosedImmersion (V j).ι :=
    IsClosedImmersion.of_isPreimmersion _ (by simpa using hclosed)
  have hpre : W j = p ⁻¹ᵁ V j := by
    ext x
    change x ∈ W j ↔ p x ∈ V j
    change x ∈ W j ↔
      (IsUniversalHomeomorphism.homeomorph p).symm
        (IsUniversalHomeomorphism.homeomorph p x) ∈ W j
    rw [Homeomorph.symm_apply_apply]
  let a := (P'.isoOfEq hpre).hom ≫ (p ∣_ V j)
  have : Surjective (p ∣_ V j) := by
    constructor
    intro x
    obtain ⟨y, hy⟩ := p.surjective x.1
    refine ⟨⟨y, ?_⟩, ?_⟩
    · change p y ∈ V j
      rw [hy]
      exact x.2
    · apply Subtype.ext
      simpa only [morphismRestrict_base_coe] using hy
  refine ⟨inferInstance, a, inferInstance, inferInstance, ?_⟩
  dsimp [a]
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, isoOfEq_hom_ι]


end AlgebraicGeometry.Scheme
