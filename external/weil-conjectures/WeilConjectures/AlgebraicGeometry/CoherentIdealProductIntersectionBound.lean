/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian

import WeilConjectures.AlgebraicGeometry.AffineIdealIntersectionInclusion
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentAffineSectionsFinite
import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
import Mathlib.RingTheory.Filtration

/-! # A uniform ideal-product intersection bound

Source: Stacks Project, Tag 01YA, the inclusion clause of coherent Artin-Rees.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- A sufficiently high ideal multiple intersects a quasi-coherent submodule
only inside a prescribed ideal multiple of that submodule.

Source: Stacks Project, Tag 01YA, inclusion clause of Artin-Rees.
(blueprint: lem-pc-coherent-ideal-product-intersection-bound)

Proof: On each affine open of X, H has a finite module of sections over a
Noetherian ring. Apply algebraic Artin-Rees to the image of a there. Choose a
finite affine cover, take c to be the maximum of its Artin-Rees constants, and
set k = c + r. On a cover member with constant d <= c the intersection
I^k H intersect T equals I^(k-d)(I^d H intersect T), which is contained in
I^(k-d) T and therefore in I^r T since k-d >= r. The affine multiplication
image formula identifies these algebraic products with the recursive ideal
products, including exponent zero. Localization gives the same range inclusion
on subopens of every cover member. For an arbitrary open W, restrict a section
in both ranges to its intersections with the affine cover. The resulting
preimages in I^r T agree on overlaps because the composite I^r T -> T -> H is
mono. Glue them using the sheaf axiom to obtain the asserted preimage on W.
For an empty scheme use c = 0 and the empty-cover sheaf axiom. When r = 0 the
right-hand product is the whole submodule. Zero and unit ideals, and T = 0,
are covered by the same algebraic Artin-Rees argument. No coherence of T and
no annihilation or complementary-open hypothesis are needed. -/
theorem coherent_ideal_product_intersection_bound
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    (H T : X.Modules) (hH : RingedSpace.IsCoherent X.toRingedSpace H)
    (a : T ⟶ H) [Mono a] (hT : T.IsQuasicoherent) (r : ℕ) :
    ∃ k : ℕ, ∀ W : X.Opens,
      Set.range ((idealModuleProductι (idealSheafPower I.toModulesι k).2 H).app W) ∩
          Set.range (a.app W) ⊆
        Set.range ((idealModuleProductι (idealSheafPower I.toModulesι r).2 T ≫
          a).app W) := by
  classical
  have hqc := (isCoherent_iff_isQuasicoherent_and_isFiniteType X H).mp hH
  have : H.IsQuasicoherent := hqc.1
  have : T.IsQuasicoherent := hT
  have hlocal (U : X.affineOpens) : ∃ k : ℕ, ∀ t : ℕ, k ≤ t →
      I.ideal U ^ t • (⊤ : Submodule Γ(X, U.1) Γ(H, U.1)) ⊓
        LinearMap.range (a.val.app (.op U.1)).hom =
      I.ideal U ^ (t - k) • (I.ideal U ^ k •
        (⊤ : Submodule Γ(X, U.1) Γ(H, U.1)) ⊓
          LinearMap.range (a.val.app (.op U.1)).hom) := by
    have := coherent_affine_sections_finite X H hH U.1 U.2
    have := IsLocallyNoetherian.component_noetherian U
    exact Ideal.exists_pow_inf_eq_pow_smul (I.ideal U) _
  choose k hk using hlocal
  have hcover : (Set.univ : Set X) ⊆ ⋃ U : X.affineOpens, (U.1 : Set X) := by
    intro x _
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hxU⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens ↦ (U.1 : Set X)) (fun U ↦ U.1.2) hcover
  let c := s.sup k
  refine ⟨c + r, ?_⟩
  intro W
  let j := idealModuleProductι (idealSheafPower I.toModulesι r).2 T ≫ a
  have : Mono j := by
    have : Mono (idealModuleProductι (idealSheafPower I.toModulesι r).2 T) := by
      dsimp [idealModuleProductι]
      infer_instance
    dsimp only [j]
    infer_instance
  let V : s → X.Opens := fun i ↦ W ⊓ i.1.1
  have hVW : ∀ i, V i ≤ W := fun _ ↦ inf_le_left
  have hVcover : W ≤ ⨆ i, V i := by
    intro x hx
    obtain ⟨U, hxU⟩ := Set.mem_iUnion.mp (hs (Set.mem_univ x))
    obtain ⟨hUs, hxU⟩ := Set.mem_iUnion.mp hxU
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, hUs⟩, hx, hxU⟩
  intro t ht
  have hlocalLift (i : s) :
      H.presheaf.map (homOfLE (hVW i)).op t ∈ Set.range (j.app (V i)) := by
    apply affine_ideal_intersection_inclusion H T a I i.1
      (c + r) r _ (V i) inf_le_right
    · obtain ⟨z, hz⟩ := ht.1
      obtain ⟨y, hy⟩ := ht.2
      constructor
      · refine ⟨(idealModuleProduct (idealSheafPower I.toModulesι (c + r)).2 H).presheaf.map
          (homOfLE (hVW i)).op z, ?_⟩
        rw [Hom.app_presheaf_map, hz]
      · refine ⟨T.presheaf.map (homOfLE (hVW i)).op y, ?_⟩
        rw [Hom.app_presheaf_map, hy]
    · have hc : k i.1 ≤ c := Finset.le_sup i.2
      rw [hk i.1 (c + r) (by omega)]
      rw [Submodule.map_smul'', Submodule.map_top]
      have he : c + r - k i.1 = r + (c - k i.1) := by omega
      rw [he, pow_add, Submodule.mul_smul]
      apply smul_mono_right
      apply le_trans (smul_mono_right _ inf_le_right)
      exact Submodule.smul_le_right
  let K := idealModuleProduct (idealSheafPower I.toModulesι r).2 T
  choose z hz using hlocalLift
  have hcompat : TopCat.Presheaf.IsCompatible K.presheaf V z := by
    intro i k
    have : Mono (j.val.app (.op (V i ⊓ V k))) :=
      (SheafOfModules.evaluation X.ringCatSheaf (.op (V i ⊓ V k))).map_mono j
    apply (ModuleCat.mono_iff_injective (j.val.app (.op (V i ⊓ V k)))).mp inferInstance
    change j.app (V i ⊓ V k) _ = j.app (V i ⊓ V k) _
    rw [Hom.app_presheaf_map, Hom.app_presheaf_map, hz i, hz k]
    change H.presheaf.map (homOfLE inf_le_left).op
        (H.presheaf.map (homOfLE (hVW i)).op t) =
      H.presheaf.map (homOfLE inf_le_right).op
        (H.presheaf.map (homOfLE (hVW k)).op t)
    simp only [presheaf_map_homOfLE_map_homOfLE]
  obtain ⟨w, hw, _⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨K.presheaf, K.isSheaf⟩
    V W (fun i ↦ homOfLE (hVW i)) hVcover z hcompat
  refine ⟨w, ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨H.presheaf, H.isSheaf⟩
    V W (fun i ↦ homOfLE (hVW i)) hVcover
  intro i
  rw [← Hom.app_presheaf_map, hw i, hz i]


end AlgebraicGeometry.Scheme.Modules
