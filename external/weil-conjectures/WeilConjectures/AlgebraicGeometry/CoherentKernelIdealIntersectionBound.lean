/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.AffineIdealIntersectionInclusion
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentAffineSectionsFinite
import Mathlib.RingTheory.Filtration
import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator

/-! # Bounding an intersection with a coherent multiplication kernel

Source: Stacks Project, Tag 01YA, applied to a quasi-coherent kernel.
(blueprint: lem-pc-coherent-kernel-ideal-intersection-bound)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- A high ideal multiple of a coherent source intersects its kernel only inside
any prescribed ideal multiple of the kernel.
Source: Stacks Project, Tag 01YA, the inclusion clause of Artin-Rees, as applied
in Tag 01YB to the kernel of tensor multiplication.
(blueprint: lem-pc-coherent-kernel-ideal-intersection-bound)

Proof: Coherence gives quasi-coherence and finite affine section modules. Apply
module Artin-Rees to the image of the kernel inclusion on every affine open.
Choose a finite affine subcover and let c be the maximum of its bounds. Set m=c+n.
For a cover member with bound k<=c, Artin-Rees identifies I^m F intersect K with
I^(m-k)(I^k F intersect K). Since m-k=n+(c-k), the latter is contained in I^n K.
The affine inclusion comparison transports this algebraic inclusion to every
subopen of a covering affine. For an arbitrary W, restrict a section in both
ranges to the cover W intersect U. These restrictions have preimages in I^n K.
The inclusion I^n K -> F is monic, so these preimages agree on overlaps by
naturality and injectivity; the sheaf axiom glues them to a preimage over W.
For the empty cover c=0 and the sheaf axiom handles the empty W. No coherence
of H or annihilation hypothesis is used, and powers zero are included. -/
theorem coherent_kernel_ideal_intersection_bound
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    (F H : X.Modules) (μ : F ⟶ H)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hK : (kernel μ).IsQuasicoherent) (n : ℕ) :
    ∃ m : ℕ, ∀ W : X.Opens,
      Set.range ((idealModuleProductι (idealSheafPower I.toModulesι m).2 F).app W) ∩
          Set.range ((kernel.ι μ).app W) ⊆
        Set.range ((idealModuleProductι (idealSheafPower I.toModulesι n).2
          (kernel μ) ≫ kernel.ι μ).app W) := by
  classical
  have hqc := (isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp hF
  have : F.IsQuasicoherent := hqc.1
  have : (kernel μ).IsQuasicoherent := hK
  have hlocal (U : X.affineOpens) : ∃ k : ℕ, ∀ t : ℕ, k ≤ t →
      I.ideal U ^ t • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1)) ⊓
        LinearMap.range ((kernel.ι μ).val.app (.op U.1)).hom =
      I.ideal U ^ (t - k) • (I.ideal U ^ k •
        (⊤ : Submodule Γ(X, U.1) Γ(F, U.1)) ⊓
          LinearMap.range ((kernel.ι μ).val.app (.op U.1)).hom) := by
    have := coherent_affine_sections_finite X F hF U.1 U.2
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
  refine ⟨c + n, ?_⟩
  intro W
  let j := idealModuleProductι (idealSheafPower I.toModulesι n).2 (kernel μ) ≫ kernel.ι μ
  have : Mono j := by
    have : Mono (idealModuleProductι (idealSheafPower I.toModulesι n).2 (kernel μ)) := by
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
      F.presheaf.map (homOfLE (hVW i)).op t ∈ Set.range (j.app (V i)) := by
    apply affine_ideal_intersection_inclusion F (kernel μ) (kernel.ι μ) I i.1
      (c + n) n _ (V i) inf_le_right
    · obtain ⟨z, hz⟩ := ht.1
      obtain ⟨y, hy⟩ := ht.2
      constructor
      · refine ⟨(idealModuleProduct (idealSheafPower I.toModulesι (c + n)).2 F).presheaf.map
          (homOfLE (hVW i)).op z, ?_⟩
        rw [Hom.app_presheaf_map, hz]
      · refine ⟨(kernel μ).presheaf.map (homOfLE (hVW i)).op y, ?_⟩
        rw [Hom.app_presheaf_map, hy]
    · have hc : k i.1 ≤ c := Finset.le_sup i.2
      rw [hk i.1 (c + n) (by omega)]
      rw [Submodule.map_smul'', Submodule.map_top]
      have he : c + n - k i.1 = n + (c - k i.1) := by omega
      rw [he, pow_add, Submodule.mul_smul]
      apply smul_mono_right
      apply le_trans (smul_mono_right _ inf_le_right)
      exact Submodule.smul_le_right
  let K := idealModuleProduct (idealSheafPower I.toModulesι n).2 (kernel μ)
  choose z hz using hlocalLift
  have hcompat : TopCat.Presheaf.IsCompatible K.presheaf V z := by
    intro i k
    have : Mono (j.val.app (.op (V i ⊓ V k))) :=
      (SheafOfModules.evaluation X.ringCatSheaf (.op (V i ⊓ V k))).map_mono j
    apply (ModuleCat.mono_iff_injective (j.val.app (.op (V i ⊓ V k)))).mp inferInstance
    change j.app (V i ⊓ V k) _ = j.app (V i ⊓ V k) _
    rw [Hom.app_presheaf_map, Hom.app_presheaf_map, hz i, hz k]
    change F.presheaf.map (homOfLE inf_le_left).op
        (F.presheaf.map (homOfLE (hVW i)).op t) =
      F.presheaf.map (homOfLE inf_le_right).op
        (F.presheaf.map (homOfLE (hVW k)).op t)
    simp only [presheaf_map_homOfLE_map_homOfLE]
  obtain ⟨w, hw, _⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨K.presheaf, K.isSheaf⟩
    V W (fun i ↦ homOfLE (hVW i)) hVcover z hcompat
  refine ⟨w, ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨F.presheaf, F.isSheaf⟩
    V W (fun i ↦ homOfLE (hVW i)) hVcover
  intro i
  rw [← Hom.app_presheaf_map, hw i, hz i]

end AlgebraicGeometry.Scheme.Modules
