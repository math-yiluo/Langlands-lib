/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase

import WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.ModuleSupportProperOverBase
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties

/-! # Proper support of finite structure direct images
Source: Stacks Project, Tags 09ZT, 056J and 0CYQ.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- The structure module of a finite scheme has proper direct-image support when
its composite to the base is proper.
Source: Stacks Project, Lemma 09ZT, the support condition in Remark 088F;
Morphisms Lemma 056J and Cohomology of Schemes Lemmas 0CYN and 0CYQ.

Proof: The finite direct image is coherent on locally Noetherian X, hence
quasi-coherent and finite type. Its support is closed by 056J. This support is
contained in the closed image of Y: outside the image there is an open neighborhood
with empty inverse image, and every section of the structure sheaf there is zero.
Consequently all germs there are zero. The full closed subset Y is proper over S,
and its image in the separated finite-type X is proper over S by 0CYQ. A closed
subset of that image is proper by 0CYN. This includes Y empty and the zero section
rings without a nonempty-fiber assumption.
(blueprint: lem-weil-pbc-finite-structure-proper-support). -/
theorem finite_structure_proper_support {Y X S : Scheme.{u}}
    (p : Y ⟶ X) (f : X ⟶ S) [IsFinite p] [IsLocallyNoetherian X]
    [IsSeparated f] [LocallyOfFiniteType f] [IsProper (p ≫ f)] :
    HasSupportProperOver f
      ((pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf)) := by
  classical
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  let F := (pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf)
  have hF : RingedSpace.IsCoherent X.toRingedSpace F :=
    (isCoherent_pushforward_of_isFinite p _
      (isCoherent_unit_of_finite_to_locallyNoetherian p)).1
  obtain ⟨hqc, hft⟩ := (isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp hF
  let := hqc
  let := hft
  obtain ⟨Z, hZ⟩ := (module_support_proper_over_base f F).1
  have htop : Scheme.IsClosedSubsetProperOver (p ≫ f) ⊤ :=
    (Scheme.closed_subset_proper_over_base_properties (p ≫ f) ⊤).1.mpr
      ⟨Y, 𝟙 Y, inferInstance, by ext x; simp, by simpa using
        (inferInstance : IsProper (p ≫ f))⟩
  obtain ⟨W, hW, hpW⟩ :=
    (Scheme.closed_subset_proper_over_base_properties (p ≫ f) ⊤).2.2.2
      p f rfl htop
  have hrange : (W : Set X) = Set.range p.base := by
    simpa using hW
  have hclosed : IsClosed (Set.range p.base) := p.isClosedMap.isClosed_range
  have hsub : Z ≤ W := by
    intro x hx
    change x ∈ (W : Set X)
    rw [hrange]
    by_contra hxn
    have hxF : ¬ Subsingleton (F.presheaf.stalk x) := by
      have hxZ : x ∈ (Z : Set X) := hx
      rw [hZ] at hxZ
      exact hxZ
    apply hxF
    let V : X.Opens := ⟨(Set.range p.base)ᶜ, hclosed.isOpen_compl⟩
    have hxV : x ∈ V := hxn
    have hzero (U : X.Opens) : p ⁻¹ᵁ (U ⊓ V) = ⊥ := by
      ext y
      change (p y ∈ U ∧ p y ∉ Set.range p.base) ↔ False
      exact ⟨fun h ↦ h.2 (Set.mem_range_self y), False.elim⟩
    have hsec (U : X.Opens) : Subsingleton Γ(F, U ⊓ V) := by
      change Subsingleton Γ(Y, p ⁻¹ᵁ (U ⊓ V))
      rw [hzero]
      infer_instance
    have hz (t : F.presheaf.stalk x) : t = 0 := by
      obtain ⟨U, hxU, t, rfl⟩ := F.presheaf.exists_germ_eq t
      let k : U ⊓ V ⟶ U := CategoryTheory.homOfLE inf_le_left
      have ht : F.presheaf.map k.op t = 0 := (hsec U).elim _ _
      rw [← F.presheaf.germ_res_apply k x ⟨hxU, hxV⟩ t, ht, map_zero]
    exact ⟨fun a b ↦ (hz a).trans (hz b).symm⟩
  exact ⟨Z, hZ, (Scheme.closed_subset_proper_over_base_properties f W).2.2.1 Z hsub hpW⟩

end AlgebraicGeometry.Scheme.Modules
