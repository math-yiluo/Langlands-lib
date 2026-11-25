/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting

/-!
# Exactness of module sheaves from sections on a basis

## References

* Stacks Project, Modules, Section 01AF and Lemma 01AG
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- Sectionwise short exactness on a basis gives a complex, monicity, epicity and
exactness of the corresponding module sheaves.
-/
theorem exactness_of_basis_sections
    (X : Scheme.{u}) (B : Set X.Opens) (hB : Opens.IsBasis B)
    (F G H : X.Modules) (i : F ⟶ G) (q : G ⟶ H)
    (hsections : ∀ U ∈ B,
      Function.Injective (i.val.app (op U)) ∧
      Function.Exact (i.val.app (op U)) (q.val.app (op U)) ∧
      Function.Surjective (q.val.app (op U))) :
    (i ≫ q = 0) ∧ Mono i ∧ Epi q ∧
      (∀ h : i ≫ q = 0, (ShortComplex.mk i q h).Exact) := by
  classical
  have hcover (W : X.Opens) :
      (⨆ U : {U : X.Opens // U ∈ B ∧ U ≤ W}, U.val) = W := by
    apply le_antisymm
    · exact iSup_le fun U ↦ U.property.2
    · intro x hx
      obtain ⟨U, hUB, hxU, hUW⟩ := Opens.isBasis_iff_nbhd.mp hB hx
      exact Opens.mem_iSup.mpr ⟨⟨U, hUB, hUW⟩, hxU⟩
  have hnat {K L : X.Modules} (φ : K ⟶ L) (V W : X.Opens) (hVW : V ≤ W)
      (s : K.val.obj (op W)) :
      φ.val.app (op V) (K.val.map (homOfLE hVW).op s) =
        L.val.map (homOfLE hVW).op (φ.val.app (op W) s) := by
    exact ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE hVW).op) s
  have hsep (K : X.Modules) (W : X.Opens) (s t : K.val.obj (op W))
      (heq : ∀ (U : X.Opens) (hUB : U ∈ B) (hUW : U ≤ W),
        K.val.map (homOfLE hUW).op s = K.val.map (homOfLE hUW).op t) : s = t := by
    exact TopCat.Sheaf.eq_of_locally_eq' ⟨K.presheaf, K.isSheaf⟩
      (fun U : {U : X.Opens // U ∈ B ∧ U ≤ W} ↦ U.val) W
      (fun U ↦ homOfLE U.property.2) (le_of_eq (hcover W).symm) s t
      (fun U ↦ heq U.val U.property.1 U.property.2)
  have hcomp : i ≫ q = 0 := by
    ext W s
    change q.val.app (op W) (i.val.app (op W) s) = 0
    apply hsep H W
    intro U hUB hUW
    rw [← hnat, ← hnat]
    simpa using (hsections U hUB).2.1.apply_apply_eq_zero
      (F.val.map (homOfLE hUW).op s)
  have hinj (W : X.Opens) : Function.Injective (i.val.app (op W)) := by
    intro s t hst
    apply hsep F W s t
    intro U hUB hUW
    apply (hsections U hUB).1
    rw [hnat, hnat, hst]
  have hmono : Mono i := by
    constructor
    intro K a b hab
    ext W s
    apply hinj W
    exact congrArg (fun φ : K ⟶ G ↦ φ.val.app (op W) s) hab
  have hepi : Epi q := by
    apply ((RingedSpace.module_exactness_local_lifting X.toRingedSpace).2.1 G H q).2.mp
    intro W t
    let I := {U : X.Opens // U ∈ B ∧ U ≤ W}
    have hlift : ∀ U : I, ∃ g : G.val.obj (op U.val),
        q.val.app (op U.val) g = H.val.map (homOfLE U.property.2).op t := by
      intro U
      exact (hsections U.val U.property.1).2.2 _
    choose g hg using hlift
    exact ⟨I, fun U ↦ U.val, fun U ↦ U.property.2, g, hcover W, hg⟩
  refine ⟨hcomp, hmono, hepi, ?_⟩
  intro h
  apply ((RingedSpace.module_exactness_local_lifting X.toRingedSpace).2.2 F G H i q h).mpr
  intro W s hs
  let I := {U : X.Opens // U ∈ B ∧ U ≤ W}
  have hlift : ∀ U : I, ∃ f : F.val.obj (op U.val),
      i.val.app (op U.val) f = G.val.map (homOfLE U.property.2).op s := by
    intro U
    apply ((hsections U.val U.property.1).2.1 _).mp
    rw [hnat, hs]
    exact map_zero _
  choose f hf using hlift
  exact ⟨I, fun U ↦ U.val, fun U ↦ U.property.2, f, hcover W, hf⟩

end AlgebraicGeometry.Scheme.Modules
