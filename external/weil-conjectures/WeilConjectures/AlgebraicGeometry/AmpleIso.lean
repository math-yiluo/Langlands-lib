/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Ample

/-! # Ampleness is invariant under module isomorphisms

Source: Stacks Project, Properties, Definition 01PS.
(blueprint: lem-sc-ample-iso).
-/

@[expose] public section

universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private theorem stalk_map_smul {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (x : X) (r : X.presheaf.stalk x) (m : ↑(TopCat.Presheaf.stalk M.val.presheaf x)) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (f.mapPresheaf) (r • m) =
      r • (show ↑(TopCat.Presheaf.stalk N.val.presheaf x) from
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f.mapPresheaf m) := by
  obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨V, hxV, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf m
  have hx : x ∈ U ⊓ V := ⟨hxU, hxV⟩
  rw [← X.presheaf.germ_res_apply (homOfLE inf_le_left : U ⊓ V ⟶ U) x hx r,
    ← TopCat.Presheaf.germ_res_apply M.val.presheaf
      (homOfLE inf_le_right : U ⊓ V ⟶ V) x hx m,
    ← PresheafOfModules.germ_smul]
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
    TopCat.Presheaf.stalkFunctor_map_germ_apply]
  change TopCat.Presheaf.germ N.val.presheaf (U ⊓ V) x hx
      (f.app (U ⊓ V) (_ • _)) = _
  rw [Hom.app_smul, PresheafOfModules.germ_smul]
  rfl

private theorem nonvanishingLocus_iso {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (s : M.val.presheaf.obj (Opposite.op ⊤)) :
    nonvanishingLocus N (e.hom.app ⊤ s) = nonvanishingLocus M s := by
  ext y
  let F := toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y
  let a := F.mapIso e
  let f : ↑(TopCat.Presheaf.stalk M.val.presheaf y) →ₗ[X.presheaf.stalk y]
      ↑(TopCat.Presheaf.stalk N.val.presheaf y) :=
    { toFun := a.hom
      map_add' := map_add a.hom.hom
      map_smul' := stalk_map_smul e.hom y }
  let g : ↑(TopCat.Presheaf.stalk N.val.presheaf y) →ₗ[X.presheaf.stalk y]
      ↑(TopCat.Presheaf.stalk M.val.presheaf y) :=
    { toFun := a.inv
      map_add' := map_add a.inv.hom
      map_smul' := stalk_map_smul e.inv y }
  have hg : f (TopCat.Presheaf.germ M.val.presheaf ⊤ y trivial s) =
      TopCat.Presheaf.germ N.val.presheaf ⊤ y trivial (e.hom.app ⊤ s) := by
    exact TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ y trivial e.hom.mapPresheaf s
  have hi : ∀ m, g (f m) = m := by
    intro m
    exact ConcreteCategory.congr_hom a.hom_inv_id m
  have hf := Submodule.smul_top_le_comap_smul_top
    (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) f
  have hb := Submodule.smul_top_le_comap_smul_top
    (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) g
  change _ ∉ _ ↔ _ ∉ _
  rw [← hg]
  constructor
  · intro h hm
    exact h (hf hm)
  · intro h hm
    apply h
    have hh := hb hm
    change g (f (TopCat.Presheaf.germ M.val.presheaf ⊤ y trivial s)) ∈
      (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) •
        (⊤ : Submodule (X.presheaf.stalk y)
          ↑(TopCat.Presheaf.stalk M.val.presheaf y)) at hh
    rwa [hi] at hh

private theorem tensorPow_iso {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (n : ℕ) : Nonempty (M.tensorPow n ≅ N.tensorPow n) := by
  induction n with
  | zero => exact ⟨Iso.refl _⟩
  | succ n ih =>
    obtain ⟨a⟩ := ih
    exact ⟨MonoidalCategory.tensorIso e a⟩

/-- Isomorphic invertible modules have the same ampleness predicate.
Source: Stacks Project, Properties, Definition 01PS and Section 01PR.
(blueprint: lem-sc-ample-iso).

Proof: an isomorphism induces isomorphisms of every tensor power, compatible with
restriction and hence with germs. Use the inverse tensor-power isomorphism to
transport a global section of `N` to one of `L`. At every point the induced stalk
isomorphism is linear over the local ring and maps the maximal ideal times the
whole stalk onto the corresponding submodule. Thus the transported section has
exactly the same nonvanishing locus. The same affine open and positive exponent
witness ampleness at each point; compactness is unchanged. Apply this argument to
the inverse isomorphism for the converse. This also works on the empty scheme.
-/
theorem isAmple_iff_of_iso {X : Scheme.{u}} {L N : X.Modules}
    [L.IsInvertible] [N.IsInvertible] (e : L ≅ N) :
    IsAmple X L ↔ IsAmple X N := by
  suffices h : ∀ {M P : X.Modules} [M.IsInvertible] [P.IsInvertible],
      (M ≅ P) → IsAmple X M → IsAmple X P from ⟨h e, h e.symm⟩
  intro M P _ _ a hM
  refine ⟨hM.1, fun x ↦ ?_⟩
  obtain ⟨n, hn, s, U, hx, hU, hs⟩ := hM.2 x
  obtain ⟨b⟩ := tensorPow_iso a n
  refine ⟨n, hn, b.hom.app ⊤ s, U, hx, hU, ?_⟩
  intro y
  have hb := Set.ext_iff.mp (nonvanishingLocus_iso b s) y
  exact (hs y).trans hb.symm

end AlgebraicGeometry.Scheme.Modules
