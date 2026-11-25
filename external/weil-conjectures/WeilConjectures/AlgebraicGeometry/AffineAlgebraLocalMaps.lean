/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf

/-! # Local maps determined by a morphism of structure algebras

Source: Stacks Project, Morphisms, Lemma 01SA; Constructions, Lemma 01LT.
(blueprint: lem-weil-pbc-affine-algebra-local-maps).
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

set_option hygiene false in
local notation "𝒪⁎" f:max => Under.mk (⟨(f).c⟩ : Scheme.sheaf _ ⟶
  (TopCat.Sheaf.pushforward CommRingCat.{u} (f).base).obj (Scheme.sheaf _))

private theorem inclusion_appTop {X : Scheme.{u}} {U V : X.Opens} (e : U ≤ V) :
    V.topIso.inv ≫ (X.homOfLE e).appTop =
      X.presheaf.map (homOfLE e).op ≫ U.topIso.inv := by
  simp only [Scheme.Opens.topIso_inv, Scheme.homOfLE_appTop, ← Functor.map_comp]
  congr 1

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An algebra morphism gives compatible scheme maps on inverse images of affine opens.
Source: Stacks Project, Morphisms, Lemma 01SA; Constructions, Lemma 01LT;
parts (i) and (iii) of the local proof of the affine structure-algebra correspondence.
(blueprint: lem-weil-pbc-affine-algebra-local-maps).

Proof: For each affine open U of S, the inverse image of U under g is affine.
The Gamma--Spec adjunction applied to the component of α on U, conjugated by the
canonical top-section isomorphisms of both open subschemes, gives a map from the
inverse image under f to the inverse image under g. The commutativity condition
of the algebra morphism says that its composite to U agrees with the restricted
map f: this follows by injectivity of the Gamma--Spec correspondence for the affine U.
Compose with the open immersion into Y to obtain k_U. Its section map is the prescribed
component by construction, including the stated top-section transport.

For an affine V contained in U, compare k_V with the restriction of k_U. Both factor
through the affine inverse image of U under g. Naturality of α gives equality of
their global section maps, and injectivity of the adjunction gives equality of maps.
For arbitrary affine U and V, their intersection need not be affine. Cover it by
affine W contained in both. On the inverse image of each W both maps agree with k_W,
by the preceding comparison. Scheme-morphism uniqueness on this open cover gives
the displayed equality on the pullback of the two open immersions. No affineness
of X is required, and the empty inverse images and empty base are covered by the
same adjunction and the uniqueness assertion for the empty cover. -/
theorem affine_algebra_local_maps {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsAffineHom g] (α : (𝒪⁎g : S.CommAlgebraSheaf) ⟶ 𝒪⁎f) :
    ∃ k : ∀ U : S.affineOpens, (f ⁻¹ᵁ U.1).toScheme ⟶ Y,
      (∀ U, k U ≫ g = (f ⁻¹ᵁ U.1).ι ≫ f) ∧
      (∀ U V, Limits.pullback.fst (f ⁻¹ᵁ U.1).ι (f ⁻¹ᵁ V.1).ι ≫ k U =
        Limits.pullback.snd (f ⁻¹ᵁ U.1).ι (f ⁻¹ᵁ V.1).ι ≫ k V) ∧
      (∀ (U : S.affineOpens) (e : ⊤ ≤ k U ⁻¹ᵁ (g ⁻¹ᵁ U.1)),
        (k U).appLE (g ⁻¹ᵁ U.1) ⊤ e =
          α.right.hom.app (op U.1) ≫ (f ⁻¹ᵁ U.1).topIso.inv) := by
  classical
  have hY (U : S.affineOpens) : IsAffineOpen (g ⁻¹ᵁ U.1) := U.2.preimage g
  let q (U : S.affineOpens) : (f ⁻¹ᵁ U.1).toScheme ⟶ (g ⁻¹ᵁ U.1).toScheme :=
    (f ⁻¹ᵁ U.1).toScheme.toSpecΓ ≫
      Spec.map (α.right.hom.app (op U.1) ≫ (f ⁻¹ᵁ U.1).topIso.inv) ≫
      (hY U).isoSpec.inv
  have hq (U : S.affineOpens) : (q U).appTop =
      (g ⁻¹ᵁ U.1).topIso.hom ≫ α.right.hom.app (op U.1) ≫
        (f ⁻¹ᵁ U.1).topIso.inv := by
    simp [q, IsAffineOpen.isoSpec_inv_appTop, Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality]
  have hα (U : S.affineOpens) :
      g.app U.1 ≫ α.right.hom.app (op U.1) = f.app U.1 := by
    exact congrArg (fun z ↦ z.hom.app (op U.1)) α.w
  have hqg (U : S.affineOpens) : q U ≫ g ∣_ U.1 = f ∣_ U.1 := by
    let : IsAffine U.1.toScheme := U.2
    apply ext_of_isAffine
    rw [Scheme.Hom.comp_appTop, hq]
    have hg := g.resLE_app_top (U := U.1) le_rfl
    have hf := f.resLE_app_top (U := U.1) le_rfl
    rw [Scheme.Hom.resLE_eq_morphismRestrict] at hg hf
    simp only [Scheme.Hom.appLE_eq_app] at hg hf
    change (g ∣_ U.1).appTop = _ at hg
    change (f ∣_ U.1).appTop = _ at hf
    rw [hg, hf]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc (g.app U.1), hα]
  have hqn (U V : S.affineOpens) (e : V.1 ≤ U.1) :
      X.homOfLE ((Opens.map f.base).map (homOfLE e)).le ≫ q U =
        q V ≫ Y.homOfLE ((Opens.map g.base).map (homOfLE e)).le := by
    let : IsAffine (g ⁻¹ᵁ U.1).toScheme := hY U
    apply ext_of_isAffine
    change (q U).appTop ≫
        (X.homOfLE ((Opens.map f.base).map (homOfLE e)).le).appTop =
      (Y.homOfLE ((Opens.map g.base).map (homOfLE e)).le).appTop ≫ (q V).appTop
    rw [hq U, hq V]
    apply (cancel_epi (g ⁻¹ᵁ U.1).topIso.inv).mp
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    simp only [Category.assoc, inclusion_appTop]
    have hn :
        Y.presheaf.map ((Opens.map g.base).map (homOfLE e)).op ≫
          α.right.hom.app (op V.1) =
        α.right.hom.app (op U.1) ≫
          X.presheaf.map ((Opens.map f.base).map (homOfLE e)).op :=
      α.right.hom.naturality (homOfLE e).op
    simp only [Iso.inv_hom_id_assoc]
    convert congrArg (· ≫ (f ⁻¹ᵁ V.1).topIso.inv) hn.symm using 1 <;>
      (try simp only [Category.assoc]) <;> congr 2
  let k (U : S.affineOpens) := q U ≫ (g ⁻¹ᵁ U.1).ι
  have hk (U : S.affineOpens) : k U ≫ g = (f ⁻¹ᵁ U.1).ι ≫ f := by
    dsimp [k]
    rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, hqg,
      morphismRestrict_ι]
  have hkn (U V : S.affineOpens) (e : V.1 ≤ U.1) :
      X.homOfLE ((Opens.map f.base).map (homOfLE e)).le ≫ k U = k V := by
    dsimp [k]
    rw [← Category.assoc, hqn U V e, Category.assoc, Scheme.homOfLE_ι]
  refine ⟨k, hk, ?_, ?_⟩
  · intro U V
    let r := Limits.pullback.fst (f ⁻¹ᵁ U.1).ι (f ⁻¹ᵁ V.1).ι ≫ (f ⁻¹ᵁ U.1).ι
    have hr : r =
        Limits.pullback.snd (f ⁻¹ᵁ U.1).ι (f ⁻¹ᵁ V.1).ι ≫ (f ⁻¹ᵁ V.1).ι :=
      Limits.pullback.condition
    apply Scheme.hom_ext_of_forall
    intro x
    have hx : (r ≫ f) x ∈ (U.1 ⊓ V.1 : S.Opens) := by
      constructor
      · exact (Limits.pullback.fst (f ⁻¹ᵁ U.1).ι (f ⁻¹ᵁ V.1).ι x).2
      · rw [hr]
        exact (Limits.pullback.snd (f ⁻¹ᵁ U.1).ι (f ⁻¹ᵁ V.1).ι x).2
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWUV⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open hx (U.1 ⊓ V.1).isOpen
    let O := (r ≫ f) ⁻¹ᵁ W
    let a : O.toScheme ⟶ (f ⁻¹ᵁ W).toScheme :=
      r.resLE (f ⁻¹ᵁ W) O (by
        change (r ≫ f) ⁻¹ᵁ W ≤ r ⁻¹ᵁ (f ⁻¹ᵁ W)
        rw [Scheme.Hom.comp_preimage])
    have ha : a ≫ (f ⁻¹ᵁ W).ι = O.ι ≫ r := r.resLE_comp_ι _
    have hWU : W ≤ U.1 := hWUV.trans inf_le_left
    have hWV : W ≤ V.1 := hWUV.trans inf_le_right
    have haU : a ≫ X.homOfLE ((Opens.map f.base).map (homOfLE hWU)).le =
        O.ι ≫ Limits.pullback.fst (f ⁻¹ᵁ U.1).ι (f ⁻¹ᵁ V.1).ι := by
      rw [← cancel_mono (f ⁻¹ᵁ U.1).ι]
      simp only [Category.assoc, Scheme.homOfLE_ι]
      rw [ha]
    have haV : a ≫ X.homOfLE ((Opens.map f.base).map (homOfLE hWV)).le =
        O.ι ≫ Limits.pullback.snd (f ⁻¹ᵁ U.1).ι (f ⁻¹ᵁ V.1).ι := by
      rw [← cancel_mono (f ⁻¹ᵁ V.1).ι]
      simp only [Category.assoc, Scheme.homOfLE_ι]
      rw [ha]
      exact congrArg (O.ι ≫ ·) hr
    refine ⟨O, hxW, ?_⟩
    calc
      O.ι ≫ (Limits.pullback.fst _ _ ≫ k U) =
          a ≫ (X.homOfLE ((Opens.map f.base).map (homOfLE hWU)).le ≫ k U) := by
        simpa only [Category.assoc] using congrArg (· ≫ k U) haU.symm
      _ = a ≫ k ⟨W, hW⟩ := by rw [hkn U ⟨W, hW⟩ hWU]
      _ = a ≫ (X.homOfLE ((Opens.map f.base).map (homOfLE hWV)).le ≫ k V) := by
        rw [hkn V ⟨W, hW⟩ hWV]
      _ = O.ι ≫ (Limits.pullback.snd _ _ ≫ k V) := by
        simpa only [Category.assoc] using congrArg (· ≫ k V) haV
  · intro U e
    have hι : (g ⁻¹ᵁ U.1).ι.appLE (g ⁻¹ᵁ U.1) ⊤ (by simp) =
        (g ⁻¹ᵁ U.1).topIso.inv := by
      simp [Scheme.Opens.ι_appLE, Scheme.Opens.topIso]
      congr 1
    have hcomp := Scheme.Hom.appLE_comp_appLE (q U) (g ⁻¹ᵁ U.1).ι
      (g ⁻¹ᵁ U.1) ⊤ ⊤ (by simp) (by simp)
    rw [hι] at hcomp
    rw [← hcomp]
    erw [Scheme.Hom.appLE_eq_app]
    change (g ⁻¹ᵁ U.1).topIso.inv ≫ (q U).appTop = _
    rw [hq]
    simp only [Iso.inv_hom_id_assoc]

end AlgebraicGeometry
