/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.AffineAlgebraLocalMaps

/-! # Full faithfulness of the affine structure-algebra functor

Source: Stacks Project, Morphisms, Lemma 01SA, with the local argument in steps 5--6 of
lem-weil-pbc-affine-morphism-relative-spec
(blueprint: lem-weil-pbc-affine-structure-algebra-fully-faithful).
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

set_option hygiene false in
local notation "𝒪⁎" f:max => Under.mk (⟨(f).c⟩ : Scheme.sheaf _ ⟶
  (TopCat.Sheaf.pushforward CommRingCat.{u} (f).base).obj (Scheme.sheaf _))

private theorem sheaf_eqToHom_app {T : TopCat.{u}}
    {A B : TopCat.Sheaf CommRingCat.{u} T} (e : A = B) (V : Opens T) :
    (eqToHom e).hom.app (op V) = eqToHom (by cases e; rfl) := by
  cases e
  rfl

private theorem affine_over_ext {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsAffineHom g] (h h' : X ⟶ Y) (w : h ≫ g = f) (w' : h' ≫ g = f)
    (he : ∀ U : S.affineOpens,
      h.appLE (g ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1)
        (by rw [← w, Scheme.Hom.comp_preimage]) =
      h'.appLE (g ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1)
        (by rw [← w', Scheme.Hom.comp_preimage])) : h = h' := by
  apply Scheme.hom_ext_of_forall
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (show f x ∈ (⊤ : S.Opens) from trivial) isOpen_univ
  refine ⟨f ⁻¹ᵁ U, hxU, ?_⟩
  have : IsAffine (g ⁻¹ᵁ U).toScheme := hU.preimage g
  have hh : h.resLE (g ⁻¹ᵁ U) (f ⁻¹ᵁ U)
      (by rw [← w, Scheme.Hom.comp_preimage]) =
    h'.resLE (g ⁻¹ᵁ U) (f ⁻¹ᵁ U)
      (by rw [← w', Scheme.Hom.comp_preimage]) := by
    apply ext_of_isAffine
    simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
    rw [he ⟨U, hU⟩]
  simpa only [Scheme.Hom.resLE_comp_ι] using congrArg (· ≫ (g ⁻¹ᵁ U).ι) hh

private theorem exists_over_map_of_algebra {S X Y : Scheme.{u}} (f : X ⟶ S)
    (g : Y ⟶ S) [IsAffineHom g] (α : (𝒪⁎g : S.CommAlgebraSheaf) ⟶ 𝒪⁎f) :
    ∃ (h : X ⟶ Y) (w : h ≫ g = f), ∀ U : S.affineOpens,
      h.appLE (g ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1)
        (by rw [← w, Scheme.Hom.comp_preimage]) = α.right.hom.app (op U.1) := by
  obtain ⟨k, hw, hc, ha⟩ := affine_algebra_local_maps f g α
  let 𝒰 := X.openCoverOfIsOpenCover (fun U : S.affineOpens ↦ f ⁻¹ᵁ U.1)
    (f.iSup_preimage_eq_top (iSup_affineOpens_eq_top S))
  let h : X ⟶ Y := 𝒰.glueMorphisms k hc
  have hi (U : S.affineOpens) : (f ⁻¹ᵁ U.1).ι ≫ h = k U :=
    𝒰.ι_glueMorphisms k hc U
  have w : h ≫ g = f := by
    apply 𝒰.hom_ext
    intro U
    change (f ⁻¹ᵁ U.1).ι ≫ h ≫ g = (f ⁻¹ᵁ U.1).ι ≫ f
    rw [← Category.assoc, hi, hw]
  refine ⟨h, w, ?_⟩
  intro U
  have e : ⊤ ≤ k U ⁻¹ᵁ (g ⁻¹ᵁ U.1) := by
    rw [← Scheme.Hom.comp_preimage, hw, Scheme.Hom.comp_preimage]
    simp
  have ea := ha U e
  simp only [← hi U] at ea
  rw [Scheme.Hom.comp_appLE] at ea
  simp only [Scheme.Opens.ι_appLE] at ea
  apply (cancel_mono (f ⁻¹ᵁ U.1).topIso.inv).mp
  simp only [Scheme.Hom.appLE, Scheme.Opens.topIso_inv, Category.assoc,
    ← Functor.map_comp] at ea ⊢
  convert ea using 1
  congr 1

/-- The canonical contravariant structure-algebra functor is full and faithful.
Source: Stacks Project, Morphisms, Lemma 01SA; Constructions, Lemmas 01LT and 01LY
(blueprint: lem-weil-pbc-affine-structure-algebra-fully-faithful).

Proof: On an affine open U of S, both inverse images are affine. The Gamma--Spec
adjunction identifies morphisms between them with ring maps on sections. The condition
of being over U is exactly compatibility with the structure maps from O_S(U).
If two S-morphisms have the same image under F, hmap gives equality of their section
maps over every affine U, hence equality of their restrictions by the adjunction.
These inverse images cover the source, so scheme-morphism gluing gives equality globally.
For fullness, an algebra morphism gives on every affine U the unique U-morphism
corresponding to its section map. Naturality of the algebra morphism and uniqueness for
maps into affine schemes give compatibility over inclusions of affine opens. For two
arbitrary affine opens, cover their intersection by smaller affine opens and apply the
same uniqueness there. Scheme-morphism gluing now gives a global S-morphism. Its image
under F has the prescribed components on all affine opens by hmap; sheaf-morphism
uniqueness on an affine basis gives equality with the original algebra morphism.
This argument also covers the empty scheme, whose empty open cover detects equality. -/
theorem affine_structure_algebra_full_faithful (S : Scheme.{u})
    (F : (ObjectProperty.FullSubcategory (fun Y : Over S ↦ IsAffineHom Y.hom))ᵒᵖ ⥤
      ObjectProperty.FullSubcategory
        (fun A : S.CommAlgebraSheaf ↦ A.toModule.IsQuasicoherent))
    (hobj : ∀ Y, (F.obj (op Y)).obj = 𝒪⁎ Y.obj.hom)
    (hmap : ∀ (Y Y') (h : Y ⟶ Y') (V : S.Opens),
      (F.map h.op).hom.right.hom.app (op V) =
        eqToHom (by rw [hobj Y']; rfl) ≫
          h.hom.left.appLE (Y'.obj.hom ⁻¹ᵁ V) (Y.obj.hom ⁻¹ᵁ V)
            (by rw [← Over.w h.hom, Scheme.Hom.comp_preimage]) ≫
          eqToHom (by rw [hobj Y]; rfl)) :
    F.Full ∧ F.Faithful := by
  constructor
  · refine ⟨?_⟩
    intro X Y a
    let α : (𝒪⁎X.unop.obj.hom : S.CommAlgebraSheaf) ⟶ 𝒪⁎Y.unop.obj.hom :=
      eqToHom (hobj X.unop).symm ≫ a.hom ≫ eqToHom (hobj Y.unop)
    let : IsAffineHom X.unop.obj.hom := X.unop.property
    obtain ⟨h, w, ha⟩ := exists_over_map_of_algebra Y.unop.obj.hom X.unop.obj.hom α
    let b : Y.unop ⟶ X.unop := ⟨Over.homMk h w⟩
    refine ⟨b.op, ?_⟩
    apply ObjectProperty.hom_ext
    apply Under.UnderMorphism.ext
    apply CategoryTheory.Sheaf.hom_ext
    apply TopCat.Sheaf.hom_ext _ _ (B := fun U : S.affineOpens ↦ U.1)
      (by
        change Opens.IsBasis (Set.range (fun U : S.affineOpens ↦ U.1))
        rw [show Set.range (fun U : S.affineOpens ↦ U.1) = S.affineOpens by
          ext V
          constructor
          · rintro ⟨U, rfl⟩
            exact U.2
          · intro hV
            exact ⟨⟨V, hV⟩, rfl⟩]
        exact S.isBasis_affineOpens)
    intro U
    rw [hmap]
    change eqToHom _ ≫ h.appLE _ _ _ ≫ eqToHom _ = _
    rw [ha U]
    dsimp [α]
    simp only [Under.eqToHom_right, TopCat.Sheaf.comp_app, sheaf_eqToHom_app,
      Category.assoc]
    simp
  · refine ⟨?_⟩
    intro X Y a b hab
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    let : IsAffineHom X.unop.obj.hom := X.unop.property
    apply affine_over_ext Y.unop.obj.hom X.unop.obj.hom
      a.unop.hom.left b.unop.hom.left (Over.w a.unop.hom) (Over.w b.unop.hom)
    intro U
    have e := congrArg (fun t ↦ t.hom.right.hom.app (op U.1)) hab
    have ea := hmap Y.unop X.unop a.unop U.1
    have eb := hmap Y.unop X.unop b.unop U.1
    simp only [Quiver.Hom.op_unop] at ea eb
    rw [ea, eb] at e
    simpa only [Category.assoc, cancel_epi, cancel_mono] using e

end AlgebraicGeometry
