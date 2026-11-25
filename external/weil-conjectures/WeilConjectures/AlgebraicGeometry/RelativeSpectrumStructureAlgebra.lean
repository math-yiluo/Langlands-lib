/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Structure algebra from compatible spectral charts

Source: Stacks Project, Constructions, proof of Lemma 01LV.
(blueprint: lem-weil-pbc-relative-spectrum-structure-algebra).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

set_option hygiene false in
local notation "𝒪⁎" f:max => Under.mk (⟨(f).c⟩ : Scheme.sheaf _ ⟶
  (TopCat.Sheaf.pushforward CommRingCat.{u} (f).base).obj (Scheme.sheaf _))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Compatible cartesian spectral charts identify an algebra sheaf with the direct image
of the structure algebra. No quasi-coherence hypothesis is needed once charts are given.
Source: Stacks Project, Constructions, proof of Lemma 01LV, first paragraph,
and Lemma 01LX (3); Sheaves, Lemma 009U.
(blueprint: lem-weil-pbc-relative-spectrum-structure-algebra).

Proof: Each chart is an open immersion by base change, with image the inverse image
of U. Its sections map O_X(f⁻¹ U) → Γ(Spec A(U)) is therefore an isomorphism. Compose
with Γ(Spec A(U)) ≅ A(U). The compatibility equation for the charts and naturality
of this spectrum sections isomorphism prove compatibility with affine restrictions.
Extend these maps to b : f_* O_X → A by the sheaf morphism extension theorem.
Its affine components are isomorphisms, so b is an isomorphism. To check that b
respects the structure maps, compose the cartesian square on sections, use the
sections formula for the inverse affine chart, and cancel the canonical spectrum
sections isomorphisms. Equality of morphisms can be checked on the affine basis,
so b defines an isomorphism in Under S.sheaf. Take its inverse for the conclusion.
The argument includes the empty base and zero section rings: empty spectra and empty
opens are legitimate charts, and the basis extension theorem applies unchanged. -/
theorem structure_algebra_iso_of_affine_spectral_charts
    (S : Scheme.{u}) (A : S.CommAlgebraSheaf) (X : Scheme.{u}) (f : X ⟶ S)
    (k : ∀ U : S.affineOpens, Spec (A.right.obj.obj (op U.1)) ⟶ X)
    (hk : ∀ U : S.affineOpens,
      IsPullback (Spec.map (A.hom.hom.app (op U.1)) ≫ U.2.isoSpec.inv)
        (k U) U.1.ι f)
    (hres : ∀ (U V : S.affineOpens) (hUV : U.1 ≤ V.1),
      Spec.map (A.right.obj.map (homOfLE hUV).op) ≫ k V = k U) :
    Nonempty (A ≅ 𝒪⁎ f) := by
  have hi (U : S.affineOpens) : IsOpenImmersion (k U) :=
    MorphismProperty.of_isPullback (hk U) inferInstance
  have hr (U : S.affineOpens) : (k U).opensRange = f ⁻¹ᵁ U.1 := by
    apply Opens.ext
    change Set.range (k U) = f ⁻¹' (U.1 : Set S)
    simpa only [Set.preimage_univ, Set.image_univ, Scheme.Opens.range_ι]
      using Scheme.image_preimage_eq_of_isPullback (hk U) Set.univ
  have hle (U : S.affineOpens) : ⊤ ≤ (k U) ⁻¹ᵁ (f ⁻¹ᵁ U.1) := by
    rw [← hr U]
    simp
  let γ (U : S.affineOpens) := (k U).appLE (f ⁻¹ᵁ U.1) ⊤ (hle U)
  have hγ (U : S.affineOpens) : IsIso (γ U) := by
    have : IsIso ((k U).app (f ⁻¹ᵁ U.1)) :=
      (k U).isIso_app _ (hr U).ge
    have he : (k U) ⁻¹ᵁ (f ⁻¹ᵁ U.1) = ⊤ := top_unique (hle U)
    have he' : homOfLE (hle U) = eqToHom he.symm := Subsingleton.elim _ _
    dsimp [γ]
    rw [Scheme.Hom.appLE, he']
    infer_instance
  let D := (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj X.sheaf
  have hb : Opens.IsBasis (Set.range (fun U : S.affineOpens ↦ U.1)) := by
    convert S.isBasis_affineOpens using 1
    ext U
    simp
  let β : (inducedFunctor (fun U : S.affineOpens ↦ U.1)).op ⋙ D.obj ⟶
      (inducedFunctor (fun U : S.affineOpens ↦ U.1)).op ⋙ A.right.obj :=
    { app := fun U ↦ γ U.unop ≫ (Scheme.ΓSpecIso _).hom
      naturality := by
        intro U V h
        change X.presheaf.map _ ≫ (γ V.unop ≫ (Scheme.ΓSpecIso _).hom) =
          (γ U.unop ≫ (Scheme.ΓSpecIso _).hom) ≫ A.right.obj.map _
        rw [Category.assoc, ← Scheme.ΓSpecIso_naturality, ← Category.assoc,
          ← Category.assoc]
        congr 1
        dsimp [γ]
        rw [Scheme.Hom.map_appLE]
        change _ = (k U.unop).appLE _ ⊤ (hle U.unop) ≫
          (Spec.map (A.right.obj.map h.unop.hom.op)).appLE ⊤ ⊤ (by simp)
        rw [Scheme.Hom.appLE_comp_appLE]
        have hh : h.unop.hom = homOfLE h.unop.hom.le := Subsingleton.elim _ _
        rw [hh]
        simp only [hres V.unop U.unop h.unop.hom.le] }
  let b : D ⟶ A.right := ⟨TopCat.Sheaf.restrictHomEquivHom D.obj A.right hb β⟩
  have : IsIso b := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis hb
    intro U
    change IsIso ((TopCat.Sheaf.restrictHomEquivHom D.obj A.right hb β).app (op U.1))
    rw [TopCat.Sheaf.extend_hom_app]
    change IsIso (γ U ≫ (Scheme.ΓSpecIso _).hom)
    infer_instance
  have hw : (𝒪⁎ f).hom ≫ b = A.hom := by
    apply Sheaf.hom_ext
    apply TopCat.Sheaf.hom_ext _ _ hb
    intro U
    change f.app U.1 ≫ b.hom.app (op U.1) = A.hom.hom.app (op U.1)
    change f.app U.1 ≫
      (TopCat.Sheaf.restrictHomEquivHom D.obj A.right hb β).app (op U.1) = _
    rw [TopCat.Sheaf.extend_hom_app]
    change f.app U.1 ≫ (γ U ≫ (Scheme.ΓSpecIso _).hom) = _
    rw [← Category.assoc]
    dsimp only [γ]
    rw [f.app_eq_appLE]
    rw [Scheme.Hom.appLE_comp_appLE]
    simp only [← (hk U).w]
    rw [← Scheme.Hom.appLE_comp_appLE
      (Spec.map (A.hom.hom.app (op U.1)) ≫ U.2.isoSpec.inv) U.1.ι
      U.1 ⊤ ⊤ U.1.ι_preimage_self.ge (by simp)]
    rw [← Scheme.Hom.appLE_comp_appLE
      (Spec.map (A.hom.hom.app (op U.1))) U.2.isoSpec.inv
      ⊤ ⊤ ⊤ (by simp) (by simp)]
    have hι : U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge = U.1.topIso.inv := by
      simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
      congr 1
    rw [hι]
    have happ {Y Z : Scheme.{u}} (g : Y ⟶ Z) (e : ⊤ ≤ g ⁻¹ᵁ ⊤) :
        g.appLE ⊤ ⊤ e = g.appTop := by
      change g.appTop ≫ Y.presheaf.map (𝟙 (op ⊤)) = g.appTop
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
    simp only [happ]
    rw [U.2.isoSpec_inv_appTop]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Scheme.ΓSpecIso_naturality]
    change (Scheme.ΓSpecIso Γ(S, U.1)).inv ≫
      (Scheme.ΓSpecIso Γ(S, U.1)).hom ≫ A.hom.hom.app (op U.1) = _
    rw [Iso.inv_hom_id_assoc]
  exact ⟨(Under.isoMk (asIso b) hw).symm⟩

end AlgebraicGeometry
