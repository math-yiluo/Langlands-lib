/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.AlgebraicGeometry.Morphisms.DepthTwoPushforwardCoherence
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteStructureAlgebraDepth
import WeilConjectures.AlgebraicGeometry.RelativeSpectrumAffineRealization
import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec

/-!
# Finite extension with depth two along the boundary

## References

* Stacks Project, Tag 0EY6, assertions (1) and (2)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

private noncomputable abbrev structureAlgebraOf {X S : Scheme.{u}} (f : X ⟶ S) :
    S.CommAlgebraSheaf :=
  Under.mk (⟨f.c⟩ : S.sheaf ⟶
    (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj X.sheaf)

private theorem iso_over_of_structure_algebra_iso {S X Y : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) [IsAffineHom f] [IsAffineHom g]
    (α : (structureAlgebraOf f : S.CommAlgebraSheaf) ≅ structureAlgebraOf g) :
    ∃ e : X ≅ Y, e.hom ≫ g = f := by
  obtain ⟨_, F, hobj, _⟩ := affine_morphism_relative_spec S
  let P : ObjectProperty (Over S) := fun Z ↦ IsAffineHom Z.hom
  let Yf : P.FullSubcategory := ⟨Over.mk f, (show IsAffineHom f from inferInstance)⟩
  let Yg : P.FullSubcategory := ⟨Over.mk g, (show IsAffineHom g from inferInstance)⟩
  let i := F.functor.preimageIso (ObjectProperty.isoMk _
    ((eqToIso (hobj Yg)) ≪≫ α.symm ≪≫ (eqToIso (hobj Yf)).symm))
  let eOver := P.ι.mapIso i.unop
  exact ⟨(Over.forget S).mapIso eOver, Over.w eOver.hom⟩

private noncomputable def pushforward_open_restriction_iso
    {L X : Scheme.{u}} (U : L.Opens) (f : X ⟶ U.toScheme) :
    ((Under.post (U.ι.isOpenEmbedding.sheafPullback CommRingCat.{u})).obj
      (structureAlgebraOf (f ≫ U.ι)) : U.toScheme.CommAlgebraSheaf) ≅ structureAlgebraOf f := by
  refine Under.isoMk (ObjectProperty.isoMk _ (NatIso.ofComponents
    (fun W ↦ X.presheaf.mapIso (eqToIso (by
      change f ⁻¹ᵁ W.unop = (f ≫ U.ι) ⁻¹ᵁ (U.ι ''ᵁ W.unop)
      rw [Scheme.Hom.comp_preimage, Scheme.Hom.preimage_image_eq])).op) ?_)) ?_
  · intro W W' i
    change X.presheaf.map _ ≫ X.presheaf.map _ = X.presheaf.map _ ≫ X.presheaf.map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
  · apply Sheaf.hom_ext
    apply NatTrans.ext
    funext W
    change (f ≫ U.ι).app (U.ι ''ᵁ W.unop) ≫ _ = f.app W.unop
    rw [Scheme.Hom.comp_app]
    change U.ι.app (U.ι ''ᵁ W.unop) ≫ f.app (U.ι ⁻¹ᵁ U.ι ''ᵁ W.unop) ≫
      X.presheaf.map _ = f.app W.unop
    erw [← f.naturality (eqToHom (U.ι.preimage_image_eq W.unop).symm).op]
    have hi : U.ι.app (U.ι ''ᵁ W.unop) ≫
        U.toScheme.presheaf.map (eqToHom (U.ι.preimage_image_eq W.unop).symm).op =
        (U.ι.appIso W.unop).hom := by
      rw [Scheme.Hom.appIso_hom]
    rw [← Category.assoc, hi, Scheme.Opens.ι_appIso]
    exact Category.id_comp _

/-- A finite etale cover extends to a finite scheme with depth two along the boundary. -/
theorem exists_finite_extension_of_depth_two
    {L : Scheme.{u}} [IsLocallyNoetherian L] (U : L.Opens)
    (hboundary : ∀ y : L, y ∉ U →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := L.presheaf.stalk y) (L.presheaf.stalk y))
    {X : Scheme.{u}} (f : X ⟶ U.toScheme) [IsFinite f] [Etale f] :
    ∃ (E : Scheme.{u}) (p : E ⟶ L), IsFinite p ∧
      (∀ z : E, p z ∉ U →
        (2 : ℕ∞) ≤ IsLocalRing.depth (R := E.presheaf.stalk z) (E.presheaf.stalk z)) ∧
      ∃ e : (p ⁻¹ᵁ U).toScheme ≅ X, e.hom ≫ f = p ∣_ U := by
  let g := f ≫ U.ι
  let B : L.CommAlgebraSheaf := structureAlgebraOf g
  obtain ⟨hqc, hfinite, hdepth⟩ := depth_two_pushforward_coherence U hboundary f
  obtain ⟨E, p, hp, ⟨α⟩⟩ := exists_affine_structure_algebra L B hqc
  have : IsAffineHom p := hp
  have : IsFinite p := by
    refine ⟨?_⟩
    intro V hV
    have hw := congrArg (fun k ↦ k.hom.app (Opposite.op V)) (Under.w α.hom)
    change B.hom.hom.app (Opposite.op V) ≫ α.hom.right.hom.app (Opposite.op V) =
      p.app V at hw
    rw [← hw, CommRingCat.hom_comp]
    exact (RingHom.Finite.of_surjective _
      ((ConcreteCategory.bijective_of_isIso (α.hom.right.hom.app (Opposite.op V))).2)).comp
        (hfinite V hV)
  have hE := depth_two_of_finite_structure_algebra U B hdepth p α
  obtain ⟨_, F, hobj, ρ, _⟩ := affine_morphism_relative_spec L
  let Yp : ObjectProperty.FullSubcategory (fun Y : Over L ↦ IsAffineHom Y.hom) :=
    ⟨Over.mk p, hp⟩
  let β := (Under.post (U.ι.isOpenEmbedding.sheafPullback CommRingCat.{u})).mapIso α
  let γ : (structureAlgebraOf (p ∣_ U) : U.toScheme.CommAlgebraSheaf) ≅ structureAlgebraOf f :=
    (ρ Yp U).symm ≪≫ β.symm ≪≫ pushforward_open_restriction_iso U f
  have : IsAffineHom (p ∣_ U) := IsZariskiLocalAtTarget.restrict hp U
  obtain ⟨e, he⟩ := iso_over_of_structure_algebra_iso (p ∣_ U) f γ
  exact ⟨E, p, inferInstance, hE, e, he⟩

end AlgebraicGeometry.Scheme
