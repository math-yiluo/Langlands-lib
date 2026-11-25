/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.CategoryTheory.Limits.Shapes.Images
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images

/-! # The canonical intersection of the lattices on a finite cover

The inverse image of the pushed-forward lattice image under the adjunction unit
is a genuine categorical pullback. Over a split finite cover it is the intersection
of the sheet lattices, so its construction requires no choices of splittings.

Source: Bhatt--Scholze, Lemma 6.8.13, finite-etale descent of integral structures.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory.Limits

variable {C : Type*} [Category C] [Abelian C] {A B D : C}

/-- The inverse image of the image of `g` under `f`.
Source: the categorical image and pullback universal properties.
(auxiliary; not a blueprint node) -/
noncomputable def imagePullback (f : A ⟶ D) (g : B ⟶ D) : C :=
  pullback f (image.ι g)

/-- The inclusion of the inverse image of an image.
Source: the pullback universal property.
(auxiliary; not a blueprint node) -/
noncomputable def imagePullbackι (f : A ⟶ D) (g : B ⟶ D) : imagePullback f g ⟶ A :=
  pullback.fst _ _

/-- Exact functors send the inclusion of this inverse image to an isomorphism
whenever they invert the map whose image was taken.
Source: exactness of images and the pullback universal property.
(auxiliary; not a blueprint node) -/
theorem imagePullbackι_map_isIso {D' : Type*} [Category D'] [Abelian D']
    (F : C ⥤ D') [PreservesFiniteLimits F]
    (f : A ⟶ D) (g : B ⟶ D) [IsIso (F.map g)] :
    IsIso (F.map (imagePullbackι f g)) := by
  have : Epi (F.map (factorThruImage g) ≫ F.map (image.ι g)) := by
    rw [← F.map_comp, image.fac]
    infer_instance
  have : Epi (F.map (image.ι g)) := epi_of_epi (F.map (factorThruImage g)) _
  have : IsIso (F.map (image.ι g)) := isIso_of_mono_of_epi _
  exact ((IsPullback.of_hasPullback f (image.ι g)).map F).isIso_fst_of_isIso

/-- Exact inverse image transports the canonical image-pullback itself.
Source: preservation of images and pullbacks by exact functors.
(auxiliary; not a blueprint node)
Proof. First use the pullback comparison, then the image comparison to transport
its second input. All three maps in this transport are isomorphisms. -/
noncomputable def imagePullbackMapIso {D' : Type*} [Category D'] [Abelian D']
    (F : C ⥤ D') [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (f : A ⟶ D) (g : B ⟶ D) :
    F.obj (imagePullback f g) ≅ imagePullback (F.map f) (F.map g) := by
  let e := PreservesImage.iso F g
  let h := pullback.map (F.map f) (F.map (image.ι g)) (F.map f) (image.ι (F.map g))
    (𝟙 _) e.inv (𝟙 _) (by simp) (by
      simpa only [Category.comp_id] using (PreservesImage.inv_comp_image_ι_map F g).symm)
  exact PreservesPullback.iso F f (image.ι g) ≪≫ asIso h

/-- Changing all objects and maps by commuting isomorphisms transports the
canonical image-pullback.
Source: functoriality of images and pullbacks.
(auxiliary; not a blueprint node)
Proof. Apply the image functor to the arrow isomorphism of the second maps.
Together with the first and target isomorphisms it induces an invertible map
between the two pullbacks. -/
noncomputable def imagePullbackCongr {A' B' D' : C}
    (f : A ⟶ D) (g : B ⟶ D) (f' : A' ⟶ D') (g' : B' ⟶ D')
    (eA : A ≅ A') (eB : B ≅ B') (eD : D ≅ D')
    (hf : eA.hom ≫ f' = f ≫ eD.hom) (hg : eB.hom ≫ g' = g ≫ eD.hom) :
    imagePullback f g ≅ imagePullback f' g' := by
  let e := Arrow.isoMk' g g' eB eD hg
  let eI := (im (C := C)).mapIso e
  let h := pullback.map f (image.ι g) f' (image.ι g') eA.hom eI.hom eD.hom
    hf.symm (by
      exact (image.map_ι e.hom).symm)
  exact asIso h

/-- The intersection of two subobjects is the kernel of one subobject's map to
the other's quotient.
Source: the normal-monomorphism property in an abelian category.
(auxiliary; not a blueprint node)
Proof. A monomorphism identifies its domain with its image. Projecting the
pullback to the second subobject therefore gives a map to the displayed kernel.
Conversely, a map killed by the first quotient factors uniquely through its
monomorphism and thus lifts to the pullback. The projection and kernel inclusions
are monic, so their universal properties prove the inverse identities. -/
noncomputable def imagePullbackIsoKernel (f : A ⟶ D) [Mono f]
    (g : B ⟶ D) [Mono g] : imagePullback f g ≅ kernel (g ≫ cokernel.π f) := by
  have : Mono (factorThruImage g) := mono_of_mono_fac (image.fac g)
  have : IsIso (factorThruImage g) := isIso_of_mono_of_epi _
  let e := asIso (factorThruImage g)
  let h : imagePullback f g ⟶ B := pullback.snd f (image.ι g) ≫ e.inv
  have hh : h ≫ g = pullback.fst f (image.ι g) ≫ f := by
    calc
      h ≫ g = h ≫ (e.hom ≫ image.ι g) :=
        congrArg (fun z : B ⟶ D ↦ h ≫ z) (image.fac g).symm
      _ = pullback.snd f (image.ι g) ≫ image.ι g := by simp [h, Category.assoc]
      _ = pullback.fst f (image.ι g) ≫ f := (pullback.condition (f := f) (g := image.ι g)).symm
  let k := kernel.lift (g ≫ cokernel.π f) h (by
    rw [← Category.assoc, hh, Category.assoc, cokernel.condition, comp_zero])
  let a := Abelian.monoLift f (kernel.ι (g ≫ cokernel.π f) ≫ g) (by
    rw [Category.assoc, kernel.condition])
  let l : kernel (g ≫ cokernel.π f) ⟶ imagePullback f g :=
    pullback.lift a (kernel.ι (g ≫ cokernel.π f) ≫ e.hom) (by
      rw [Abelian.monoLift_comp]
      simp only [Category.assoc]
      rw [show e.hom ≫ image.ι g = g from image.fac g])
  refine ⟨k, l, ?_, ?_⟩
  · apply (cancel_mono (pullback.snd f (image.ι g))).1
    simp [k, l, h, Category.assoc]
  · apply (cancel_mono (kernel.ι (g ≫ cokernel.π f))).1
    simp only [Category.assoc, k, kernel.lift_ι, h, l, pullback.lift_snd_assoc,
      Iso.hom_inv_id, Category.comp_id, Category.id_comp]

end CategoryTheory.Limits

namespace CategoryTheory.Adjunction

/-- Transposing a pushed integral embedding is coefficient-change pushforward
followed by the pushed rational map.
Source: the counit equation for the mates correspondence.
(auxiliary; not a blueprint node) -/
theorem pushHomOfComapIso_homEquiv
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {LX : A ⥤ B} {UX : B ⥤ A} {LY : C ⥤ D} {UY : D ⥤ C}
    (adjX : LX ⊣ UX) (adjY : LY ⊣ UY) {G : A ⥤ C} {H : B ⥤ D}
    (κ : H ⋙ UY ≅ UX ⋙ G) (M : A) (N : B) (f : LX.obj M ⟶ N) :
    LY.map (G.map ((adjX.homEquiv M N) f) ≫ κ.inv.app N) ≫ adjY.counit.app _ =
      (pushHomOfComapIso adjX adjY κ).app M ≫ H.map f := by
  let β := pushHomOfComapIso adjX adjY κ
  have hc := mateEquiv_counit_symm adjX adjY (TwoSquare.mk _ _ _ _ κ.inv) N
  change LY.map (κ.inv.app N) ≫ adjY.counit.app (H.obj N) =
    β.app (UX.obj N) ≫ H.map (adjX.counit.app N) at hc
  rw [LY.map_comp, Category.assoc, hc, ← Category.assoc]
  have hn := β.naturality ((adjX.homEquiv M N) f)
  change LY.map (G.map ((adjX.homEquiv M N) f)) ≫ β.app (UX.obj N) =
    β.app M ≫ H.map (LX.map ((adjX.homEquiv M N) f)) at hn
  rw [hn, Category.assoc, ← H.map_comp]
  have heq : LX.map ((adjX.homEquiv M N) f) ≫ adjX.counit.app N = f := by
    exact (adjX.homEquiv M N).symm_apply_apply f
  rw [heq]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a] (X : Scheme.{u})
  (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj S X))
  {U : Scheme.{u}} (p : U ⟶ X)
  (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
    (condensedRingObj R U))
  (e : (Mod.extendScalars (coefficientMap a U)).obj M ≅
    (upperStar S p).obj P)

/-- The supplied lattice maps to the restricted rational module by `m ↦ e(1 ⊗ m)`.
Source: Bhatt--Scholze, Lemma 6.8.13, integral structures on a finite cover.
(auxiliary; not a blueprint node) -/
noncomputable def latticeIntegralEmbedding :
    M ⟶ (Mod.comap (coefficientMap a U)).obj
      ((upperStar S p).obj P) :=
  (Mod.extendRestrictAdjunction (coefficientMap a U)).homEquiv
    M ((upperStar S p).obj P) e.hom

/-- Push forward the lattice embedding and use the canonical change-of-scalars comparison.
Source: Bhatt--Scholze, Lemma 6.8.13, finite-etale descent.
(auxiliary; not a blueprint node) -/
noncomputable def latticePushedEmbedding :
    (lowerStar R p).obj M ⟶
      (Mod.comap (coefficientMap a X)).obj
        ((lowerStar S p).obj
          ((upperStar S p).obj P)) :=
  (lowerStar R p).map (latticeIntegralEmbedding a X P p M e) ≫
    (comapLowerStarIso a p).inv.app
      ((upperStar S p).obj P)

/-- The rational adjunction unit, viewed as an integral-linear map.
Source: the inverse-image/direct-image adjunction in Bhatt--Scholze, Section 4.
(auxiliary; not a blueprint node) -/
noncomputable def latticeIntersectionUnit :
    (Mod.comap (coefficientMap a X)).obj P ⟶
      (Mod.comap (coefficientMap a X)).obj
        ((lowerStar S p).obj
          ((upperStar S p).obj P)) :=
  (Mod.comap (coefficientMap a X)).map
    ((upperStarLowerStarAdjunction S p).unit.app P)

/-- Pull back the image of the pushed lattice under the rational adjunction unit.
This constructs the module itself without selecting a witness of an existence theorem.
Source: Bhatt--Scholze, Lemma 6.8.13, finite-etale descent, using intersections.
(auxiliary; not a blueprint node) -/
noncomputable def latticeIntersection :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj R X) :=
  imagePullback (latticeIntersectionUnit a X P p)
    (latticePushedEmbedding a X P p M e)

/-- The canonical inclusion of the intersection in the rational module.
Source: the pullback construction of the finite-sheet lattice intersection.
(auxiliary; not a blueprint node) -/
noncomputable def latticeIntersectionι :
    latticeIntersection a X P p M e ⟶
      (Mod.comap (coefficientMap a X)).obj P :=
  by
    unfold latticeIntersection
    exact imagePullbackι _ _

/-- The canonical scalar extension map from the intersection to the original module.
Source: the tensor universal property in Bhatt--Scholze, Lemma 6.8.13.
(auxiliary; not a blueprint node) -/
noncomputable def latticeIntersectionRationalization :
    (Mod.extendScalars (coefficientMap a X)).obj
      (latticeIntersection a X P p M e) ⟶ P :=
  ((Mod.extendRestrictAdjunction (coefficientMap a X)).homEquiv _ _).symm
    (latticeIntersectionι a X P p M e)

/-- The canonical map out of the pushed lattice is the coefficient-change mate.
Source: the mates correspondence for extension and restriction of scalars.
(auxiliary; not a blueprint node) -/
theorem latticePushedEmbedding_rationalization :
    (Mod.extendScalars (coefficientMap a X)).map (latticePushedEmbedding a X P p M e) ≫
        (Mod.extendRestrictAdjunction (coefficientMap a X)).counit.app
          ((lowerStar S p).obj ((upperStar S p).obj P)) =
      (pushHom a p).app M ≫ (lowerStar S p).map e.hom := by
  exact Adjunction.pushHomOfComapIso_homEquiv
    (Mod.extendRestrictAdjunction (coefficientMap a U))
    (Mod.extendRestrictAdjunction (coefficientMap a X))
    (comapLowerStarIso a p) M ((upperStar S p).obj P) e.hom

/-- Invertibility of coefficient-change pushforward implies invertibility of the
extended pushed lattice map, provided the rational localization counit is invertible.
Source: the counit equation for the mates correspondence.
(auxiliary; not a blueprint node) -/
theorem latticePushedEmbedding_map_isIso
    [IsIso ((pushHom a p).app M)]
    [IsIso ((Mod.extendRestrictAdjunction (coefficientMap a X)).counit.app
      ((lowerStar S p).obj ((upperStar S p).obj P)))] :
    IsIso ((Mod.extendScalars (coefficientMap a X)).map
      (latticePushedEmbedding a X P p M e)) := by
  have : IsIso ((Mod.extendScalars (coefficientMap a X)).map
      (latticePushedEmbedding a X P p M e) ≫
        (Mod.extendRestrictAdjunction (coefficientMap a X)).counit.app
          ((lowerStar S p).obj ((upperStar S p).obj P))) := by
    rw [latticePushedEmbedding_rationalization]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((Mod.extendRestrictAdjunction (coefficientMap a X)).counit.app _)

/-- If scalar extension inverts the pushed lattice map and its restriction counit,
it identifies the canonical intersection with the rational module.
Source: exactness of localization and the pullback universal property.
(auxiliary; not a blueprint node) -/
theorem latticeIntersectionRationalization_isIso_of_map_isIso
    [PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]
    [IsIso ((Mod.extendScalars (coefficientMap a X)).map
      (latticePushedEmbedding a X P p M e))]
    [IsIso ((Mod.extendRestrictAdjunction (coefficientMap a X)).counit.app P)] :
    IsIso (latticeIntersectionRationalization a X P p M e) := by
  have hι : IsIso ((Mod.extendScalars (coefficientMap a X)).map
      (latticeIntersectionι a X P p M e)) := by
    unfold latticeIntersectionι latticeIntersection
    exact imagePullbackι_map_isIso (Mod.extendScalars (coefficientMap a X))
      (latticeIntersectionUnit a X P p) (latticePushedEmbedding a X P p M e)
  have h : latticeIntersectionRationalization a X P p M e =
      (Mod.extendScalars (coefficientMap a X)).map (latticeIntersectionι a X P p M e) ≫
        (Mod.extendRestrictAdjunction (coefficientMap a X)).counit.app P := by
    rfl
  rw [h]
  infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing
