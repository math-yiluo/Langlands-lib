/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
import WeilConjectures.AlgebraicGeometry.InversePartialMapRestrictions

/-!
# Restricting generically inverse partial maps

Source: Stacks Project, Tag 0552, the inverse rational map argument, together with
Tag 01RR (rational maps determined at the generic point).
(blueprint: lem-sbc-generic-inverse-partial-map-restrictions)
-/

@[expose] public section

universe u
open CategoryTheory Topology IsLocalRing
namespace AlgebraicGeometry.Scheme.PartialMap

private lemma dominant_of_generic_iso
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X.PartialMap Y) (e : Spec X.functionField ≅ Spec Y.functionField)
    (hf : f.fromFunctionField = e.hom ≫ Y.fromSpecStalk (genericPoint Y)) :
    IsDominant f.hom := by
  have he : e.hom (closedPoint X.functionField) = closedPoint Y.functionField :=
    @Subsingleton.elim (PrimeSpectrum Y.functionField) inferInstance _ _
  have hpoint := congrArg (fun k : Spec X.functionField ⟶ Y ↦
    k (closedPoint X.functionField)) hf
  simp only [Hom.comp_apply, he, fromSpecStalk_closedPoint] at hpoint
  refine ⟨?_⟩
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_univ_subset
  rw [← genericPoint_spec Y]
  apply closure_mono
  rw [Set.singleton_subset_iff]
  exact ⟨_, hpoint⟩

set_option backward.defeqAttrib.useBackward true in
private lemma comp_fromFunctionField_of_generic_inverse
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap X)
    (e : Spec X.functionField ≅ Spec Y.functionField)
    (hf : f.fromFunctionField = e.hom ≫ Y.fromSpecStalk (genericPoint Y))
    (hg : g.fromFunctionField = e.inv ≫ X.fromSpecStalk (genericPoint X)) :
    (f.comp g).fromFunctionField = X.fromSpecStalk (genericPoint X) := by
  let W := (f.comp g).domain
  have hWf : W ≤ f.domain := f.domain.ι_image_le _
  let k : W.toScheme ⟶ g.domain.toScheme :=
    (f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).inv ≫ f.hom ∣_ g.domain
  have hk : k ≫ g.domain.ι = X.homOfLE hWf ≫ f.hom := by
    dsimp [k]
    simp only [Category.assoc, morphismRestrict_ι]
    rw [← Category.assoc]
    congr 1
    exact f.domain.isoImage_ι_inv_ι _
  have hxW : genericPoint X ∈ W :=
    ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr
      (by simpa only [Set.univ_inter] using (f.comp g).dense_domain.nonempty)
  have hxF : genericPoint X ∈ f.domain := hWf hxW
  have hyG : genericPoint Y ∈ g.domain :=
    ((genericPoint_spec Y).mem_open_set_iff g.domain.isOpen).mpr
      (by simpa using g.dense_domain.nonempty)
  have hl : W.fromSpecStalkOfMem (genericPoint X) hxW ≫ X.homOfLE hWf =
      f.domain.fromSpecStalkOfMem (genericPoint X) hxF := by
    apply (cancel_mono f.domain.ι).mp
    simp
  have H : W.fromSpecStalkOfMem (genericPoint X) hxW ≫ k =
      e.hom ≫ g.domain.fromSpecStalkOfMem (genericPoint Y) hyG := by
    apply (cancel_mono g.domain.ι).mp
    rw [Category.assoc, hk, ← Category.assoc, hl]
    change f.fromFunctionField = _
    simpa using hf
  change W.fromSpecStalkOfMem (genericPoint X) hxW ≫ (k ≫ g.hom) = _
  rw [← Category.assoc, H, Category.assoc]
  change e.hom ≫ g.fromFunctionField = _
  rw [hg]
  simp

/-- Partial maps inducing inverse generic isomorphisms become inverse morphisms on
smaller dense opens. The forward morphism is a restriction of the supplied partial map.

Source: Stacks Project, Tag 0552, inverse rational map argument; Tag 01RR.
Proof: The two partial maps are dominant, since their generic maps send generic point
 to generic point. Compose them on the inverse images of their domains. At the generic
point both composites are the identity, by the two inverse identities of e. Equality
at the generic point makes the composites equal to the identity on dense open subsets
W_X and W_Y, using injectivity of germs of integral schemes. Shrink W_X to lie in the
forward domain and in the inverse image of W_Y. Put U = W_X intersect f^{-1}(W_Y)
and V = W_Y intersect g^{-1}(U). The equalities g f = id on W_X and f g = id on W_Y
show that f maps U into V and g maps V into U. These opens contain the generic points
and hence are dense. Restrict f and g to them. Cancelling the open inclusions proves
both inverse identities and gives the asserted equality with the original forward map.

(blueprint: lem-sbc-generic-inverse-partial-map-restrictions) -/
theorem exists_inverse_restrictions_of_generic_inverse
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X.PartialMap Y) (g : Y.PartialMap X)
    (e : Spec X.functionField ≅ Spec Y.functionField)
    (hf : f.fromFunctionField = e.hom ≫ Y.fromSpecStalk (genericPoint Y))
    (hg : g.fromFunctionField = e.inv ≫ X.fromSpecStalk (genericPoint X)) :
    ∃ (U : X.Opens) (_ : Dense (U : Set X)) (hUf : U ≤ f.domain)
      (V : Y.Opens) (_ : Dense (V : Set Y))
      (f' : U.toScheme ⟶ V.toScheme) (g' : V.toScheme ⟶ U.toScheme),
      f' ≫ g' = 𝟙 _ ∧ g' ≫ f' = 𝟙 _ ∧
        f' ≫ V.ι = X.homOfLE hUf ≫ f.hom := by
  have := dominant_of_generic_iso f e hf
  have := dominant_of_generic_iso g e.symm hg
  let fg := f.comp g
  let gf := g.comp f
  have hfg : fg.fromFunctionField = X.fromSpecStalk (genericPoint X) :=
    comp_fromFunctionField_of_generic_inverse f g e hf hg
  have hgf : gf.fromFunctionField = Y.fromSpecStalk (genericPoint Y) :=
    comp_fromFunctionField_of_generic_inverse g f e.symm hg hf
  have hfg' : fg.equiv (PartialMap.id X) := by
    apply equiv_of_fromSpecStalkOfMem_eq fg (PartialMap.id X) (x := genericPoint X)
      (hxf := (genericPoint_spec X).mem_open_set_iff fg.domain.isOpen |>.mpr
        (by simpa using fg.dense_domain.nonempty)) (hxg := trivial)
    simpa using hfg
  have hgf' : gf.equiv (PartialMap.id Y) := by
    apply equiv_of_fromSpecStalkOfMem_eq gf (PartialMap.id Y) (x := genericPoint Y)
      (hxf := (genericPoint_spec Y).mem_open_set_iff gf.domain.isOpen |>.mpr
        (by simpa using gf.dense_domain.nonempty)) (hxg := trivial)
    simpa using hgf
  exact exists_inverse_restrictions_of_comp_equiv_id f g hfg' hgf'

end AlgebraicGeometry.Scheme.PartialMap
