/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.KInjectiveMayerVietorisData
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
/-! # Evaluation of the transported nested-open restriction

Source: Stacks Project, Cohomology, Tag 08BV.
(blueprint: lem-pc-open-module-image-section-restriction).
-/
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option autoImplicit false
namespace AlgebraicGeometry

/-- The overlap mate is ordinary restriction after the open-site comparisons.
Source: Stacks Project, Cohomology, Tag 08BV (lemma-exact-sequence-j-star),
sectionwise sequence, with the concrete maps of
`schemeOpenModuleImageRestriction`.
(blueprint: lem-pc-open-module-image-section-restriction)
Proof: Conjugate the nested-open restriction by the direct images of
`overFunctorEquiv`. The proved `schemeOpenModuleImage_unit_restriction`
identity, together with `ofNatIsoLeft_unit`, says that this ordinary map
composes with the U-restriction unit to give the W-restriction unit.
Put P = U ∩ T and Q = W ∩ T. Evaluate that identity at P and apply
naturality of the ordinary map along P ⊆ T. Both source restrictions are
the same map from M(P) to M(U ∩ P); the resulting equation identifies
restriction of the desired value to W ∩ P with restriction of the input.
Since W ⊆ U, W ∩ P = Q, so that restriction is an isomorphism. Cancel it
and combine the presheaf restriction maps. Finally cancel the inverse and
forward U-comparisons to recover the original transported expression.
The image-preimage opens equal these intersections by
`image_preimage_eq_opensRange_inf` and `opensRange_ι`. This works for
empty and equal opens and needs no cover or amalgamation.
-/
theorem schemeOpenModuleImage_section_restriction
    (X : Scheme.{u}) {W U : X.Opens} (i : W ⟶ U)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (T : X.Opens)
    (a : ((schemeOpenModuleImage X U).obj M).val.obj (.op T)) :
    (((Scheme.Modules.pushforward W.ι).map
      ((Scheme.Modules.overFunctorEquiv W).hom.app M)).val.app (.op T))
      (((schemeOpenModuleImageRestriction X i).app M).val.app (.op T) a) =
    M.val.map (homOfLE (show W.ι ''ᵁ (W.ι ⁻¹ᵁ T) ≤ U.ι ''ᵁ (U.ι ⁻¹ᵁ T) by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
        Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
        Scheme.Opens.opensRange_ι]
      exact inf_le_inf_right T (leOfHom i))).op
      ((((Scheme.Modules.pushforward U.ι).map
        ((Scheme.Modules.overFunctorEquiv U).hom.app M)).val.app (.op T)) a) := by
  let e (A : X.Opens) := (Scheme.Modules.pushforward A.ι).mapIso
    ((Scheme.Modules.overFunctorEquiv A).app M)
  let f := (e U).inv ≫ (schemeOpenModuleImageRestriction X i).app M ≫ (e W).hom
  have hf : (Scheme.Modules.restrictAdjunction U.ι).unit.app M ≫ f =
      (Scheme.Modules.restrictAdjunction W.ι).unit.app M := by
    have h := schemeOpenModuleImage_unit_restriction X i M
    simp only [schemeOpenModuleAdjunction, Adjunction.ofNatIsoLeft_unit,
      NatTrans.comp_app, Functor.whiskerRight_app] at h
    simp only [Iso.symm_hom, Category.assoc] at h
    change (Scheme.Modules.restrictAdjunction U.ι).unit.app M ≫
      (e U).inv ≫ (schemeOpenModuleImageRestriction X i).app M =
        (Scheme.Modules.restrictAdjunction W.ι).unit.app M ≫ (e W).inv at h
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      congrArg (fun k ↦ k ≫ (e W).hom) h
  let P := U.ι ''ᵁ (U.ι ⁻¹ᵁ T)
  let Q := W.ι ''ᵁ (W.ι ⁻¹ᵁ T)
  let j : P ⟶ T := homOfLE (U.ι.image_preimage_le T)
  have hQ : W.ι ''ᵁ (W.ι ⁻¹ᵁ P) = Q := by
    dsimp [P, Q]
    simp only [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    rw [← inf_assoc, inf_eq_left.mpr (leOfHom i)]
  let k : Q ⟶ P := homOfLE (by
    dsimp [P, Q]
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      Scheme.Opens.opensRange_ι]
    exact inf_le_inf_right T (leOfHom i))
  let b : M.val.obj (.op P) := (e U).hom.val.app (.op T) a
  have h := congrArg (fun k ↦ k.val.app (.op P) b) hf
  change f.val.app (.op P) (M.val.map (homOfLE (U.ι.image_preimage_le P)).op b) =
    M.val.map (homOfLE (W.ι.image_preimage_le P)).op b at h
  have n := PresheafOfModules.naturality_apply f.val j.op b
  change f.val.app (.op P) (M.val.map (homOfLE (U.ι.image_preimage_le P)).op b) =
    M.val.map (homOfLE hQ.le).op (f.val.app (.op T) b) at n
  have hn := n.symm.trans h
  have hi : IsIso (homOfLE hQ.le) := by
    rw [show homOfLE hQ.le = eqToHom hQ from Subsingleton.elim _ _]
    infer_instance
  have hb : f.val.app (.op T) b = M.val.map k.op b := by
    apply (ConcreteCategory.bijective_of_isIso
      (M.val.presheaf.map (homOfLE hQ.le).op)).1
    change M.val.map (homOfLE hQ.le).op (f.val.app (.op T) b) =
      M.val.map (homOfLE hQ.le).op (M.val.map k.op b)
    rw [hn, ← M.val.map_comp_apply]
    congr 1
  have hc : (e U).hom ≫ f =
      (schemeOpenModuleImageRestriction X i).app M ≫ (e W).hom := by
    dsimp [f]
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have ht := congrArg (fun k ↦ k.val.app (.op T) a) hc
  change f.val.app (.op T) b =
    (e W).hom.val.app (.op T)
      (((schemeOpenModuleImageRestriction X i).app M).val.app (.op T) a) at ht
  exact ht.symm.trans hb
end AlgebraicGeometry
