/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackComposition

/-! # Identity normalization of geometric and scalar pullback comparisons

Source: Stacks Project, sites-cohomology.tex, Tag 0E46 (remark-compose-base-change),
identity specialization; Tags 03D8 and 0D6D for the ordinary and derived compositors.
(blueprint: lem-pur-etale-scalar-pullback-identity-normalization).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

private theorem identity_of_composition
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ C) (G : D ⥤ D) (S : C ⥤ D)
    (a : F ≅ 𝟭 C) (b : G ≅ 𝟭 D)
    (c : F ≅ F ⋙ F) (d : G ≅ G ⋙ G) (t : S ⋙ G ≅ F ⋙ S)
    (hc : ∀ X, c.hom.app X ≫ F.map (a.hom.app X) = 𝟙 _)
    (hd : ∀ Y, d.hom.app Y ≫ G.map (b.hom.app Y) = 𝟙 _)
    (ht : ∀ X, d.hom.app (S.obj X) ≫ G.map (t.hom.app X) ≫
      t.hom.app (F.obj X) = t.hom.app X ≫ S.map (c.hom.app X)) (X : C) :
    t.hom.app X ≫ S.map (a.hom.app X) = b.hom.app (S.obj X) := by
  have hn := t.hom.naturality (a.hom.app X)
  simp only [Functor.comp_map, Functor.id_obj] at hn
  have h := congrArg (fun z ↦ z ≫ S.map (F.map (a.hom.app X))) (ht X)
  simp only [Category.assoc] at h
  rw [← hn, ← S.map_comp, hc, S.map_id] at h
  erw [Category.comp_id] at h
  have h' : d.hom.app (S.obj X) ≫
      G.map (t.hom.app X ≫ S.map (a.hom.app X)) = 𝟙 _ := by
    apply (cancel_mono (t.hom.app X)).1
    simpa only [Functor.map_comp, Category.assoc, Category.id_comp] using h
  have : G.Faithful := Functor.Faithful.of_iso b.symm
  apply G.map_injective
  apply (cancel_epi (d.hom.app (S.obj X))).1
  exact h'.trans (hd (S.obj X)).symm

private theorem transport_unit
    {C : Type*} [Category C] (F G : C ⥤ C) (e : F ≅ G) (i : F ≅ 𝟭 C)
    (c : G ≅ G ⋙ G)
    (h : ∀ X, e.hom.app X ≫ c.hom.app X ≫ G.map (e.inv.app X) ≫
      e.inv.app (F.obj X) ≫ F.map (i.hom.app X) = 𝟙 _) (X : C) :
    c.hom.app X ≫ G.map ((e.symm ≪≫ i).hom.app X) = 𝟙 _ := by
  have hn := e.inv.naturality (i.hom.app X)
  have hx := h X
  rw [← hn] at hx
  have hh := congrArg (fun z ↦ e.inv.app X ≫ z ≫ e.hom.app X) hx
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp,
    Category.assoc, Functor.id_obj, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app,
    Category.id_comp, Category.comp_id] using hh

namespace AlgebraicGeometry.Etale

-- Transport the proved derived unit law to the exact derived inverse image.
private theorem exact_identity_unit
    (R : Type (u + 1)) [CommRing R] (T : Scheme.{u})
    (X : DerivedCategoryModule R T) :
    (Functor.mapDerivedCategoryNatIso
        (upperStarComp (ModuleCat.{u + 1} R) (𝟙 T) (𝟙 T) (𝟙 T)
          (Category.id_comp (𝟙 T)).symm) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm).hom.app X ≫
      (upperStar (ModuleCat.{u + 1} R) (𝟙 T)).mapDerivedCategory.map
        (((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} R) (𝟙 T)).symm ≪≫
          leftDerivedUpperStarId (ModuleCat.{u + 1} R) T).hom.app X) = 𝟙 _ := by
  apply transport_unit L(upperStar (ModuleCat.{u + 1} R) (𝟙 T))
    (upperStar (ModuleCat.{u + 1} R) (𝟙 T)).mapDerivedCategory
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} R) (𝟙 T))
    (leftDerivedUpperStarId (ModuleCat.{u + 1} R) T)
  intro E
  have h := leftDerivedUpperStarComp_id_right_hom_app (ModuleCat.{u + 1} R) (𝟙 T) E
  simpa only [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, leftDerivedUpperStarIsoMapDerivedCategory,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc, Iso.inv_hom_id_app_assoc] using h

/-- The canonical identity-identity geometric compositor and scalar/pullback comparison
become identity transformations under the canonical geometric identity comparisons.
Source: Stacks Project, Tag 0E46 (remark-compose-base-change), identity specialization,
with ordinary formulas from Tag 03D8 and derived normalization from Tag 0D6D.
(blueprint: lem-pur-etale-scalar-pullback-identity-normalization).

Proof: (1) Resolve each complex by a flat-term K-flat complex using
lem-pc-kflat-resolution. Geometric pullback and scalar extension are computed on these
models by lem-weil-pbc-ringed-topoi-derived-tensor-pullback and
situation-conventions, with their specified counits.
(2) Write I_R for ordinary identity module pullback and F for scalar extension.
The ordinary identity map h_R sends m tensor r to rm, and the compositor d_R sends
m tensor r to (m tensor 1) tensor r. Thus h_R I_R(h_R) d_R = h_R.
The adjunction-conjugate scalar comparison a of def-pur-scalar-pullback-representative-data
sends (m tensor b) tensor b' to (m tensor 1) tensor bb'. Both adjunction routes send the
unit generator m to (m tensor 1) tensor 1, so this is the specified comparison.
Consequently F(h_A) a = h_B. Tensor balancing gives equality of presheaf maps and of
sheafifications, as in def-pur-sheaf-tensor-product. These degreewise maps introduce no sign.
(3) Localize the first equality. The geometric identity and composition comparisons of
lem-sfb-ringed-derived-monoidal-comparisons are induced by h_R and d_R, giving the first
two conjuncts on all representing complexes.
(4) For a K-flat A-complex P, write r_P for the scalar counit and g_R for the geometric
counit. The defining square of def-pur-etale-scalar-pullback-iso is
lambda ; S(g_A) ; r_(I_A P) = P_B(r_P) ; g_B ; Q(a_P).
The geometric identity is Q(h_R) g_R. Naturality of r with h_A, followed by F(h_A) a = h_B,
therefore gives r_P S(i_A) lambda = r_P i_B. Cancel the invertible r_P, using
lem-pur-derived-change-of-rings, to obtain the third conjunct on K-flat representatives.
(5) Every derived object is isomorphic to such a representative. Naturality transports
each equality along that isomorphism, and cancellation gives the equality at every object.
Conjugating by the identity comparisons now gives identity transformations. Neither
boundedness nor flatness of B over A is used. -/
theorem leftDerivedUpperStarId_scalarExtension_normalization
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) :
    (∀ E : DerivedCategoryModule A T,
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (𝟙 T) (𝟙 T) (𝟙 T)
          (Category.id_comp (𝟙 T)).symm).hom.app E ≫
        L(upperStar (ModuleCat.{u + 1} A) (𝟙 T)).map
          ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) T).hom.app E) ≫
        (leftDerivedUpperStarId (ModuleCat.{u + 1} A) T).hom.app E =
      (leftDerivedUpperStarId (ModuleCat.{u + 1} A) T).hom.app E) ∧
    (∀ E : DerivedCategoryModule B T,
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} B) (𝟙 T) (𝟙 T) (𝟙 T)
          (Category.id_comp (𝟙 T)).symm).hom.app E ≫
        L(upperStar (ModuleCat.{u + 1} B) (𝟙 T)).map
          ((leftDerivedUpperStarId (ModuleCat.{u + 1} B) T).hom.app E) ≫
        (leftDerivedUpperStarId (ModuleCat.{u + 1} B) T).hom.app E =
      (leftDerivedUpperStarId (ModuleCat.{u + 1} B) T).hom.app E) ∧
    (∀ N : DerivedCategoryModule A T,
      (scalarPullbackIso φ (𝟙 T)).hom.app N ≫
        (scalarExtension φ T).map
          ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) T).hom.app N) =
      (leftDerivedUpperStarId (ModuleCat.{u + 1} B) T).hom.app
        ((scalarExtension φ T).obj N)) := by
  -- Use scalar composition and cancellation for the identity specialization.
  refine ⟨?_, ?_, ?_⟩
  · intro E
    simpa only [← Category.assoc, Category.id_comp] using congrArg
      (fun z ↦ z ≫ (leftDerivedUpperStarId (ModuleCat.{u + 1} A) T).hom.app E)
      (leftDerivedUpperStarComp_id_right_hom_app (ModuleCat.{u + 1} A) (𝟙 T) E)
  · intro E
    simpa only [← Category.assoc, Category.id_comp] using congrArg
      (fun z ↦ z ≫ (leftDerivedUpperStarId (ModuleCat.{u + 1} B) T).hom.app E)
      (leftDerivedUpperStarComp_id_right_hom_app (ModuleCat.{u + 1} B) (𝟙 T) E)
  · intro N
    let eA := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (𝟙 T)
    let eB := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) (𝟙 T)
    let iA := leftDerivedUpperStarId (ModuleCat.{u + 1} A) T
    let iB := leftDerivedUpperStarId (ModuleCat.{u + 1} B) T
    let t := Functor.isoWhiskerLeft (scalarExtension φ T) eB.symm ≪≫
      scalarPullbackIso φ (𝟙 T) ≪≫ Functor.isoWhiskerRight eA (scalarExtension φ T)
    have ht := identity_of_composition
      (upperStar (ModuleCat.{u + 1} A) (𝟙 T)).mapDerivedCategory
      (upperStar (ModuleCat.{u + 1} B) (𝟙 T)).mapDerivedCategory
      (scalarExtension φ T) (eA.symm ≪≫ iA) (eB.symm ≪≫ iB)
      (Functor.mapDerivedCategoryNatIso
        (upperStarComp (ModuleCat.{u + 1} A) (𝟙 T) (𝟙 T) (𝟙 T)
          (Category.id_comp (𝟙 T)).symm) ≪≫ (Functor.mapDerivedCategoryCompIso _ _).symm)
      (Functor.mapDerivedCategoryNatIso
        (upperStarComp (ModuleCat.{u + 1} B) (𝟙 T) (𝟙 T) (𝟙 T)
          (Category.id_comp (𝟙 T)).symm) ≪≫ (Functor.mapDerivedCategoryCompIso _ _).symm) t
      (exact_identity_unit A T) (exact_identity_unit B T)
      (fun X ↦ scalarPullback_composition φ (𝟙 T) (𝟙 T) (𝟙 T)
        (Category.id_comp (𝟙 T)) X) N
    simp only [t, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp,
      Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app] at ht
    erw [CategoryTheory.Functor.map_id, Category.id_comp] at ht
    apply (cancel_epi (eB.inv.app ((scalarExtension φ T).obj N))).1
    exact ht

end AlgebraicGeometry.Etale
