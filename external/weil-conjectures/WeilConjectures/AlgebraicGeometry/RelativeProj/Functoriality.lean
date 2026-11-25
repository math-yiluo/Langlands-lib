/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps

/-!
# Functoriality of the relative `Proj`

A morphism `f: A ⟶ B` of quasi-coherent graded algebras on `X` satisfying the irrelevant ideal
condition on every affine open induces a morphism `relProjMap f: B.relProj ⟶ A.relProj` over
`X`, glued from the morphisms `Proj.map (f.app V)`.

## Main results

- `AlgebraicGeometry.Scheme.GradedAlgebraData.relProjMap` — the induced morphism, with
  `relProjMap_id` and `relProjMap_comp`.
- `AlgebraicGeometry.Scheme.GradedAlgebraData.relProjIsoOfIso` — a degree-preserving isomorphism
  of graded algebras induces an isomorphism of relative `Proj`s over `X`.
- `AlgebraicGeometry.Scheme.GradedAlgebraData.isClosedImmersion_relProjMap` — a surjective
  degree-preserving morphism induces a closed immersion in the opposite direction.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.GradedAlgebraData

variable {X : Scheme.{u}} {A B C : X.GradedAlgebraData}

/-- The irrelevant ideal condition for a morphism of graded algebras, on every affine open. -/
abbrev IrrelevantLE (f : A ⟶ B) : Prop :=
  ∀ U : X.affineOpens, HomogeneousIdeal.irrelevant (B.grading U) ≤
    (HomogeneousIdeal.irrelevant (A.grading U)).map (f.app U)

lemma irrelevantLE_of_surjective (f : A ⟶ B) (hf : ∀ U, Function.Surjective (f.app U)) :
    IrrelevantLE f := fun U ↦ GradedRingHom.irrelevant_le_map_of_surjective (hf U)

lemma irrelevantLE_id : IrrelevantLE (𝟙 A) := fun U ↦ by simp

lemma IrrelevantLE.comp {f : A ⟶ B} {g : B ⟶ C} (hf : IrrelevantLE f) (hg : IrrelevantLE g) :
    IrrelevantLE (f ≫ g) := fun U ↦ HomogeneousIdeal.irrelevant_le_map_comp (hf U) (hg U)

lemma comp_res_eq (f : A ⟶ B) {U V : X.affineOpens} (h : U ≤ V) :
    (B.res h).comp (f.app V) = (f.app U).comp (A.res h) :=
  GradedRingHom.ext fun x ↦ (f.naturality h x).symm

variable (f : A ⟶ B) (hf : IrrelevantLE f)

/-- The local structure morphisms commute with `Proj.map (f.app U)`. -/
@[reassoc]
lemma map_app_toOpen (U : X.affineOpens) :
    Proj.map (f.app U) (hf U) ≫ A.toOpen U = B.toOpen U := by
  rw [toOpen_eq, toOpen_eq, ← Category.assoc,
    Proj.map_toSpecOfAlgebra_of_comp (RingHom.id _) (f.app U) (f.app_algebraMap U) (hf U),
    CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]

lemma map_res_map_app_relProjι {U V : X.affineOpens} (h : U ≤ V) :
    Proj.map (B.res h) (B.irrelevant_le_map_res h) ≫ Proj.map (f.app V) (hf V) ≫
      A.relProjι V = Proj.map (f.app U) (hf U) ≫ A.relProjι U := by
  rw [← Category.assoc, ← Proj.map_comp, Proj.map_congr (comp_res_eq f h) _
    (HomogeneousIdeal.irrelevant_le_map_comp (A.irrelevant_le_map_res h) (hf U)),
    Proj.map_comp _ _ (A.irrelevant_le_map_res h) (hf U), Category.assoc]
  exact congrArg _ (A.relProjFunctor_map_relProjι (homOfLE h))

/-- The morphism of relative `Proj`s induced by a morphism of graded algebras satisfying the
irrelevant ideal condition. -/
noncomputable def relProjMap : B.relProj ⟶ A.relProj :=
  colimit.desc B.relProjFunctor
    { pt := A.relProj
      ι :=
        { app U := Proj.map (f.app U) (hf U) ≫ A.relProjι U
          naturality _ _ h :=
            (map_res_map_app_relProjι f hf (leOfHom h)).trans (Category.comp_id _).symm } }

@[reassoc (attr := simp)]
lemma relProjι_relProjMap (U : X.affineOpens) :
    B.relProjι U ≫ relProjMap f hf = Proj.map (f.app U) (hf U) ≫ A.relProjι U :=
  colimit.ι_desc _ U

/-- The induced morphism lies over `X`. -/
@[reassoc (attr := simp)]
lemma relProjMap_relProjHom : relProjMap f hf ≫ A.relProjHom = B.relProjHom := by
  refine colimit.hom_ext fun U ↦ ?_
  change B.relProjι U ≫ _ = B.relProjι U ≫ _
  rw [relProjι_relProjMap_assoc, relProjι_relProjHom, relProjι_relProjHom,
    map_app_toOpen_assoc]

lemma relProjMap_preimage_opensRange (U : X.affineOpens) :
    relProjMap f hf ⁻¹ᵁ (A.relProjι U).opensRange = (B.relProjι U).opensRange := by
  rw [← relProjHom_preimage, ← relProjHom_preimage, ← Scheme.Hom.comp_preimage,
    relProjMap_relProjHom]

lemma relProjMap_id : relProjMap (𝟙 A) irrelevantLE_id = 𝟙 A.relProj := by
  refine colimit.hom_ext fun U ↦ ?_
  change A.relProjι U ≫ _ = A.relProjι U ≫ _
  rw [relProjι_relProjMap, Category.comp_id]
  exact (Proj.map_congr (id_app U) _ (by simp)).trans Proj.map_id ▸ Category.id_comp _

lemma relProjMap_comp (g : B ⟶ C) (hg : IrrelevantLE g) :
    relProjMap (f ≫ g) (hf.comp hg) = relProjMap g hg ≫ relProjMap f hf := by
  refine colimit.hom_ext fun U ↦ ?_
  change C.relProjι U ≫ _ = C.relProjι U ≫ _
  rw [relProjι_relProjMap, relProjι_relProjMap_assoc, relProjι_relProjMap, ← Category.assoc,
    ← Proj.map_comp]
  rfl

/-- **Isomorphisms of graded algebras induce isomorphisms of relative `Proj`**: a
degree-preserving isomorphism `e: A ≅ B` of quasi-coherent graded algebras (which is compatible
with the `Γ(X, U)`-algebra structures, i.e. induces the identity on the degree-zero base) induces
an isomorphism `B.relProj ≅ A.relProj` over `X`. -/
noncomputable def relProjIsoOfIso (e : A ≅ B) : B.relProj ≅ A.relProj where
  hom := relProjMap e.hom (irrelevantLE_of_surjective e.hom fun U x ↦
    ⟨e.inv.app U x, by rw [← GradedRingHom.comp_apply, ← comp_app, e.inv_hom_id]; rfl⟩)
  inv := relProjMap e.inv (irrelevantLE_of_surjective e.inv fun U x ↦
    ⟨e.hom.app U x, by rw [← GradedRingHom.comp_apply, ← comp_app, e.hom_inv_id]; rfl⟩)
  hom_inv_id := by
    rw [← relProjMap_comp, ← relProjMap_id]
    congr 1
    exact e.inv_hom_id
  inv_hom_id := by
    rw [← relProjMap_comp, ← relProjMap_id]
    congr 1
    exact e.hom_inv_id

@[reassoc (attr := simp)]
lemma relProjIsoOfIso_hom_relProjHom (e : A ≅ B) :
    (relProjIsoOfIso e).hom ≫ A.relProjHom = B.relProjHom :=
  relProjMap_relProjHom _ _

lemma iSup_opensRange_relProjι : ⨆ U : X.affineOpens, (A.relProjι U).opensRange = ⊤ := by
  simp_rw [← relProjHom_preimage]
  rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]

/-- **Surjections of graded algebras induce closed immersions**: if `f: A ⟶ B` is surjective on
every affine open, then `relProjMap f: B.relProj ⟶ A.relProj` is a closed immersion. -/
theorem isClosedImmersion_relProjMap (hsurj : ∀ U, Function.Surjective (f.app U)) :
    IsClosedImmersion (relProjMap f (irrelevantLE_of_surjective f hsurj)) := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion) _
    iSup_opensRange_relProjι fun U ↦ ?_
  have e := morphismRestrictArrowIso (relProjMap f (irrelevantLE_of_surjective f hsurj))
    (Proj.map (f.app U) (irrelevantLE_of_surjective f hsurj U))
    (relProjι_relProjMap _ _ U) (relProjMap_preimage_opensRange _ _ U)
  exact (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion e).mpr
    (Proj.isClosedImmersion_map _ _ (hsurj U))

end AlgebraicGeometry.Scheme.GradedAlgebraData
