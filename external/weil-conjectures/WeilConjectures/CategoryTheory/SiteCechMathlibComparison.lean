/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

import Mathlib.Algebra.Category.Grp.Biproducts
public import WeilConjectures.CategoryTheory.SiteCechComplex
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-!
# Comparing chosen-product and Mathlib Čech complexes

Source: Stacks Project, Cohomology on Sites, Tags 03AK and 03AM.
(blueprint: lem-weil-pbc-site-cech-mathlib-comparison)
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SiteCechComplex

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

private noncomputable def tupleProductIso {J : Type w} (A : J → AddCommGrpCat.{w}) :
    AddCommGrpCat.of (∀ j, A j) ≅ ∏ᶜ A :=
  (AddCommGrpCat.HasLimit.productLimitCone A).isLimit.conePointUniqueUpToIso
    (limit.isLimit _)

private noncomputable def chosenFan
    {C : Type u} [Category.{v} C] {U : C} {I : Type w}
    {V : I → C} {f : ∀ i, V i ⟶ U} (S : SiteCechComplex V f)
    (p : ℕ) (t : Fin (p + 1) → I) : Fan (fun k ↦ Over.mk (f (t k))) :=
  Fan.mk (Over.mk (S.pr p t 0 ≫ f (t 0)))
    (fun k ↦ Over.homMk (S.pr p t k) (S.comm p t k))

private noncomputable def chosenFanIsLimit
    {C : Type u} [Category.{v} C] {U : C} {I : Type w}
    {V : I → C} {f : ∀ i, V i ⟶ U} (S : SiteCechComplex V f)
    (p : ℕ) (t : Fin (p + 1) → I) : IsLimit (chosenFan S p t) := by
  classical
  have hu (s : Fan (fun k ↦ Over.mk (f (t k)))) :=
    S.universal p t s.pt.left (fun k ↦ (s.proj k).left)
      (fun k ↦ (Over.w (s.proj k)).trans (Over.w (s.proj 0)).symm)
  refine Fan.IsLimit.mk _
    (fun s ↦ Over.homMk (hu s).choose ?_) ?_ ?_
  · change (hu s).choose ≫ (S.pr p t 0 ≫ f (t 0)) = s.pt.hom
    rw [← Category.assoc, (hu s).choose_spec.1 0]
    exact Over.w (s.proj 0)
  · intro s k
    apply Over.OverMorphism.ext
    exact (hu s).choose_spec.1 k
  · intro s m hm
    apply Over.OverMorphism.ext
    apply (hu s).choose_spec.2 m.left
    intro k
    exact congrArg (fun a ↦ a.left) (hm k)

private noncomputable def productIso
    {C : Type u} [Category.{v} C] [HasFiniteWidePullbacks C]
    {U : C} {I : Type w} {V : I → C} {f : ∀ i, V i ⟶ U}
    (S : SiteCechComplex V f) (p : ℕ) (t : Fin (p + 1) → I) :
    (chosenFan S p t).pt ≅ ∏ᶜ (fun k ↦ Over.mk (f (t k))) :=
  (chosenFanIsLimit S p t).conePointUniqueUpToIso (limit.isLimit _)

private theorem tupleProductIso_hom_π {J : Type w} (A : J → AddCommGrpCat.{w}) (j : J) :
    (tupleProductIso A).hom ≫ Pi.π A j =
      AddCommGrpCat.ofHom (Pi.evalAddMonoidHom (fun j ↦ A j) j) := by
  unfold tupleProductIso
  exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ (Discrete.mk j)

private theorem productIso_inv_π
    {C : Type u} [Category.{v} C] [HasFiniteWidePullbacks C]
    {U : C} {I : Type w} {V : I → C} {f : ∀ i, V i ⟶ U}
    (S : SiteCechComplex V f) (p : ℕ) (t : Fin (p + 1) → I) (k : Fin (p + 1)) :
    (productIso S p t).inv ≫ (chosenFan S p t).proj k =
      Pi.π (fun k ↦ Over.mk (f (t k))) k := by
  exact IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk k)

private noncomputable def degreeIso
    {C : Type u} [Category.{v} C] [HasFiniteWidePullbacks C]
    {U : C} {I : Type w} {V : I → C} {f : ∀ i, V i ⟶ U}
    (S : SiteCechComplex V f) (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (p : ℕ) :
    S.cochains F p ≅
      ∏ᶜ (fun t : Fin (p + 1) → I ↦
        F.obj (Opposite.op (∏ᶜ (fun k ↦ Over.mk (f (t k)))).left)) :=
  tupleProductIso _ ≪≫ Pi.mapIso (fun t ↦
    F.mapIso (((Over.forget U).mapIso (productIso S p t)).symm.op))

private theorem productIso_inv_indexMap
    {C : Type u} [Category.{v} C] [HasFiniteWidePullbacks C]
    {U : C} {I : Type w} {V : I → C} {f : ∀ i, V i ⟶ U}
    (S : SiteCechComplex V f) {p q : ℕ} (t : Fin (p + 1) → I)
    (α : Fin (q + 1) → Fin (p + 1)) :
    (Pi.lift (fun k ↦ Pi.π (fun k ↦ Over.mk (f (t k))) (α k)) :
      (∏ᶜ (fun k ↦ Over.mk (f (t k)))) ⟶
        ∏ᶜ (fun k ↦ Over.mk (f ((t ∘ α) k)))).left ≫
        (productIso S q (t ∘ α)).inv.left =
      (productIso S p t).inv.left ≫ S.indexMap t α := by
  have hπ (p : ℕ) (t : Fin (p + 1) → I) (k : Fin (p + 1)) :
      (productIso S p t).inv.left ≫ S.pr p t k =
        (Pi.π (fun k ↦ Over.mk (f (t k))) k).left :=
    congrArg (fun a ↦ a.left) (productIso_inv_π S p t k)
  have hc (k) :
      ((productIso S p t).inv.left ≫ S.indexMap t α ≫ S.pr q (t ∘ α) k) ≫
        f ((t ∘ α) k) =
      ((productIso S p t).inv.left ≫ S.indexMap t α ≫ S.pr q (t ∘ α) 0) ≫
        f ((t ∘ α) 0) := by
    simp only [Category.assoc, S.comm]
  obtain ⟨b, _, hb⟩ := S.universal q (t ∘ α) _
    (fun k ↦ (productIso S p t).inv.left ≫ S.indexMap t α ≫ S.pr q (t ∘ α) k) hc
  apply (hb _ ?_).trans (hb _ (fun _ ↦ Category.assoc _ _ _)).symm
  intro k
  rw [Category.assoc, hπ]
  rw [← Over.comp_left]
  simp only [Pi.lift_comp_π]
  rw [S.indexMap_pr, hπ]

private theorem degreeIso_hom_π
    {C : Type u} [Category.{v} C] [HasFiniteWidePullbacks C]
    {U : C} {I : Type w} {V : I → C} {f : ∀ i, V i ⟶ U}
    (S : SiteCechComplex V f) (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (p : ℕ)
    (t : Fin (p + 1) → I) :
    (degreeIso S F p).hom ≫ Pi.π _ t =
      AddCommGrpCat.ofHom (Pi.evalAddMonoidHom (fun t ↦ F.obj (Opposite.op (S.W p t))) t) ≫
        F.map (productIso S p t).inv.left.op := by
  simp only [degreeIso, Iso.trans_hom, Category.assoc, Pi.mapIso_hom_π]
  rw [← Category.assoc, tupleProductIso_hom_π]
  rfl

private def sectionIndexMap
    {C : Type u} [Category.{v} C] {U : C} {I : Type w}
    {V : I → C} {f : ∀ i, V i ⟶ U} (S : SiteCechComplex V f)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) {p q : ℕ}
    (α : Fin (q + 1) → Fin (p + 1)) : S.cochains F q ⟶ S.cochains F p :=
  AddCommGrpCat.ofHom
    { toFun := fun s t ↦ F.map (S.indexMap t α).op (s (t ∘ α))
      map_zero' := by funext t; exact (F.map (S.indexMap t α).op).hom.map_zero
      map_add' := by intro a b; funext t; exact (F.map (S.indexMap t α).op).hom.map_add _ _ }

private theorem degreeIso_indexMap
    {C : Type u} [Category.{v} C] [HasFiniteWidePullbacks C]
    {U : C} {I : Type w} {V : I → C} {f : ∀ i, V i ⟶ U}
    (S : SiteCechComplex V f) (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) {p q : ℕ}
    (α : Fin (q + 1) → Fin (p + 1)) :
    (degreeIso S F q).hom ≫
      Pi.lift (fun t : Fin (p + 1) → I ↦ Pi.π _ (t ∘ α) ≫
        F.map (Pi.lift (fun k ↦ Pi.π (fun k ↦ Over.mk (f (t k))) (α k))).left.op) =
      sectionIndexMap S F α ≫ (degreeIso S F p).hom := by
  apply Pi.hom_ext
  intro t
  simp only [Category.assoc, Pi.lift_comp_π]
  rw [← Category.assoc, degreeIso_hom_π, Category.assoc, degreeIso_hom_π]
  apply AddCommGrpCat.ext
  intro s
  change F.map (Pi.lift (fun k ↦ Pi.π (fun k ↦ Over.mk (f (t k))) (α k))).left.op
      (F.map (productIso S q (t ∘ α)).inv.left.op (s (t ∘ α))) =
    F.map (productIso S p t).inv.left.op
      (F.map (S.indexMap t α).op (s (t ∘ α)))
  have h := congrArg (fun a ↦ F.map a.op) (productIso_inv_indexMap S t α)
  simp only [op_comp, F.map_comp] at h
  exact congrArg (fun a ↦ a (s (t ∘ α))) h

private theorem differential_sum
    {C : Type u} [Category.{v} C] {U : C} {I : Type w}
    {V : I → C} {f : ∀ i, V i ⟶ U} (S : SiteCechComplex V f)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (p : ℕ) :
    S.differential F p =
      ∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val • sectionIndexMap S F j.succAbove := by
  apply AddCommGrpCat.ext
  intro s
  apply funext
  intro t
  change S.differentialValue F p s t =
    (AddCommGrpCat.homAddEquiv
      (∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val • sectionIndexMap S F j.succAbove) s) t
  rw [map_sum]
  simp only [map_zsmul, AddMonoidHom.finsetSum_apply, AddMonoidHom.zsmul_apply]
  change (∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
      F.map (S.indexMap t j.succAbove).op (s (t ∘ j.succAbove))) =
    (∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
      (fun t ↦ F.map (S.indexMap t j.succAbove).op (s (t ∘ j.succAbove)))) t
  simp only [Finset.sum_apply, Pi.smul_apply]

/-- Any choice of the iterated fibre products gives the Mathlib Čech complex up to
isomorphism, for every abelian presheaf and every family of arrows.

Source: Stacks Project, Cohomology on Sites, Tags 03AK and 03AM; the universal-property
comparison in step 3 of lem-weil-pbc-injective-etale-module-cech-h1.
(blueprint: lem-weil-pbc-site-cech-mathlib-comparison)

Proof: For each tuple t, the underlying object of the categorical product of the
objects Over.mk (hom (t k)) is a fibre product over U. Its projections satisfy the
same universal property as S.W p t. The unique projection-compatible maps in both
directions are inverse, since both composites have the identity's projections.
Restriction along these isomorphisms identifies the section groups. The categorical
product of abelian groups is isomorphic to the group of tuples of sections, by its
projection universal property, so these identifications give an isomorphism in each
degree. For every index injection omitting one factor, both composites of the product
comparison and the corresponding index maps have the same projections, hence agree.
Functoriality of restriction shows that the degree isomorphisms commute with every
term of the alternating sum, and therefore with the differential. Their inverses
also commute, yielding an isomorphism of cochain complexes. Empty families cause no
exception: the products of section groups over the empty tuple-index set are zero
objects in every degree. No sheaf, covering or injectivity hypothesis is used. -/
theorem mathlib_complex_iso_exists
    {C : Type u} [Category.{v} C] [HasFiniteWidePullbacks C]
    {U : C} {I : Type w} (V : I → C) (f : ∀ i, V i ⟶ U)
    (S : SiteCechComplex V f) (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) :
    Nonempty (S.complex F ≅
      (cechComplexFunctor fun i : I ↦ Over.mk (f i)).obj ((Over.forget U).op ⋙ F)) := by
  classical
  refine ⟨HomologicalComplex.Hom.isoOfComponents (fun p ↦ degreeIso S F p) ?_⟩
  intro p q h
  have hq : p + 1 = q := h
  subst q
  simp only [complex, cechComplexFunctor, Limits.FormalCoproduct.cochainComplexFunctor,
    Functor.comp_obj, AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d]
  change (degreeIso S F p).hom ≫
      AlgebraicTopology.AlternatingCofaceMapComplex.objD
        ((Limits.FormalCoproduct.cosimplicialObjectFunctor
          (Limits.FormalCoproduct.mk _ (fun i : I ↦ Over.mk (f i))).cech).obj
            ((Over.forget U).op ⋙ F)) p =
    S.differential F p ≫ (degreeIso S F (p + 1)).hom
  rw [differential_sum]
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD,
    Preadditive.comp_sum, Preadditive.sum_comp,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact degreeIso_indexMap S F j.succAbove

end CategoryTheory.SiteCechComplex
