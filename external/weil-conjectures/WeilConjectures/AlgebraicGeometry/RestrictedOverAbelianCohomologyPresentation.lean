/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RestrictedOverAbelianComplexData
import all WeilConjectures.AlgebraicGeometry.RawAffineComplexSystemMapCoherence
import all WeilConjectures.AlgebraicGeometry.RestrictedOverSingleUnit
import WeilConjectures.AlgebraicGeometry.RestrictedOverSingleComposition

/-! # Canonical restricted abelian cohomology diagrams

Source: Stacks Project, Tags 09Z1 and 0EZM.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale


private theorem restrictedOverCohomologyMap_eq
    {W S : Scheme.{u}} (k : W ⟶ S)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)
    {A B : Over W} (f : A ⟶ B) (U : S.Etale) :
    restrictedOverCohomologyMap k F q f U =
      rawAffineComplexPullback q
        (rawAffineRestrictedMap f.left (B.hom ≫ k) (A.hom ≫ k)
          (by rw [← Category.assoc, Over.w]) U)
        (restrictedOverSingle k F B U) ≫
        (cohomology AddCommGrpCat.{u + 1} (pullback U.hom (A.hom ≫ k)) q).map
          (DerivedCategory.Q.map (restrictedOverSingleIso k F f U).hom) := by
  simp only [restrictedOverCohomologyMap, restrictedOverSingleIso, asIso_hom]
  rfl

attribute [local irreducible] restrictedOverCohomologyMap restrictedOverSingleIso
  upperStar upperStarComp upperStarId rawAffineRestrictedMap

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true

private theorem restrictedSingle_plus
    {W S : Scheme.{u}} (k : W ⟶ S)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (A : Over W) (U : S.Etale) :
    CochainComplex.plus _ (restrictedOverSingle k F A U) := by
  refine ⟨0, (CochainComplex.isStrictlyGE_iff _ 0).2 ?_⟩
  intro n hn
  exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ n (ne_of_lt hn)

private theorem pairMap_identity_transport {X : Scheme.{u}} (a : X ⟶ X)
    (ha : a = 𝟙 X)
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (hK : CochainComplex.plus _ K)
    (φ : ((upperStar AddCommGrpCat.{u + 1} a).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K ⟶ K)
    (hφ : HEq φ ((NatIso.mapHomologicalComplex
      (upperStarId AddCommGrpCat.{u + 1} X) (ComplexShape.up ℤ)).hom.app K)) (q : ℤ) :
    pairMap a K K φ q = 𝟙 _ := by
  subst a
  rw [eq_of_heq hφ]
  exact (derivedEtaleCohomology_pullback_laws pairMap @pairMap_spec).1 X ⟨K, hK⟩ q

private theorem restrictedMap_id
    {W S : Scheme.{u}} (k : W ⟶ S)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)
    (A : Over W) (U : S.Etale) :
    restrictedOverCohomologyMap k F q (𝟙 A) U = 𝟙 _ := by
  rw [restrictedOverCohomologyMap_eq]
  apply pairMap_identity_transport
  · apply pullback.hom_ext <;> simp [rawAffineRestrictedMap]
  · exact restrictedSingle_plus k F A U
  · exact restricted_identity_heq k F A U

private theorem restrictedMap_comp
    {W S : Scheme.{u}} (k : W ⟶ S)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)
    {A B C : Over W} (f : B ⟶ A) (g : C ⟶ B) (U : S.Etale) :
    restrictedOverCohomologyMap k F q (g ≫ f) U =
      restrictedOverCohomologyMap k F q f U ≫ restrictedOverCohomologyMap k F q g U := by
  let rf := rawAffineRestrictedMap f.left (A.hom ≫ k) (B.hom ≫ k)
    (by rw [← Category.assoc, Over.w]) U
  let rg := rawAffineRestrictedMap g.left (B.hom ≫ k) (C.hom ≫ k)
    (by rw [← Category.assoc, Over.w]) U
  let ra := rawAffineRestrictedMap (g ≫ f).left (A.hom ≫ k) (C.hom ≫ k)
    (by rw [← Category.assoc, Over.w]) U
  have hq : ra = rg ≫ rf := by
    set_option backward.isDefEq.respectTransparency false in
    apply pullback.hom_ext <;> simp [ra, rg, rf, rawAffineRestrictedMap, Category.assoc]
  simp only [restrictedOverCohomologyMap_eq]
  rw [restrictedOverSingle_composition k F f g (g ≫ f) rfl U hq]
  exact pairMap_comp rf rg ra hq _ _ _
    (restrictedSingle_plus k F A U) (restrictedSingle_plus k F B U)
    (restrictedSingle_plus k F C U) _ _ q

private theorem restrictedMapLaws
    {W S : Scheme.{u}} (k : W ⟶ S)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)
    {I : Type u} [SmallCategory I] (D : I ⥤ Over W) (c : Cone D) (U : S.Etale) :
    (∀ i : I, restrictedOverCohomologyMap k F q (D.map (𝟙 i)) U = 𝟙 _) ∧
    (∀ (i j l : I) (f : j ⟶ i) (g : l ⟶ j),
      restrictedOverCohomologyMap k F q (D.map (g ≫ f)) U =
        restrictedOverCohomologyMap k F q (D.map f) U ≫
          restrictedOverCohomologyMap k F q (D.map g) U) ∧
    (∀ (i j : I) (f : j ⟶ i),
      restrictedOverCohomologyMap k F q (D.map f) U ≫
        restrictedOverCohomologyMap k F q (c.π.app j) U =
          restrictedOverCohomologyMap k F q (c.π.app i) U) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [D.map_id]
    exact restrictedMap_id k F q (D.obj i) U
  · intro i j l f g
    rw [D.map_comp]
    exact restrictedMap_comp k F q (D.map f) (D.map g) U
  · intro i j f
    rw [← restrictedMap_comp k F q (D.map f) (c.π.app j) U, c.w f]

private noncomputable def restrictedDiagram
    {W S : Scheme.{u}} (k : W ⟶ S)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)
    {I : Type u} [SmallCategory I] (D : I ⥤ Over W) (c : Cone D) (U : S.Etale) :
    Iᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj i := restrictedOverCohomology k F q (D.obj i.unop) U
  map f := restrictedOverCohomologyMap k F q (D.map f.unop) U
  map_id i := (restrictedMapLaws k F q D c U).1 i.unop
  map_comp f g := (restrictedMapLaws k F q D c U).2.1 _ _ _ f.unop g.unop

private noncomputable def restrictedCocone
    {W S : Scheme.{u}} (k : W ⟶ S)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)
    {I : Type u} [SmallCategory I] (D : I ⥤ Over W) (c : Cone D) (U : S.Etale) :
    Cocone (restrictedDiagram k F q D c U) where
  pt := restrictedOverCohomology k F q c.pt U
  ι :=
    { app := fun i ↦ restrictedOverCohomologyMap k F q (c.π.app i.unop) U
      naturality := fun i j f ↦ by
        change restrictedOverCohomologyMap k F q (D.map f.unop) U ≫
          restrictedOverCohomologyMap k F q (c.π.app j.unop) U =
            restrictedOverCohomologyMap k F q (c.π.app i.unop) U ≫ 𝟙 _
        rw [Category.comp_id]
        exact (restrictedMapLaws k F q D c U).2.2 _ _ f.unop }

/-- Fixed coefficients on an inverse scheme system have a canonical restricted
cohomology diagram and cocone, with a complex-continuity presentation.
Source: Stacks Project, Tags 09Z1 and 0EZM.
(blueprint: lem-sc-restricted-over-abelian-cohomology-presentation).

Proof: Form restrictedOverDiagram and restrictedOverCone. Restrict the fixed
coefficient sheaf and put it in degree zero, using restrictedOverSingle. Its
transition isomorphisms and constant limiting diagram obey the equations in
restrictedOverSingle_coherence. The canonical derived-unit maps on cohomology
therefore obey identity, composition and cone-leg equations by
derivedEtaleCohomology_pullback_laws, using the proved single-complex unit and
composition equations. Use them to construct H and B, with
objects restrictedOverCohomology and maps restrictedOverCohomologyMap. Their
comparison isomorphisms are identities. The theorem
restrictedOverAbelianCocone_complex_data supplies the required presentation;
its only additional hypotheses are the two map equations, which are reflexive.
This constructs the diagram without using cohomology continuity. The degree can
be negative; the single complexes remain uniformly bounded below by zero. -/
theorem exists_restrictedOverAbelian_cohomology_presentation
    {W S : Scheme.{u}} (k : W ⟶ S)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)
    {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Over W)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i, QuasiCompact ((D.obj i).hom ≫ k)]
    [∀ i, QuasiSeparated ((D.obj i).hom ≫ k)]
    (c : Cone D) (hc : IsLimit ((Over.forget W).mapCone c))
    [QuasiCompact (c.pt.hom ≫ k)] [QuasiSeparated (c.pt.hom ≫ k)]
    (U : S.Etale) [IsAffine U.left] :
    ∃ (H : Iᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (B : Cocone H)
      (e : ∀ i : I, H.obj (op i) ≅ restrictedOverCohomology k F q (D.obj i) U)
      (e₀ : B.pt ≅ restrictedOverCohomology k F q c.pt U),
      EtaleComplexCohomologyPresentationData H B ∧
      (∀ (i j : I) (f : j ⟶ i), H.map f.op ≫ (e j).hom =
        (e i).hom ≫ restrictedOverCohomologyMap k F q (D.map f) U) ∧
      (∀ i : I, B.ι.app (op i) ≫ e₀.hom =
        (e i).hom ≫ restrictedOverCohomologyMap k F q (c.π.app i) U) := by
  let H := restrictedDiagram k F q D c U
  let B := restrictedCocone k F q D c U
  refine ⟨H, B, fun _ ↦ Iso.refl _, Iso.refl _, ?_, ?_, ?_⟩
  · exact restrictedOverAbelianCocone_complex_data k F q D c hc U H B
      (fun _ ↦ Iso.refl _) (Iso.refl _)
      (by intros; exact (Category.comp_id _).trans (Category.id_comp _).symm)
      (by intros; exact (Category.comp_id _).trans (Category.id_comp _).symm)
  · intros
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  · intros
    exact (Category.comp_id _).trans (Category.id_comp _).symm

end AlgebraicGeometry.Etale
