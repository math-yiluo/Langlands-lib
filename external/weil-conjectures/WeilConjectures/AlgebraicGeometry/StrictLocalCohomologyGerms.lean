/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationRestriction
public import WeilConjectures.AlgebraicGeometry.StrictLocalGermRestrictionIso
public import WeilConjectures.AlgebraicGeometry.StrictLocalNeighbourhoodGeometry

/-! # Canonical derived sections and strict-local cohomology germs

Source: Stacks Project, Tags 03Q8 and 03Q9. The derived Hom comparison is the
explicit free-abelian-sheaf construction used in AbelianHigherDirectImagePresheaf.
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

section DerivedSections

variable {C : Type (v + 1)} [Category.{v} C]
  {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{v + 1}]

/-- The free sheaf `ℤ[W]` of abelian groups on an étale `X`-scheme `W`: the sheafification of the
presheaf `V ↦ ℤ^{(Hom_X(V, W))}`. It corepresents sections over `W`, and
`Ext^q(ℤ[W], F)` is the étale cohomology `H^q(W, F|_W)`.
(blueprint: def-weil-pbc-canonical-derived-cohomology-germs). -/
noncomputable def strictLocalFreeSheaf (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v + 1}] :
    C ⥤ Sheaf J (AddCommGrpCat.{v + 1}) :=
  uliftYoneda.{v + 1} ⋙ (Functor.whiskeringRight _ _ _).obj (AddCommGrpCat.free) ⋙
    presheafToSheaf _ _

/-- Evaluation at the generator: for a sheaf `G` of abelian groups on `X_ét`, the natural map
`Hom(ℤ[W], G) ⟶ G(W)` sending `f` to the image under `f` of the section of `ℤ[W]` given by
the identity of `W`.
(blueprint: def-weil-pbc-canonical-derived-cohomology-germs). -/
noncomputable def strictLocalFreeSheafSections
    (G : Sheaf J (AddCommGrpCat.{v + 1})) :
    (strictLocalFreeSheaf J).op ⋙ preadditiveYoneda.obj G ⟶
      G.obj where
  app W := AddCommGrpCat.ofHom
    { toFun f := (f.hom.app W).hom (((toSheafify J
        (uliftYoneda.{v + 1}.obj W.unop ⋙ AddCommGrpCat.free)).app W).hom
          (FreeAbelianGroup.of (ULift.up (𝟙 W.unop))))
      map_zero' := rfl
      map_add' _ _ := rfl }
  naturality W W' g := by
    ext f
    have h₁ := congr_arg (fun k ↦ (k.app W').hom (FreeAbelianGroup.of (ULift.up (𝟙 W'.unop))))
      (toSheafify_naturality J
        (Functor.whiskerRight (uliftYoneda.{v + 1}.map g.unop) (AddCommGrpCat.free)))
    have h₂ := congr_arg (fun k ↦ k.hom (FreeAbelianGroup.of (ULift.up (𝟙 W.unop))))
      ((toSheafify J
        (uliftYoneda.{v + 1}.obj W.unop ⋙ AddCommGrpCat.free)).naturality g)
    have h₃ := congr_arg (fun k ↦ k.hom (((toSheafify J
        (uliftYoneda.{v + 1}.obj W.unop ⋙ AddCommGrpCat.free)).app W).hom
          (FreeAbelianGroup.of (ULift.up (𝟙 W.unop))))) (f.hom.naturality g)
    have h₀ : ((AddCommGrpCat.free).map ((uliftYoneda.{v + 1}.map g.unop).app W')).hom
        (FreeAbelianGroup.of (ULift.up (𝟙 W'.unop))) =
        ((AddCommGrpCat.free).map ((uliftYoneda.{v + 1}.obj W.unop).map g)).hom
          (FreeAbelianGroup.of (ULift.up (𝟙 W.unop))) := by
      simp
    dsimp at h₁ h₂ h₃
    exact (congr_arg (f.hom.app W').hom h₁.symm).trans
      ((congr_arg (fun x ↦ (f.hom.app W').hom
        (((toSheafify J
          (uliftYoneda.{v + 1}.obj W.unop ⋙ AddCommGrpCat.free)).app W').hom x)) h₀).trans
        ((congr_arg (f.hom.app W').hom h₂).trans h₃))


variable [HasDerivedCategory.{v + 1} (Sheaf J AddCommGrpCat.{v + 1})]

/-- For `L ∈ D⁺(X_ét)`, the map `Hom(ℤ[W][0], L) ⟶ Hom(ℤ[W], H⁰(L))` induced by the degree-`0`
homology, natural in `W`.
(blueprint: def-weil-pbc-canonical-derived-cohomology-germs). -/
noncomputable def strictLocalDerivedHomToHomology
    (L : DerivedCategory.Plus (Sheaf J (AddCommGrpCat.{v + 1}))) :
    (strictLocalFreeSheaf J ⋙ DerivedCategory.Plus.singleFunctor _ 0).op ⋙
        preadditiveYoneda.obj L ⟶
      (strictLocalFreeSheaf J).op ⋙ preadditiveYoneda.obj
        ((DerivedCategory.Plus.homologyFunctor _ 0).obj L) where
  app W := AddCommGrpCat.ofHom <|
    (Preadditive.leftComp _
      ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _)).comp
      (DerivedCategory.Plus.homologyFunctor _ 0).mapAddHom
  naturality W W' g := by
    have hs := (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso
      (C := Sheaf J (AddCommGrpCat.{v + 1})) 0).inv.naturality
        ((strictLocalFreeSheaf J).map g.unop)
    dsimp at hs
    ext f
    revert f
    change ∀ f :
      (DerivedCategory.Plus.singleFunctor _ 0).obj ((strictLocalFreeSheaf J).obj W.unop) ⟶
        L,
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _ ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map ((strictLocalFreeSheaf J).map g.unop) ≫ f) =
      (strictLocalFreeSheaf J).map g.unop ≫
        (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app
          ((strictLocalFreeSheaf J).obj W.unop) ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).map f
    intro f
    rw [Functor.map_comp, ← reassoc_of% hs]

end DerivedSections

/-- The degree-n derived-sections presheaf of a bounded below derived sheaf.
Source: Stacks, Tag 03Q8
(blueprint: def-weil-pbc-canonical-derived-cohomology-germs). -/
noncomputable def strictLocalCohomologyPresheaf {S : Scheme.{v}}
    (L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{v + 1} :=
  (strictLocalFreeSheaf S.smallEtaleTopology ⋙
    DerivedCategory.Plus.singleFunctor _ 0).op ⋙ preadditiveYoneda.obj (L⟦n⟧)

/-- The canonical map from derived sections to sections of the cohomology sheaf.
It takes a derived morphism to its degree-zero homology, evaluates the free generator,
and uses the homology shift isomorphism. No sheafification isomorphism is chosen.
Source: Stacks, Tag 03Q8
(blueprint: def-weil-pbc-canonical-derived-cohomology-germs). -/
noncomputable def strictLocalCohomologyGermMap {S : Scheme.{v}}
    (L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) : strictLocalCohomologyPresheaf L n ⟶
      ((DerivedCategory.Plus.homologyFunctor _ n).obj L).obj :=
  strictLocalDerivedHomToHomology (L⟦n⟧) ≫
    strictLocalFreeSheafSections _ ≫
    (((DerivedCategory.Plus.homologyFunctor _ 0).shiftIso n 0 n (add_zero n)).hom.app L).hom

/-- The stalk-to-source isomorphism for the strict-local mate, using the unique germ
restriction and commutation of exact inverse image with homology.
Source: Stacks, Tags 03Q9 and 03QO
(blueprint: def-weil-pbc-canonical-derived-cohomology-germs). -/
noncomputable def strictLocalCohomologySourceIso {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) :
    (Scheme.pointSmallEtale s).sheafFiber.obj
        ((DerivedCategory.Plus.homologyFunctor _ n).obj L) ≅
      (Sheaf.Γ (Scheme.strictLocalization s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).obj
        ((DerivedCategory.Plus.homologyFunctor _ n).obj
          ((upperStar AddCommGrpCat.{v + 1}
            (Scheme.strictLocalizationToBase s)).mapDerivedCategoryPlus.obj L)) := by
  classical
  let G := (DerivedCategory.Plus.homologyFunctor _ n).obj L
  let r := Classical.choose (existsUnique_strictHenselizationStalkRestriction s G)
  have hr := (Classical.choose_spec (existsUnique_strictHenselizationStalkRestriction s G)).1
  letI := isIso_strictHenselizationStalkRestriction s G r hr
  exact asIso r ≪≫
    (Sheaf.Γ (Scheme.strictLocalization s).smallEtaleTopology
      AddCommGrpCat.{v + 1}).mapIso
      ((Functor.mapDerivedCategoryPlusHomologyFunctorIso
        (upperStar AddCommGrpCat.{v + 1}
          (Scheme.strictLocalizationToBase s)) n).app L)

/-- Restrict the derived-sections presheaf to the small pointed affine representatives.
Source: Stacks, Tag 03Q9, first proof paragraph
(blueprint: def-weil-pbc-canonical-derived-cohomology-germs). -/
noncomputable def strictLocalCohomologyNeighbourhoodFunctor {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) :
    (SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s))ᵒᵖ ⥤
      AddCommGrpCat.{v + 1} :=
  (strictLocalNeighbourhoods s).op ⋙ strictLocalCohomologyPresheaf L n

/-- Canonical source legs: a presheaf germ, the canonical map to the cohomology-sheaf
stalk, and the unique strict-local germ restriction transported through exact inverse image.
Source: Stacks, Tags 03Q8 and 03Q9
(blueprint: def-weil-pbc-canonical-derived-cohomology-germs). -/
noncomputable def strictLocalCohomologySourceLegs {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) :
    strictLocalCohomologyNeighbourhoodFunctor s L n ⟶
      (Functor.const _).obj
        ((Sheaf.Γ (Scheme.strictLocalization s).smallEtaleTopology
          AddCommGrpCat.{v + 1}).obj
          ((DerivedCategory.Plus.homologyFunctor _ n).obj
            ((upperStar AddCommGrpCat.{v + 1}
              (Scheme.strictLocalizationToBase s)).mapDerivedCategoryPlus.obj L))) where
  app i :=
    (Scheme.pointSmallEtale s).toPresheafFiber
      ((strictLocalNeighbourhoods s).obj i.unop)
      ((equivSmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj
        i.unop).2 (strictLocalCohomologyPresheaf L n) ≫
      (Scheme.pointSmallEtale s).presheafFiber.map (strictLocalCohomologyGermMap L n) ≫
        (strictLocalCohomologySourceIso s L n).hom
  naturality i j a := by
    dsimp [strictLocalCohomologyNeighbourhoodFunctor]
    simp only [Category.comp_id, ← Category.assoc]
    congr 1
    congr 1
    let N := (equivSmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)).inverse ⋙
      Scheme.strictHenselizationAffineInclusion s ⋙ ObjectProperty.ι
        (fun q : (Scheme.pointSmallEtale s).fiber.Elements ↦ IsAffine q.1.left)
    exact (Scheme.pointSmallEtale s).presheafFiberCocone
      (strictLocalCohomologyPresheaf L n) |>.w (N.map a.unop).op

end AlgebraicGeometry.Etale
