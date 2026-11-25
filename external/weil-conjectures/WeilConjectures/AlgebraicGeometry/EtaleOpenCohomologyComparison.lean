/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleOpenObjectCohomologyMap
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective

/-! # Étale cohomology over an open object

Source: Stacks Project, Cohomology on Sites, Lemma 03F3 and Sites, Section 00XZ
(blueprint: def-weil-pbc-etale-open-comparison-data).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

namespace EtaleOpenComparison

/-- Canonical sections construction for the open-cohomology comparison.
Source: Stacks 03F3 and the free-abelian Yoneda adjunction.
(blueprint: def-weil-pbc-etale-open-comparison-data). -/
noncomputable def freeSectionsEquiv
    {C : Type (u + 1)} [Category.{u} C] (W : C)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (uliftYoneda.{u + 1}.obj W ⋙ AddCommGrpCat.free ⟶ F) ≃+ F.obj (Opposite.op W) where
  toEquiv := ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _).trans uliftYonedaEquiv
  map_add' a b := by
    change ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _ (a + b)).app
      (Opposite.op W) (ULift.up (𝟙 W)) = _
    simp only [Adjunction.homEquiv_apply, NatTrans.comp_app,
      Adjunction.whiskerRight_unit_app_app]
    rfl

/-- Canonical sections construction for the open-cohomology comparison.
Source: Stacks 03F3 and the free-abelian Yoneda adjunction.
(blueprint: def-weil-pbc-etale-open-comparison-data). -/
noncomputable def sectionsEquiv
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u + 1}] (W : C)
    (F : Sheaf J AddCommGrpCat.{u + 1}) :
    ((presheafToSheaf J AddCommGrpCat.{u + 1}).obj
      (uliftYoneda.{u + 1}.obj W ⋙ AddCommGrpCat.free) ⟶ F) ≃+ F.obj.obj (Opposite.op W) :=
  ((sheafificationAdjunction J AddCommGrpCat.{u + 1}).homAddEquiv _ F).trans
    (freeSectionsEquiv W F.obj)

/-- Canonical sections construction for the open-cohomology comparison.
Source: Stacks 03F3 and the free-abelian Yoneda adjunction.
(blueprint: def-weil-pbc-etale-open-comparison-data). -/
lemma sectionsEquiv_naturality
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u + 1}] (W : C)
    {F G : Sheaf J AddCommGrpCat.{u + 1}} (f : F ⟶ G)
    (a : (presheafToSheaf J AddCommGrpCat.{u + 1}).obj
      (uliftYoneda.{u + 1}.obj W ⋙ AddCommGrpCat.free) ⟶ F) :
    sectionsEquiv J W G (a ≫ f) =
      f.hom.app (Opposite.op W) (sectionsEquiv J W F a) := by
  dsimp only [sectionsEquiv, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply]
  rw [Adjunction.homEquiv_naturality_right]
  dsimp [freeSectionsEquiv]
  rfl

/-- Canonical sections construction for the open-cohomology comparison.
Source: Stacks 03F3 and the free-abelian Yoneda adjunction.
(blueprint: def-weil-pbc-etale-open-comparison-data). -/
noncomputable abbrev integerSheaf (U : Scheme.{u}) :=
  (constantSheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- Canonical sections construction for the open-cohomology comparison.
Source: Stacks 03F3 and the free-abelian Yoneda adjunction.
(blueprint: def-weil-pbc-etale-open-comparison-data). -/
noncomputable def restrictedSectionsEquiv
    {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (integerSheaf U ⟶
      (Etale.openImmersionRestriction (A := AddCommGrpCat.{u + 1}) j).obj G) ≃+
      G.obj.obj (Opposite.op (Scheme.Etale.mk j)) := by
  let e := ((constantSheafAdj U.smallEtaleTopology AddCommGrpCat.{u + 1}
    (MorphismProperty.Over.mkIdTerminal @Etale U)).homAddEquiv _
      ((Etale.openImmersionRestriction (A := AddCommGrpCat.{u + 1}) j).obj G)).trans
        (AddCommGrpCat.uliftZMultiplesAddEquiv _)
  let i : Scheme.Etale.mk (𝟙 U ≫ j) ≅ Scheme.Etale.mk j :=
    MorphismProperty.Over.isoMk (Iso.refl U) (Category.id_comp j)
  exact e.trans (G.obj.mapIso i.op.symm).addCommGroupIsoToAddEquiv

/-- Canonical sections construction for the open-cohomology comparison.
Source: Stacks 03F3 and the free-abelian Yoneda adjunction.
(blueprint: def-weil-pbc-etale-open-comparison-data). -/
lemma restrictedSectionsEquiv_naturality
    {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {G G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (f : G ⟶ G')
    (a : integerSheaf U ⟶
      (Etale.openImmersionRestriction (A := AddCommGrpCat.{u + 1}) j).obj G) :
    restrictedSectionsEquiv j G'
      (a ≫ (Etale.openImmersionRestriction (A := AddCommGrpCat.{u + 1}) j).map f) =
      f.hom.app (Opposite.op (Scheme.Etale.mk j)) (restrictedSectionsEquiv j G a) := by
  dsimp only [restrictedSectionsEquiv, AddEquiv.trans_apply,
    Adjunction.homAddEquiv_apply]
  rw [Adjunction.homEquiv_naturality_right]
  change G'.obj.map _ (f.hom.app _ _) = f.hom.app _ (G.obj.map _ _)
  exact (NatTrans.naturality_apply f.hom _ _).symm

/-- Canonical sections construction for the open-cohomology comparison.
Source: Stacks 03F3 and the free-abelian Yoneda adjunction.
(blueprint: def-weil-pbc-etale-open-comparison-data). -/
noncomputable def representingHomEquiv
    {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ((Etale.openImmersionLowerShriek (A := AddCommGrpCat.{u + 1}) j).obj
      (integerSheaf U) ⟶ G) ≃
    ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (uliftYoneda.{u + 1}.obj (Scheme.Etale.mk j) ⋙ AddCommGrpCat.free) ⟶ G) :=
  ((Etale.openImmersionLowerShriekAdjunction AddCommGrpCat.{u + 1} j).homEquiv _ G).trans
    ((restrictedSectionsEquiv j G).toEquiv.trans
      (sectionsEquiv X.smallEtaleTopology (Scheme.Etale.mk j) G).toEquiv.symm)

/-- Canonical sections construction for the open-cohomology comparison.
Source: Stacks 03F3 and the free-abelian Yoneda adjunction.
(blueprint: def-weil-pbc-etale-open-comparison-data). -/
lemma representingHomEquiv_naturality
    {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {G G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (f : G ⟶ G')
    (a : (Etale.openImmersionLowerShriek (A := AddCommGrpCat.{u + 1}) j).obj
      (integerSheaf U) ⟶ G) :
    representingHomEquiv j G' (a ≫ f) = representingHomEquiv j G a ≫ f := by
  apply (sectionsEquiv X.smallEtaleTopology (Scheme.Etale.mk j) G').injective
  simp only [representingHomEquiv, Equiv.trans_apply, AddEquiv.toEquiv_eq_coe,
    AddEquiv.coe_toEquiv]
  rw [Adjunction.homEquiv_naturality_right, restrictedSectionsEquiv_naturality,
    sectionsEquiv_naturality]
  change (sectionsEquiv X.smallEtaleTopology (Scheme.Etale.mk j) G')
    ((sectionsEquiv X.smallEtaleTopology (Scheme.Etale.mk j) G').symm _) =
    f.hom.app _ ((sectionsEquiv X.smallEtaleTopology (Scheme.Etale.mk j) G)
      ((sectionsEquiv X.smallEtaleTopology (Scheme.Etale.mk j) G).symm _))
  simp only [AddEquiv.apply_symm_apply]

/-- Canonical sections construction for the open-cohomology comparison.
Source: Stacks 03F3 and the free-abelian Yoneda adjunction.
(blueprint: def-weil-pbc-etale-open-comparison-data). -/
noncomputable def representingIso
    {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (uliftYoneda.{u + 1}.obj (Scheme.Etale.mk j) ⋙ AddCommGrpCat.free) ≅
    (Etale.openImmersionLowerShriek (A := AddCommGrpCat.{u + 1}) j).obj
      (integerSheaf U) :=
  Coyoneda.ext _ _ (fun a ↦ (representingHomEquiv j _).symm a)
    (fun a ↦ representingHomEquiv j _ a)
    (fun a ↦ Equiv.apply_symm_apply _ a)
    (fun a ↦ Equiv.symm_apply_apply _ a)
    (fun a f ↦ representingHomEquiv_naturality j f a)

end EtaleOpenComparison

/-- Cohomology over an open étale object agrees with cohomology on the open scheme.
The left side is the large-universe Ext model of object cohomology: free abelian
sheafification of the universe-lifted representable of `j`. This is the analogue of
`Sheaf.H'` for coefficients in `AddCommGrpCat.{u + 1}`; unlike global `Sheaf.H G q`,
it evaluates sections at `j`. Mathlib's `H'` requires coefficients in the Hom universe
of the site, which here is `u`, so it cannot be applied to this larger coefficient sheaf.
Source: Stacks Project, Cohomology on Sites, Lemma 03F3 and Sites, Section 00XZ
(blueprint: def-weil-pbc-etale-open-comparison-data).

Proof: Extension by zero and restriction are exact adjoints. The image of the constant
integer sheaf under extension by zero represents sections at the object `j`: use the
adjunction, the constant-sheaf adjunction on U, and the free-abelian Yoneda adjunction on X.
Yoneda therefore identifies this image with the free abelian sheaf on the representable
of `j`. The Ext adjunction and precomposition with this representing isomorphism give the
comparison in every degree. -/
noncomputable def etaleCohomologyOverOpenEquiv {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [Etale j]
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Abelian.Ext
      ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (uliftYoneda.{u + 1}.obj (Scheme.Etale.mk j) ⋙ AddCommGrpCat.free)) G q ≃+
      Sheaf.H ((Etale.openImmersionRestriction (A := AddCommGrpCat.{u + 1}) j).obj G) q := by
  have : (Etale.openImmersionRestriction AddCommGrpCat.{u + 1} j).IsLeftAdjoint :=
    (Etale.localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} j
      inferInstance).isLeftAdjoint
  let adj := Etale.openImmersionLowerShriekAdjunction AddCommGrpCat.{u + 1} j
  let e := adj.extAddEquiv (EtaleOpenComparison.integerSheaf U) G q
  exact (Abelian.Ext.precompAddEquiv (EtaleOpenComparison.representingIso j) G q).symm.trans e.symm


/-- The canonical comparison commutes with a morphism of coefficient sheaves.
Source: Stacks 03F3; naturality of the exact Ext adjunction and Ext composition.
(blueprint: def-weil-pbc-etale-open-comparison-data).
Proof: apply the inverse comparison. Naturality of the Ext adjunction moves the
coefficient map across the adjunction, and associativity of Yoneda composition moves
it across precomposition with the representing isomorphism. -/
theorem etaleCohomologyOverOpenEquiv_naturality {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [Etale j]
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})]
    {G G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (f : G ⟶ G') (q : ℕ)
    (x : Abelian.Ext
      ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (uliftYoneda.{u + 1}.obj (Scheme.Etale.mk j) ⋙ AddCommGrpCat.free)) G q) :
    etaleCohomologyOverOpenEquiv j G' q (x.comp (Abelian.Ext.mk₀ f) (add_zero q)) =
      Sheaf.H.map ((Etale.openImmersionRestriction AddCommGrpCat.{u + 1} j).map f) q
        (etaleCohomologyOverOpenEquiv j G q x) := by
  let adj := Etale.openImmersionLowerShriekAdjunction AddCommGrpCat.{u + 1} j
  let y := etaleCohomologyOverOpenEquiv j G q x
  have hx : (etaleCohomologyOverOpenEquiv j G q).symm y = x :=
    AddEquiv.symm_apply_apply _ x
  apply (etaleCohomologyOverOpenEquiv j G' q).symm.injective
  rw [AddEquiv.symm_apply_apply]
  change x.comp (Abelian.Ext.mk₀ f) (add_zero q) =
    (Abelian.Ext.mk₀ (EtaleOpenComparison.representingIso j).hom).comp
      (adj.mapExtCounit (EtaleOpenComparison.integerSheaf U) G' q
        (y.comp (Abelian.Ext.mk₀
          ((Etale.openImmersionRestriction AddCommGrpCat.{u + 1} j).map f))
            (add_zero q))) (zero_add q)
  rw [adj.mapExtCounit_comp_mk₀]
  rw [← Abelian.Ext.comp_assoc]
  · exact congrArg (fun z ↦ z.comp (Abelian.Ext.mk₀ f) (add_zero q)) hx.symm
  all_goals omega

/-- The free abelian sheaf functor representing sections on the small etale site.
Source: Stacks 03F3 (blueprint: def-weil-pbc-etale-open-comparison-data). -/
noncomputable abbrev EtaleOpenComparison.freeSheaf (X : Scheme.{u}) :
    X.Etale ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  etaleOpenFreeSheaf X

/-- Restriction in global cohomology, transported from inverse image to site restriction.
The three coefficient maps identify k^*j^*G with (k composed with j)^*G, using the
inverse-image composition isomorphism and the canonical restriction comparisons.
Source: Stacks 03F3 (blueprint: def-weil-pbc-etale-open-comparison-data). -/
noncomputable def etaleCohomologyOverOpenRestriction {X U V : Scheme.{u}}
    (j : U ⟶ X) (k : V ⟶ U) [IsOpenImmersion j] [IsOpenImmersion k]
    [HasExt.{u + 1} (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Sheaf.H ((Etale.openImmersionRestriction AddCommGrpCat.{u + 1} j).obj G) q →+
      Sheaf.H ((Etale.openImmersionRestriction AddCommGrpCat.{u + 1} (k ≫ j)).obj G) q :=
  (Sheaf.H.map
    (((Etale.upperStar AddCommGrpCat.{u + 1} k).map
      ((Etale.upperStarIsoOpenImmersionRestriction AddCommGrpCat.{u + 1} j).inv.app G)) ≫
      (Etale.upperStarComp AddCommGrpCat.{u + 1} k j).inv.app G ≫
      (Etale.upperStarIsoOpenImmersionRestriction AddCommGrpCat.{u + 1} (k ≫ j)).hom.app G)
    q).comp (Etale.cohomologyMap k
      ((Etale.openImmersionRestriction AddCommGrpCat.{u + 1} j).obj G) q)

end AlgebraicGeometry
