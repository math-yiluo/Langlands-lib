/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleInjectiveSectionsComparison
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-! # Canonical cycle comparisons for source sections

Source: Stacks Project, Tags 03Q8 and 03Q9, injective-complex computation.
(blueprint: def-weil-pbc-strict-local-injective-source-comparison).
-/

/- This original-model counterpart follows the proved calculation in
WeilConjectures.AlgebraicGeometry.StrictLocalInjectiveSourceComparison.
The spectrum and structure morphism are those of the small coordinate-ring colimit. -/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry CochainComplex CochainComplex.HomComplex

namespace AlgebraicGeometry.Etale

section
variable {C : Type (v + 1)} [Category.{v} C]
  {T : GrothendieckTopology C} [HasSheafify T AddCommGrpCat.{v + 1}]

/-- The sections equivalence is the composite of sheafification, free abelian groups,
and Yoneda adjunctions.
Source: Stacks Project, Tag 03Q8 (free-sheaf sections adjunction).
(blueprint: def-weil-pbc-strict-local-injective-source-comparison). -/
noncomputable def smallModel_sourceFreeSectionsEquiv (W : C)
    (G : Sheaf T AddCommGrpCat.{v + 1}) :
    ((strictLocalFreeSheaf T).obj W ⟶ G) ≃+ G.obj.obj (op W) where
  toEquiv := ((sheafificationAdjunction _ _).homEquiv _ _).trans <|
    (((AddCommGrpCat.adj).whiskerRight Cᵒᵖ).homEquiv _ _).trans uliftYonedaEquiv
  map_add' a b := by
    change (strictLocalFreeSheafSections G).app (op W) (a + b) =
      (strictLocalFreeSheafSections G).app (op W) a +
        (strictLocalFreeSheafSections G).app (op W) b
    exact map_add _ a b

/-- The sections equivalence commutes with maps of sheaves.
Source: Stacks Project, Tag 03Q8 (naturality of free-generator evaluation).
(blueprint: def-weil-pbc-strict-local-injective-source-comparison). -/
theorem smallModel_sourceFreeSectionsEquiv_comp (W : C)
    {G H : Sheaf T AddCommGrpCat.{v + 1}}
    (a : (strictLocalFreeSheaf T).obj W ⟶ G) (b : G ⟶ H) :
    smallModel_sourceFreeSectionsEquiv W H (a ≫ b) =
      b.hom.app (op W) (smallModel_sourceFreeSectionsEquiv W G a) := by
  simp [smallModel_sourceFreeSectionsEquiv]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Degreewise evaluation identifies the Hom complex with the sections complex.
Source: Stacks Project, Tags 03Q8 and 03Q9, injective-complex computation.
(blueprint: def-weil-pbc-strict-local-injective-source-comparison). -/
noncomputable def smallModel_sourceFreeSectionsComplexIso (W : C)
    (L : CochainComplex (Sheaf T AddCommGrpCat.{v + 1}) ℤ) :
    HomComplex ((CochainComplex.singleFunctor _ 0).obj ((strictLocalFreeSheaf T).obj W)) L ≅
      (((sheafSections T AddCommGrpCat.{v + 1}).obj (op W)).mapHomologicalComplex
        (.up ℤ)).obj L :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ ((Cochain.fromSingleEquiv (zero_add n)).trans
      (smallModel_sourceFreeSectionsEquiv W (L.X n))).toAddCommGrpIso) (by
        intro i j hij
        ext a
        obtain ⟨a, rfl⟩ := Cochain.fromSingleMk_surjective a i (zero_add i)
        simpa [HomComplex, Cochain.δ_fromSingleMk,
          Cochain.fromSingleEquiv_fromSingleMk] using!
          (smallModel_sourceFreeSectionsEquiv_comp W a (L.d i j)).symm)

end

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The right-derived unit on a fixed injective representative identifies the
source with the localization of its underived direct image.
Source: Stacks Project, Tags 03Q8 and 03Q9, injective-complex computation.
(blueprint: def-weil-pbc-strict-local-injective-source-comparison). -/
noncomputable def smallModel_sourceInjectiveDirectImageIso {X S : Scheme.{v}} (f : X ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (J : CochainComplex.Plus (InjectiveObject
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})))
    (q : K.obj ≅ DerivedCategory.Q.obj
      (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj)) :
    ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K).obj ≅
      DerivedCategory.Q.obj
        (((lowerStar AddCommGrpCat.{v + 1} f).mapHomologicalComplex (.up ℤ)).obj
          (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj)) := by
  let M := (InjectiveObject.ι _).mapCochainComplexPlus.obj J
  let q' : K ≅ (HomotopyCategory.Plus.quotient _ ⋙ DerivedCategory.Plus.Qh).obj M :=
    DerivedCategory.Plus.ι.preimageIso
      (q ≪≫ (DerivedCategory.quotientCompQhIso _).symm.app M.obj)
  let F := lowerStar AddCommGrpCat.{v + 1} f
  let e := F.rightDerivedFunctorPlus.mapIso q' ≪≫
    (asIso (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient _).obj M))).symm
  exact DerivedCategory.Plus.ι.mapIso e ≪≫
    DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (.up ℤ)).app M.obj) ≪≫
    (DerivedCategory.quotientCompQhIso (Sheaf S.smallEtaleTopology
      AddCommGrpCat.{v + 1})).app ((F.mapHomologicalComplex (.up ℤ)).obj M.obj)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Localized Hom classes into a K-injective complex compute derived Hom.
Source: Stacks Project, Tags 03Q8 and 03Q9, injective-complex computation.
(blueprint: def-weil-pbc-strict-local-injective-source-comparison). -/
noncomputable def smallModel_sourceClassDerivedHomIso
    {C : Type (v + 2)} [Category.{v + 1} C] [Abelian C] [HasDerivedCategory.{v + 1} C]
    (A : C) (L : CochainComplex C ℤ) [L.IsKInjective] (n : ℤ) :
    AddCommGrpCat.of (CohomologyClass ((CochainComplex.singleFunctor _ 0).obj A) L n) ≅
      AddCommGrpCat.of ((DerivedCategory.singleFunctor C 0).obj A ⟶
        (DerivedCategory.Q.obj L)⟦n⟧) := by
  let E := CohomologyClass.homAddEquiv
    (K := (CochainComplex.singleFunctor _ 0).obj A) (L := L) (n := n)
  let E' := AddEquiv.ofBijective (DerivedCategory.Qh.mapAddHom
    (X := (HomotopyCategory.quotient _ _).obj
      ((CochainComplex.singleFunctor _ 0).obj A))
    (Y := (HomotopyCategory.quotient _ _).obj (L⟦n⟧)))
    (CochainComplex.IsKInjective.Qh_map_bijective _ (L⟦n⟧))
  let a := (DerivedCategory.quotientCompQhIso C).app
    ((CochainComplex.singleFunctor _ 0).obj A) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ C 0).app A).symm
  let b := (DerivedCategory.quotientCompQhIso C).app (L⟦n⟧) ≪≫
    (DerivedCategory.Q.commShiftIso n).app L
  let E'' := AddEquiv.mk' (a.homCongr b)
    (fun x y ↦ by simp [Iso.homCongr_apply, Preadditive.comp_add, Preadditive.add_comp])
  exact (E.trans (E'.trans E'')).toAddCommGrpIso

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Underived direct-image sections are sections on the base-changed stage.
Source: Stacks Project, Tags 03Q8 and 03Q9, injective-complex computation.
(blueprint: def-weil-pbc-strict-local-injective-source-comparison). -/
noncomputable def smallModel_sourceStageSectionsIso {X S : Scheme.{v}} (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
    lowerStar AddCommGrpCat.{v + 1} f ⋙
      (sheafSections S.smallEtaleTopology AddCommGrpCat.{v + 1}).obj
        (op ((strictLocalNeighbourhoods s).obj i)) ≅
    upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f s).app i) ⋙
      Sheaf.Γ ((strictLocalNeighbourhoodDiagram f s).obj i).smallEtaleTopology
        AddCommGrpCat.{v + 1} := by
  let W := (MorphismProperty.Over.pullback @Etale ⊤ f).obj
    ((strictLocalNeighbourhoods s).obj i)
  let t := (strictLocalNeighbourhoodProjection f s).app i
  change (sheafSections X.smallEtaleTopology AddCommGrpCat.{v + 1}).obj (op W) ≅
    upperStar AddCommGrpCat.{v + 1} t ⋙ Sheaf.Γ W.left.smallEtaleTopology
      AddCommGrpCat.{v + 1}
  have ht : Etale t := by dsimp [t, strictLocalNeighbourhoodProjection]; infer_instance
  let V : W.left.Etale := Scheme.Etale.mk (𝟙 W.left)
  let hV : IsTerminal V := IsTerminal.ofUniqueHom
    (fun Z ↦ MorphismProperty.Over.homMk Z.hom (by simp [V]))
    (fun Z b ↦ MorphismProperty.Over.Hom.ext (by simpa [V] using b.w))
  let U := (MorphismProperty.Over.map ⊤ ht).obj V
  let a : U ≅ W := MorphismProperty.Over.isoMk (Iso.refl W.left)
    (by simp [U, V, t, W, strictLocalNeighbourhoodProjection])
  let h : ((sheafSections X.smallEtaleTopology AddCommGrpCat.{v + 1}).obj (op W)) ≅
      localizationRestriction AddCommGrpCat.{v + 1} t ht ⋙
        (sheafSections W.left.smallEtaleTopology AddCommGrpCat.{v + 1}).obj
          (op V) :=
    NatIso.ofComponents (fun G ↦ G.obj.mapIso a.op) (fun b ↦ by
      change b.hom.app (op W) ≫ _ = _ ≫ b.hom.app (op U)
      exact (b.hom.naturality a.inv.op).symm)
  exact h ≪≫
    (Functor.isoWhiskerRight (upperStarIsoLocalizationRestriction
      AddCommGrpCat.{v + 1} t ht) _).symm ≪≫
    Functor.isoWhiskerLeft (upperStar AddCommGrpCat.{v + 1} t)
      (Sheaf.ΓNatIsoSheafSections _ _ hV).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Transport a bounded-below shifted Hom through a specified unbounded representative.
Source: Stacks Project, Tags 03Q8 and 03Q9, injective-complex computation.
(blueprint: def-weil-pbc-strict-local-injective-source-comparison). -/
noncomputable def smallModel_sourcePlusHomIso
    {C : Type (v + 2)} [Category.{v + 1} C] [Abelian C] [HasDerivedCategory.{v + 1} C]
    (A : C) (K : DerivedCategory.Plus C) (L : CochainComplex C ℤ)
    (q : K.obj ≅ DerivedCategory.Q.obj L) (n : ℤ) :
    AddCommGrpCat.of ((DerivedCategory.Plus.singleFunctor C 0).obj A ⟶ K⟦n⟧) ≅
      AddCommGrpCat.of ((DerivedCategory.singleFunctor C 0).obj A ⟶
        (DerivedCategory.Q.obj L)⟦n⟧) := by
  let E := AddEquiv.mk' ((Functor.FullyFaithful.ofFullyFaithful DerivedCategory.Plus.ι).homEquiv
    (X := (DerivedCategory.Plus.singleFunctor C 0).obj A) (Y := K⟦n⟧))
    (fun x y ↦ by exact Functor.map_add DerivedCategory.Plus.ι (f := x) (g := y))
  let b := (DerivedCategory.Plus.ι.commShiftIso n).app K ≪≫
    (CategoryTheory.shiftFunctor _ n).mapIso q
  let E' := AddEquiv.mk' ((Iso.refl ((DerivedCategory.singleFunctor C 0).obj A)).homCongr b)
    (fun x y ↦ by simp [Iso.homCongr_apply, Preadditive.comp_add, Preadditive.add_comp])
  exact (E.trans E').toAddCommGrpIso

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical source comparison: localize the Hom complex of the underived
injective direct image, evaluate its free generator, and identify its sections
with sections of the inverse image on the stage. No existence witness is chosen.
Source: Stacks Project, Tags 03Q8 and 03Q9.
(blueprint: def-weil-pbc-strict-local-injective-source-comparison). -/
noncomputable def smallModel_strictLocalInjectiveSourceIso {X S : Scheme.{v}}
    (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ)
    (J : CochainComplex.Plus (InjectiveObject
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})))
    (q : K.obj ≅ DerivedCategory.Q.obj
      (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj))
    (i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
    (strictLocalCohomologyNeighbourhoodFunctor s
      ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n).obj (op i) ≅
      termwiseSectionsCohomology ((strictLocalNeighbourhoodDiagram f s).obj i)
        (((upperStar AddCommGrpCat.{v + 1}
          ((strictLocalNeighbourhoodProjection f s).app i)).mapHomologicalComplex
            (.up ℤ)).obj
              (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj)) n := by
  let M := (InjectiveObject.ι _).mapCochainComplexPlus.obj J
  let F := lowerStar AddCommGrpCat.{v + 1} f
  let L := F.mapCochainComplexPlus.obj M
  have : F.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f)
  have (k : ℤ) : Injective (L.obj.X k) :=
    F.injective_obj ((InjectiveObject.ι _).obj (J.obj.X k))
  have : L.obj.IsKInjective := by
    obtain ⟨b, hb⟩ := L.property
    let : L.obj.IsStrictlyGE b := hb
    exact CochainComplex.isKInjective_of_injective L.obj b
  let W := (strictLocalNeighbourhoods s).obj i
  let A := (strictLocalFreeSheaf S.smallEtaleTopology).obj W
  let r := smallModel_sourceInjectiveDirectImageIso f K J q
  let E := smallModel_sourcePlusHomIso A _ L.obj r n ≪≫
    (smallModel_sourceClassDerivedHomIso A L.obj n).symm
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{v + 1} (.up ℤ) n
  let E' := (leftHomologyData ((CochainComplex.singleFunctor _ 0).obj A) L.obj n).homologyIso.symm
    ≪≫ H.mapIso (smallModel_sourceFreeSectionsComplexIso W L.obj)
  let E'' := H.mapIso ((NatIso.mapHomologicalComplex (smallModel_sourceStageSectionsIso f s i)
    (.up ℤ)).app M.obj)
  exact E ≪≫ E' ≪≫ E'' ≪≫
    (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v + 1} n).symm.app _

end AlgebraicGeometry.Etale
