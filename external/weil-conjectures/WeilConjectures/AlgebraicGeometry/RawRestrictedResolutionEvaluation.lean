/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawRestrictedHomotopySectionsIso
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.AlgebraicGeometry.RawRestrictedSectionsUnitZero

/-! # Compatibility of derived evaluation with a resolution

Source: Stacks Project, Cohomology on Sites, Tags 072W, 0BKV and 0D6F.
(blueprint: lem-sbc-raw-restricted-resolution-evaluation).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale.RawRestrictedComparison

/-- The canonical computation of restricted derived sections on a K-injective restriction.
Source: Stacks Project, Tags 072W and 0BKV.
(blueprint: lem-sbc-raw-restricted-resolution-evaluation). -/
noncomputable def resolutionSectionsIso {Y : Scheme.{v}} (W : Y.Etale)
    (I : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}))
    [CochainComplex.IsKInjective
      (((upperStar AddCommGrpCat.{v + 1} W.hom).mapHomologicalComplex (.up ℤ)).obj
      I.obj)] :
    (sectionsFunctor W ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0).obj
        (DerivedCategory.Plus.Q.obj I) ≅
      (((underivedSections W).mapHomologicalComplex (.up ℤ)).obj I.obj).homology 0 :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0).mapIso
      ((Sheaf.Γ W.left.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctor.mapIso
          ((upperStar AddCommGrpCat.{v + 1} W.hom).mapDerivedCategoryFactors.app I.obj) ≪≫
        (Sheaf.Γ W.left.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctorObjQIso
          (((upperStar AddCommGrpCat.{v + 1} W.hom).mapHomologicalComplex (.up ℤ)).obj
            I.obj)) ≪≫
    (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v + 1} 0).app _

set_option backward.isDefEq.respectTransparency false in
private theorem unit_naturality
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (R : D ⥤ E) [R.Additive]
    {K J : CochainComplex C ℤ} (f : K ⟶ J) :
    let η := fun (K : CochainComplex C ℤ) ↦
      (DerivedCategory.quotientCompQhIso E).inv.app
          ((R.mapHomologicalComplex (.up ℤ)).obj ((L.mapHomologicalComplex (.up ℤ)).obj K)) ≫
        R.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj
          ((L.mapHomologicalComplex (.up ℤ)).obj K)) ≫
        R.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso D).hom.app
          ((L.mapHomologicalComplex (.up ℤ)).obj K)) ≫
        R.rightDerivedFunctor.map (L.mapDerivedCategoryFactors.inv.app K)
    DerivedCategory.Q.map
        ((R.mapHomologicalComplex (.up ℤ)).map ((L.mapHomologicalComplex (.up ℤ)).map f)) ≫
        η J =
      η K ≫ R.rightDerivedFunctor.map (L.mapDerivedCategory.map (DerivedCategory.Q.map f)) := by
  let g := (L.mapHomologicalComplex (.up ℤ)).map f
  have hn := R.rightDerivedFunctorUnit.naturality
    ((HomotopyCategory.quotient _ (.up ℤ)).map g)
  have hl := L.mapDerivedCategoryFactors.inv.naturality f
  dsimp only [Functor.comp_map] at hl hn
  dsimp only
  simp only [Category.assoc]
  erw [DerivedCategory.quotientCompQhIso_inv_naturality_assoc]
  erw [reassoc_of% hn]
  simp only [← Functor.map_comp_assoc]
  erw [(DerivedCategory.quotientCompQhIso D).hom.naturality g]
  congr 1
  congr 1
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  rw [Category.assoc, hl, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem sectionsUnit_naturality {Y : Scheme.{v}} (W : Y.Etale)
    {K J : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ}
    (f : K ⟶ J) :
    DerivedCategory.Q.map (((underivedSections W).mapHomologicalComplex (.up ℤ)).map f) ≫
        sectionsUnit W J =
      sectionsUnit W K ≫
        (Sheaf.Γ W.left.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctor.map
          ((upperStar AddCommGrpCat.{v + 1} W.hom).mapDerivedCategory.map
            (DerivedCategory.Q.map f)) := by
  exact unit_naturality (upperStar AddCommGrpCat.{v + 1} W.hom)
    (Sheaf.Γ W.left.smallEtaleTopology AddCommGrpCat.{v + 1}) f

set_option backward.isDefEq.respectTransparency false in
private theorem sectionsUnit_resolution {Y : Scheme.{v}} (W : Y.Etale)
    (I : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}))
    [CochainComplex.IsKInjective
      (((upperStar AddCommGrpCat.{v + 1} W.hom).mapHomologicalComplex (.up ℤ)).obj
        I.obj)] :
    (sectionsUnit W I.obj) ≫
      (Sheaf.Γ W.left.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctor.map
        ((upperStar AddCommGrpCat.{v + 1} W.hom).mapDerivedCategoryFactors.hom.app I.obj) ≫
      ((Sheaf.Γ W.left.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctorObjQIso
        (((upperStar AddCommGrpCat.{v + 1} W.hom).mapHomologicalComplex (.up ℤ)).obj
          I.obj)).hom = 𝟙 _ := by
  dsimp only [sectionsUnit, Functor.rightDerivedFunctorObjQIso, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, asIso_inv]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc]
  erw [Iso.hom_inv_id_app]
  simp
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- On a chain map, derived evaluation agrees with termwise evaluation in the resolution.
Source: Stacks Project, Cohomology on Sites, Tags 072W, 0BKV and 0D6F.
(blueprint: lem-sbc-raw-restricted-resolution-evaluation).

Proof: let L be etale restriction and R be sections. The comparison defining
`resolutionSectionsIso` first uses the exact-functor localization comparison for L,
then the inverse right-derived unit for R on the K-injective complex L(I), and finally
homology's localization comparison. Naturality of all three comparisons identifies
its composite with the image under H^0(R L) of the given chain map. For the degree-zero
single source, the degree-zero derived-to-underived isomorphism `zeroIso` is the same
comparison followed by the single-complex homology identification. Thus the element
`zeroIso.inv (generator h U)` maps to the generator's single-complex class. Applying
the chain map gives exactly `chainEvaluation`. This equality is independent of any
chosen homotopy class isomorphism and does not assert its bijectivity. It also holds
for a zero chain map and for a zero or empty restricted complex. -/
theorem rawRestricted_resolution_evaluation {S Y : Scheme.{v}}
    (h : Y ⟶ S) (U : S.Etale)
    (I : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}))
    [CochainComplex.IsKInjective
      (((upperStar AddCommGrpCat.{v + 1}
      ((MorphismProperty.Over.pullback @Etale ⊤ h).obj U).hom).mapHomologicalComplex
         (.up ℤ)).obj I.obj)]
    (f : (CochainComplex.singleFunctor _ 0).obj
      ((upperStar AddCommGrpCat.{v + 1} h).obj (freeSheaf S U)) ⟶ I.obj) :
    let W := (MorphismProperty.Over.pullback @Etale ⊤ h).obj U
    let A := (upperStar AddCommGrpCat.{v + 1} h).obj (freeSheaf S U)
    let T := sectionsFunctor W ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0
    let x := (zeroIso W A).inv (generator h U)
    (resolutionSectionsIso W I).hom
        (T.map (DerivedCategory.Plus.ι.preimage
          (DerivedCategory.Q.map f) :
            (DerivedCategory.Plus.singleFunctor _ 0).obj A ⟶
              DerivedCategory.Plus.Q.obj I) x) =
      chainEvaluation h U I.obj f := by
  let W := (MorphismProperty.Over.pullback @Etale ⊤ h).obj U
  let A := (upperStar AddCommGrpCat.{v + 1} h).obj (freeSheaf S U)
  let H := DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0
  let F := (underivedSections W).mapHomologicalComplex (.up ℤ)
  let β := DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v + 1} 0
  let c := (Sheaf.Γ W.left.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctor.map
      ((upperStar AddCommGrpCat.{v + 1} W.hom).mapDerivedCategoryFactors.hom.app I.obj) ≫
    ((Sheaf.Γ W.left.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctorObjQIso
      (((upperStar AddCommGrpCat.{v + 1} W.hom).mapHomologicalComplex (.up ℤ)).obj
        I.obj)).hom
  have hn := sectionsUnit_naturality W f
  have hr := sectionsUnit_resolution W I
  change sectionsUnit W I.obj ≫ c = 𝟙 _ at hr
  have hc := congrArg (fun k ↦ k ≫ c) hn
  simp only [Category.assoc, hr, Category.comp_id] at hc
  have he := congrArg H.map hc
  simp only [Functor.map_comp] at he
  have hz := sectionsUnit_zero W A
  have hb := β.hom.naturality (F.map f)
  dsimp only [Functor.comp_map] at hb
  have hm :
      (zeroIso W A).inv ≫
        H.map ((Sheaf.Γ W.left.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctor.map
          ((upperStar AddCommGrpCat.{v + 1} W.hom).mapDerivedCategory.map
            (DerivedCategory.Q.map f))) ≫ H.map c ≫ (β.app (F.obj I.obj)).hom =
      (underivedSingleIso W A).inv ≫ HomologicalComplex.homologyMap (F.map f) 0 := by
    rw [← hz]
    simp only [Category.assoc]
    rw [← reassoc_of% he]
    erw [hb]
    change (underivedSingleIso W A).inv ≫
      (β.app (F.obj ((CochainComplex.singleFunctor _ 0).obj A))).inv ≫
        (β.app (F.obj ((CochainComplex.singleFunctor _ 0).obj A))).hom ≫
          HomologicalComplex.homologyMap (F.map f) 0 = _
    simp only [Iso.inv_hom_id_assoc]
  have hv := congrArg (fun k ↦ k (generator h U)) hm
  simpa only [resolutionSectionsIso, Iso.trans_hom, Functor.mapIso_hom,
    Functor.map_comp, Functor.comp_map, Functor.map_preimage, H, c, β, F, A, W,
    chainEvaluation, AddCommGrpCat.coe_comp, Function.comp_apply, Iso.app_hom] using! hv


end AlgebraicGeometry.Etale.RawRestrictedComparison
