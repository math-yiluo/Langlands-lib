/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionCanonicalComparison
import WeilConjectures.AlgebraicGeometry.ConstantSectionAdjunctPullback

/-!
# Whole-to-open restriction of normalized resolution comparisons

Source: Stacks Project, Tags 0A50 and 03F3 (2), expanded on Hom cocycles.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Etale

private noncomputable abbrev globalSectionsEquiv {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
    (MorphismProperty.Over.mkIdTerminal @Etale X)).homAddEquiv
      (AddCommGrpCat.of (ULift ℤ)) F).trans (AddCommGrpCat.uliftZMultiplesAddEquiv _)

private lemma globalSectionsEquiv_comp {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (a : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift ℤ)) ⟶ F) (f : F ⟶ G) :
    globalSectionsEquiv G (a ≫ f) =
      f.hom.app (op (Scheme.Etale.mk (𝟙 X))) (globalSectionsEquiv F a) := by
  dsimp only [globalSectionsEquiv, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply]
  rw [Adjunction.homEquiv_naturality_right]
  rfl

private noncomputable def openToInteger {X : Scheme.{u}} (W : X.Opens) :
    (etaleOpenFreeSheaf X).obj (Scheme.Etale.mk W.ι) ⟶
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)) :=
  (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology (Scheme.Etale.mk W.ι) _).symm
    (((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift ℤ))).obj.map
        (MorphismProperty.Over.homMk W.ι (Category.comp_id _) :
          Scheme.Etale.mk W.ι ⟶ Scheme.Etale.mk (𝟙 X)).op
          (globalSectionsEquiv _ (𝟙 _)))

private lemma openToInteger_comp {X : Scheme.{u}} (W : X.Opens)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (f : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift ℤ)) ⟶ F) :
    EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology (Scheme.Etale.mk W.ι) F
      (openToInteger W ≫ f) =
      F.obj.map (MorphismProperty.Over.homMk W.ι (Category.comp_id _) :
        Scheme.Etale.mk W.ι ⟶ Scheme.Etale.mk (𝟙 X)).op (globalSectionsEquiv F f) := by
  rw [EtaleOpenComparison.sectionsEquiv_naturality]
  simp only [openToInteger, AddEquiv.apply_symm_apply]
  rw [f.hom.naturality_apply]
  congr 1

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma sectionsEquiv_generator {X : Scheme.{u}} (W : X.Etale)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : (etaleOpenFreeSheaf X).obj W ⟶ F) (V : X.Etale) (t : V ⟶ W) :
    a.hom.app (op V)
      ((toSheafify X.smallEtaleTopology
        (uliftYoneda.{u + 1}.obj W ⋙ AddCommGrpCat.free)).app
          (op V) (FreeAbelianGroup.of ⟨t⟩)) =
      F.obj.map t.op (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology W F a) := by
  have h := (toSheafify X.smallEtaleTopology
    (uliftYoneda.{u + 1}.obj W ⋙ AddCommGrpCat.free) ≫ a.hom).naturality t.op
  have h' := ConcreteCategory.congr_hom h (FreeAbelianGroup.of (ULift.up (𝟙 W)))
  change a.hom.app (op V)
      ((toSheafify X.smallEtaleTopology
        (uliftYoneda.{u + 1}.obj W ⋙ AddCommGrpCat.free)).app
          (op V) (FreeAbelianGroup.of ⟨t ≫ 𝟙 W⟩)) = _ at h'
  dsimp only [EtaleOpenComparison.sectionsEquiv, AddEquiv.trans_apply,
    Adjunction.homAddEquiv_apply]
  rw [Adjunction.homEquiv_apply]
  dsimp [EtaleOpenComparison.freeSectionsEquiv, Adjunction.homEquiv_apply,
    uliftYonedaEquiv]
  erw [Adjunction.homEquiv_apply]
  change a.hom.app (op V)
      ((toSheafify X.smallEtaleTopology
        (uliftYoneda.{u + 1}.obj W ⋙ AddCommGrpCat.free)).app
          (op V) (FreeAbelianGroup.of ⟨t⟩)) =
    F.obj.map t.op (a.hom.app (op W)
      ((toSheafify X.smallEtaleTopology
        (uliftYoneda.{u + 1}.obj W ⋙ AddCommGrpCat.free)).app
          (op W) (FreeAbelianGroup.of ⟨𝟙 W⟩)))
  simp only [Category.comp_id, NatTrans.comp_app, ConcreteCategory.comp_apply] at h'
  exact h'

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Pointwise restriction-unit calculation, adapted from the proved private helper
-- in WeilConjectures.AlgebraicGeometry.EtaleRestrictionPullbackUnitEq (Stacks 03CF and 03EF).
private theorem restriction_unit
    {T Y : Scheme.{u}} (f : T ⟶ Y) [Etale f]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (b : Y.Etale) (d : T.Etale)
    (ψ : d ⟶ (MorphismProperty.Over.pullback @Etale ⊤ f).obj b) :
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app F).hom.app (op b) ≫
        ((upperStar AddCommGrpCat.{u + 1} f).obj F).obj.map ψ.op ≫
        ((upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} f inferInstance).hom.app
          F).hom.app (op d) =
      F.obj.map (((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ f inferInstance
        _root_.trivial).homEquiv d b).symm ψ).op := by
  let A := AddCommGrpCat.{u + 1}
  let ρ := (upperStarIsoLocalizationRestriction A f inferInstance).hom.app F
  have hu := congrArg (fun α ↦ α.hom.app (op b))
    (Adjunction.unit_leftAdjointUniq_hom_app (upperStarLowerStarAdjunction A f)
      (localizationRestrictionLowerStarAdjunction A f inferInstance) F)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at hu
  rw [ρ.hom.naturality, ← Category.assoc]
  erw [show ((upperStarLowerStarAdjunction A f).unit.app F).hom.app (op b) ≫
    ρ.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj b)) =
    ((localizationRestrictionLowerStarAdjunction A f inferInstance).unit.app F).hom.app
      (op b) from hu]
  change (𝟙 _ ≫ F.obj.map _ ≫ 𝟙 _) ≫ F.obj.map _ = _
  simp only [Category.id_comp, Category.comp_id, ← Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma openToInteger_unit {X : Scheme.{u}} (W : X.Opens) :
    etaleOpenFreeSheafUnit W ≫
      (upperStar AddCommGrpCat.{u + 1} W.ι).map (openToInteger W) =
      (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} W.ι).inv.app
        (AddCommGrpCat.of (ULift ℤ)) := by
  let F := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift ℤ))
  let b := Scheme.Etale.mk (𝟙 W.toScheme)
  let v := (MorphismProperty.Over.map ⊤ (inferInstance : Etale W.ι)).obj b
  let t : v ⟶ Scheme.Etale.mk W.ι :=
    MorphismProperty.Over.homMk (𝟙 W.toScheme) (by rfl)
  let r : Scheme.Etale.mk W.ι ⟶ Scheme.Etale.mk (𝟙 X) :=
    MorphismProperty.Over.homMk W.ι (Category.comp_id _)
  let ρ := upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} W.ι inferInstance
  let adj := constantSheafAdj W.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1}
    (show IsTerminal b from IsTerminal.ofUniqueHom
      (fun a ↦ MorphismProperty.Over.homMk a.hom (Category.comp_id _))
      (fun a f ↦ by
        apply MorphismProperty.Over.Hom.ext
        exact (Category.comp_id _).symm.trans (MorphismProperty.Over.w f)))
  apply (adj.homEquiv _ _).injective
  apply (AddCommGrpCat.uliftZMultiplesAddEquiv _).injective
  have hz {B C : AddCommGrpCat.{u + 1}}
      (f : AddCommGrpCat.of (ULift.{u + 1} ℤ) ⟶ B) (g : B ⟶ C) :
      AddCommGrpCat.uliftZMultiplesAddEquiv C (f ≫ g) =
        g (AddCommGrpCat.uliftZMultiplesAddEquiv B f) := by rfl
  have hnat := congrArg (fun f ↦ f.hom.app (op b))
    (ρ.inv.naturality (openToInteger W))
  change _ ≫ _ = _ ≫ _ at hnat
  rw [adj.homEquiv_naturality_right, hz]
  dsimp only [adj, b]
  simp only [etaleOpenFreeSheafUnit, Equiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  change (((upperStar AddCommGrpCat.{u + 1} W.ι).map (openToInteger W)).hom.app
    (op b)) (etaleOpenFreeSheafSection W) = _
  dsimp only [etaleOpenFreeSheafSection]
  rw [← ConcreteCategory.comp_apply, ← hnat, ConcreteCategory.comp_apply]
  change (ρ.inv.app F).hom.app (op b)
    ((openToInteger W).hom.app (op v)
      ((toSheafify X.smallEtaleTopology
        (uliftYoneda.{u + 1}.obj (Scheme.Etale.mk W.ι) ⋙ AddCommGrpCat.free)).app
          (op v) (FreeAbelianGroup.of ⟨t⟩))) = _
  rw [sectionsEquiv_generator (Scheme.Etale.mk W.ι) F (openToInteger W) v t]
  simp only [F, openToInteger, AddEquiv.apply_symm_apply]
  change (ρ.inv.app F).hom.app (op b)
    (F.obj.map t.op (F.obj.map r.op (globalSectionsEquiv F (𝟙 F)))) = _
  have hp := constantSection_adjunct_pullback W.ι (AddCommGrpCat.of (ULift ℤ)) F (𝟙 F)
  dsimp only at hp
  rw [CategoryTheory.Functor.map_id] at hp
  erw [Category.comp_id ((Scheme.upperStarConstantSheafIso
    AddCommGrpCat.{u + 1} W.ι).inv.app (AddCommGrpCat.of (ULift ℤ)))] at hp
  rw [hp, hz]
  let ψ : b ⟶ (MorphismProperty.Over.pullback @Etale ⊤ W.ι).obj
      (Scheme.Etale.mk (𝟙 X)) := terminalSectionPullback W.ι
  have hu := restriction_unit W.ι F (Scheme.Etale.mk (𝟙 X)) b ψ
  have he : ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ W.ι inferInstance
      _root_.trivial).homEquiv b (Scheme.Etale.mk (𝟙 X))).symm ψ = t ≫ r := by
    apply (MorphismProperty.Over.mkIdTerminal @Etale X).hom_ext
  rw [he] at hu
  have hinv : (ρ.hom.app F).hom.app (op b) ≫ (ρ.inv.app F).hom.app (op b) = 𝟙 _ :=
    (((sheafSections W.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op b)).mapIso (ρ.app F)).hom_inv_id
  have hu' := congrArg (fun f ↦ f ≫ (ρ.inv.app F).hom.app (op b)) hu
  simp only [Category.assoc] at hu'
  change ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} W.ι).unit.app F).hom.app
      (op (Scheme.Etale.mk (𝟙 X))) ≫
    ((upperStar AddCommGrpCat.{u + 1} W.ι).obj F).obj.map ψ.op ≫
    (ρ.hom.app F).hom.app (op b) ≫ (ρ.inv.app F).hom.app (op b) = _ at hu'
  rw [hinv] at hu'
  simp only [Category.comp_id] at hu'
  rw [op_comp, Functor.map_comp] at hu'
  exact (ConcreteCategory.congr_hom hu' (globalSectionsEquiv F (𝟙 F))).symm

/-- Whole-to-open restriction identity for a normalized comparison.
Source: Stacks Project, Tag 03F3 (2), and Tag 0A50, proof;
the Hom-cocycle expansion of the parent restriction argument.
(blueprint: lem-weil-pbc-etale-resolution-section-canonical-whole-to-open)

Proof: Let K be the resolution evaluated at the terminal etale object. Since
K.homologyπ q is an epimorphism of abelian groups, write the given class as the
image of a cycle z. The constant-sheaf adjunction identifies K.iCycles q z
with a unique morphism f from the constant lifted integers to I.cocomplex.X q.
Naturality in the coefficient sheaf identifies its composite with the differential
with the differential of the section, which is zero; thus f is a Hom cocycle.
Let a be the free-sheaf map from the free sheaf on W to the constant integer
sheaf corresponding to the constant section 1 on W. The free-sheaf sections
adjunction identifies a composed with f with the restriction of the original
section. Naturality of homologyπ identifies its cycle class with the homology
map of etaleSectionMap. Apply c.global_cocycle and c.open_cocycle to the two
cycles. The formula I.mk₀_comp_extMk identifies the second Ext class with
precomposition of the first by a. In etaleOpenObjectCohomologyMap, pulling
back a and precomposing with etaleOpenFreeSheafUnit W is the inverse of the
constant-sheaf comparison: both maps classify the section 1 by the constant
sheaf adjunction. Functoriality of Ext under the exact inverse-image functor
and associativity of Ext composition now give cohomologyMap W.ι on the first
class. Surjectivity of homologyπ gives the equality for every class. The
argument uses no positive-degree or nonempty-open assumption, so includes
q = 0, the empty open, identity restriction and the zero sheaf. -/
theorem resolutionSection_canonical_whole_to_open {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution G)
    (c : ResolutionSectionCanonicalComparison G I) :
    ∀ W q x, c.openEquiv W q (HomologicalComplex.homologyMap (etaleSectionMap
      (MorphismProperty.Over.homMk W.ι (Category.comp_id _) :
        Scheme.Etale.mk W.ι ⟶ Scheme.Etale.mk (𝟙 X)) I.cocomplex) q x) =
      cohomologyMap W.ι G q (c.globalEquiv q x) := by
  intro W q x
  let K := ((etaleSectionFunctor (Scheme.Etale.mk (𝟙 X))).mapHomologicalComplex
    (.up ℕ)).obj I.cocomplex
  let L := ((etaleSectionFunctor (Scheme.Etale.mk W.ι)).mapHomologicalComplex
    (.up ℕ)).obj I.cocomplex
  let r := etaleSectionMap
    (MorphismProperty.Over.homMk W.ι (Category.comp_id _) :
      Scheme.Etale.mk W.ι ⟶ Scheme.Etale.mk (𝟙 X)) I.cocomplex
  obtain ⟨z, rfl⟩ := (AddCommGrpCat.epi_iff_surjective (K.homologyπ q)).mp
    inferInstance x
  let f := (globalSectionsEquiv (I.cocomplex.X q)).symm ((K.iCycles q) z)
  have hz : (K.iCycles q) z = globalSectionsEquiv (I.cocomplex.X q) f := by
    simp only [f, AddEquiv.apply_symm_apply]
  have hf : f ≫ I.cocomplex.d q (q + 1) = 0 := by
    apply (globalSectionsEquiv _).injective
    rw [globalSectionsEquiv_comp, ← hz]
    change (K.d q (q + 1)) ((K.iCycles q) z) = _
    have h := ConcreteCategory.congr_hom (K.iCycles_d q (q + 1)) z
    rw [map_zero]
    exact h
  have hres : (L.iCycles q) ((HomologicalComplex.cyclesMap r q) z) =
      EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology
        (Scheme.Etale.mk W.ι) (I.cocomplex.X q) (openToInteger W ≫ f) := by
    rw [openToInteger_comp, ← hz]
    exact ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i r q) z
  have hπ := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality r q) z
  change (HomologicalComplex.homologyMap r q) ((K.homologyπ q) z) =
    (L.homologyπ q) ((HomologicalComplex.cyclesMap r q) z) at hπ
  rw [hπ, c.open_cocycle W q (openToInteger W ≫ f)
    (by simp [Category.assoc, hf]) _ hres, c.global_cocycle q f hf z hz]
  rw [← I.mk₀_comp_extMk f (q + 1) rfl hf (openToInteger W)]
  change (Abelian.Ext.mk₀ (etaleOpenFreeSheafUnit W)).comp
      (((Abelian.Ext.mk₀ (openToInteger W)).comp
        (I.extMk f (q + 1) rfl hf) (zero_add q)).mapExactFunctor
          (upperStar AddCommGrpCat.{u + 1} W.ι)) (zero_add q) = _
  rw [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.mk₀_comp_mk₀_assoc]
  rw [cohomologyMap_apply]
  rw [openToInteger_unit]
  rfl
end AlgebraicGeometry.Etale
