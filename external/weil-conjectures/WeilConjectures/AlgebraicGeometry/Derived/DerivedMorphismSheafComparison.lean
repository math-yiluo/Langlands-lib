/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import WeilConjectures.CategoryTheory.Derived.DerivedMorphismPresheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement

public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedHomFiniteProducts
/-!
# Canonical comparison and evaluation of derived morphism sheaves

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
set_option autoImplicit false
private lemma derivedSquareCoherence
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
  [Category C₀] [Category C₁] [Category C₂]
  [Category D₀] [Category D₁] [Category D₂]
  [Abelian C₀] [Abelian C₁] [Abelian C₂]
  [Abelian D₀] [Abelian D₁] [Abelian D₂]
  [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [HasDerivedCategory D₀] [HasDerivedCategory D₁] [HasDerivedCategory D₂]
  (R : C₀ ⥤ C₁) (S : C₁ ⥤ C₂) (R' : C₀ ⥤ C₂)
  (H : C₀ ⥤ D₀) (F : C₁ ⥤ D₁) (G : C₂ ⥤ D₂)
  (T : D₁ ⥤ D₂) (P : D₀ ⥤ D₁) (P' : D₀ ⥤ D₂)
  [R.Additive] [S.Additive] [R'.Additive]
  [H.Additive] [F.Additive] [G.Additive] [T.Additive] [P.Additive] [P'.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [PreservesFiniteLimits P'] [PreservesFiniteColimits P']
    (a : R ⋙ S ≅ R') (b : R' ⋙ G ≅ H ⋙ P')
    (c : R ⋙ F ≅ H ⋙ P) (d : P ⋙ T ≅ P') (e : S ⋙ G ≅ F ⋙ T)
    (hab : Functor.isoWhiskerRight a G ≪≫ b =
      Functor.isoWhiskerLeft R e ≪≫ Functor.isoWhiskerRight c T ≪≫
        Functor.isoWhiskerLeft H d) :
    Functor.whiskerRight
        (Functor.mapDerivedCategoryCompIso R S ≪≫
          Functor.mapDerivedCategoryNatIso a).hom G.mapDerivedCategory ≫
      (Functor.mapDerivedCategorySquareIso b).hom =
    Functor.whiskerLeft R.mapDerivedCategory (Functor.mapDerivedCategorySquareIso e).hom ≫
      Functor.whiskerRight (Functor.mapDerivedCategorySquareIso c).hom T.mapDerivedCategory ≫
        Functor.whiskerLeft H.mapDerivedCategory
          (Functor.mapDerivedCategoryCompIso P T ≪≫
            Functor.mapDerivedCategoryNatIso d).hom := by
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Iso.trans_hom, Iso.symm_hom, Functor.mapDerivedCategorySquareIso, Functor.map_comp,
    Category.assoc]
  rw [← cancel_epi ((Functor.mapDerivedCategoryCompIso (R ⋙ S) G).inv.app K ≫
    G.mapDerivedCategory.map ((Functor.mapDerivedCategoryCompIso R S).inv.app K))]
  rw [← cancel_mono ((Functor.mapDerivedCategoryCompIso H P').hom.app K)]
  have ha := NatTrans.congr_app
    (Functor.mapDerivedCategoryNatIso_isoWhiskerRight a G) K
  have he := NatTrans.congr_app
    (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft R e) K
  have hc := NatTrans.congr_app
    (Functor.mapDerivedCategoryNatIso_isoWhiskerRight c T) K
  have hd := NatTrans.congr_app
    (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft H d) K
  have hRS := NatTrans.congr_app (Functor.mapDerivedCategoryCompIso_assoc R S G) K
  have hRF := NatTrans.congr_app (Functor.mapDerivedCategoryCompIso_assoc R F T) K
  have hHP := NatTrans.congr_app (Functor.mapDerivedCategoryCompIso_assoc H P T) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    at ha he hc hd hRS hRF hHP
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    Iso.inv_hom_id_app_assoc]
  rw [← reassoc_of% ha, Iso.inv_hom_id_app_assoc, Category.comp_id]
  rw [← reassoc_of% hRS, Iso.inv_hom_id_app_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% he, reassoc_of% hRF]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hc, ← reassoc_of% hHP, Iso.inv_hom_id_app_assoc,
    ← reassoc_of% hd, Iso.inv_hom_id_app, Category.comp_id]
  have h := congrArg (fun z ↦ (Functor.mapDerivedCategoryNatIso z).hom.app K) hab
  simpa only [Functor.mapDerivedCategoryNatIso_trans, NatTrans.comp_app,
    Category.assoc] using h

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]

/-- The actual inverse-image functor on set sheaves for the etale/pro-etale comparison.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable abbrev comparisonSetUpperStar :=
  Functor.sheafPullbackConstruction.sheafPullback (toProEt X)
    (Type (u + 1)) X.smallEtaleTopology (ProEt.topology X)

/-- The exact module-sheaf comparison inverse image, applied to the actual derived category.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable abbrev derivedComparison :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory

/-- The etale-to-pro-etale inclusion induces a continuous functor on localized sites.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison)

Proof: An etale cover on the slice is a jointly surjective etale covering of its domain. Its
image in the pro-etale slice is a covering family. Covering sieves are stable under the base
changes that define the localized topologies. The continuity criterion on covering families
therefore applies to the postcomposition functor. -/
theorem comparisonSlice_continuous (V : X.Etale) :
    (Over.post (toProEt X)).IsContinuous (X.smallEtaleTopology.over V)
      ((ProEt.topology X).over ((toProEt X).obj V)) := by
  have : RepresentablyFlat (Over.post (X := V) (toProEt X)) :=
    flat_of_preservesFiniteLimits _
  exact Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
    ((CoverPreserving.of_isContinuous (toProEt X) _ _).overPost V)

attribute [instance] comparisonSlice_continuous

/-- The constructed comparison inverse image on the localized etale and pro-etale sites.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable abbrev comparisonSliceUpperStar (V : X.Etale) :=
  Functor.sheafPullbackConstruction.sheafPullback (Over.post (toProEt X))
    (ModuleCat.{u + 1} B) (X.smallEtaleTopology.over V)
      ((ProEt.topology X).over ((toProEt X).obj V))

/-- The constructed pullback/pushforward adjunction on the localized sites.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable abbrev comparisonSliceAdjunction (V : X.Etale) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Over.post (toProEt X))
    (ModuleCat.{u + 1} B) (X.smallEtaleTopology.over V)
      ((ProEt.topology X).over ((toProEt X).obj V))

/-- The localized comparison direct image is additive, section by section.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
instance comparisonSliceLowerStar_additive (V : X.Etale) :
    ((Over.post (toProEt X)).sheafPushforwardContinuous (ModuleCat.{u + 1} B)
      (X.smallEtaleTopology.over V)
      ((ProEt.topology X).over ((toProEt X).obj V))).Additive where
  map_add := by intros; rfl

/-- The localized comparison inverse image is additive by its adjunction.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable instance comparisonSliceUpperStar_additive (V : X.Etale) :
    (comparisonSliceUpperStar X B V).Additive :=
  (comparisonSliceAdjunction X B V).left_adjoint_additive

/-- The localized comparison inverse image preserves finite colimits as a left adjoint.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
instance comparisonSliceUpperStar_preservesFiniteColimits (V : X.Etale) :
    PreservesFiniteColimits (comparisonSliceUpperStar X B V) :=
  letI := (comparisonSliceAdjunction X B V).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _

/-- The localized comparison inverse image is left exact.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison)

Proof: The inclusion on slices preserves finite limits: the underlying inclusion does so, and
slice finite limits are computed in the original categories. Together with continuity, the
constructed sheaf inverse image is the inverse image of a geometric morphism and preserves
finite limits. The same calculation applies to module-valued sheaves since the finite-limit
comparison is computed on their underlying sheaves. -/
theorem comparisonSliceUpperStar_preservesFiniteLimits (V : X.Etale) :
    PreservesFiniteLimits (comparisonSliceUpperStar X B V) := by
  have : RepresentablyFlat (Over.post (X := V) (toProEt X)) :=
    flat_of_preservesFiniteLimits _
  exact Functor.sheafPullbackConstruction.instPreservesFiniteLimitsSheafSheafPullback
    (Over.post (toProEt X)) (ModuleCat.{u + 1} B) (X.smallEtaleTopology.over V)
      ((ProEt.topology X).over ((toProEt X).obj V))

attribute [instance] comparisonSliceUpperStar_preservesFiniteLimits

/-- The canonical slice base-change map, defined by restricting the unit of the global comparison
adjunction and transposing under the slice adjunction.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable def comparisonSliceBaseMap (V : X.Etale)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    (comparisonSliceUpperStar X B V).obj (M.over V) ⟶
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).obj M).over
        ((toProEt X).obj V) :=
  ((comparisonSliceAdjunction X B V).homEquiv _ _).symm
    ((X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} B) V).map
      ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) X).unit.app M))

private noncomputable def comparisonStarIso (V : X.Etale) :
    Over.star V ⋙ Over.post (toProEt X) ≅
      toProEt X ⋙ Over.star ((toProEt X).obj V) :=
  NatIso.ofComponents (fun W ↦ Over.isoMk (asIso (prodComparison (toProEt X) V W))
    (by simp [Over.post, Over.star_obj_hom])) (by
      intro W Z f
      ext
      simpa using prodComparison_natural (toProEt X) (𝟙 V) f)

/-- The specified canonical slice base-change map is invertible and natural in the module sheaf.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison)

Proof: Both composites are inverse image for the same geometric morphism from the localized
pro-etale topos to the etale topos. The comparison obtained by transposing the restricted unit
is their canonical localization comparison, and is invertible: on a sheafified presheaf it is
the restriction/sheafification comparison on the slice. Sheafification and restriction commute
by the covering-sieve description of a localized topology. Naturality follows by restricting
naturality of the adjunction unit and transposing through the slice adjunction. -/
theorem comparisonSliceBaseMap_properties (V : X.Etale) :
    (∀ M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B),
      IsIso (comparisonSliceBaseMap X B V M)) ∧
    (∀ (M N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) (f : M ⟶ N),
      (comparisonSliceUpperStar X B V).map
          ((X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} B) V).map f) ≫
        comparisonSliceBaseMap X B V N =
      comparisonSliceBaseMap X B V M ≫
        ((ProEt.topology X).overPullback (ModuleCat.{u + 1} B)
          ((toProEt X).obj V)).map
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).map f)) := by
  let rV := (Over.forgetAdjStar V).sheafPushforwardContinuous
    (E := ModuleCat.{u + 1} B) (X.smallEtaleTopology.over V) X.smallEtaleTopology
  let rU := (Over.forgetAdjStar ((toProEt X).obj V)).sheafPushforwardContinuous
    (E := ModuleCat.{u + 1} B)
    ((ProEt.topology X).over ((toProEt X).obj V)) (ProEt.topology X)
  have : (toProEt X ⋙ Over.star ((toProEt X).obj V)).IsContinuous
      X.smallEtaleTopology ((ProEt.topology X).over ((toProEt X).obj V)) :=
    Functor.isContinuous_comp _ _ _ (ProEt.topology X) _
  let eR :=
    Functor.sheafPushforwardContinuousComp' (comparisonStarIso X V)
      (ModuleCat.{u + 1} B) X.smallEtaleTopology
      (X.smallEtaleTopology.over V)
      ((ProEt.topology X).over ((toProEt X).obj V)) ≪≫
    (Functor.sheafPushforwardContinuousComp (toProEt X)
      (Over.star ((toProEt X).obj V)) (ModuleCat.{u + 1} B)
      X.smallEtaleTopology (ProEt.topology X)
      ((ProEt.topology X).over ((toProEt X).obj V))).symm
  let adj₁ := (rV.comp (comparisonSliceAdjunction X B V)).ofNatIsoRight eR
  let adj₂ := (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) X).comp rU
  let e := Adjunction.leftAdjointUniq adj₁ adj₂
  have he (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
      e.hom.app M = comparisonSliceBaseMap X B V M := by
    apply (adj₁.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    change adj₂.unit.app M =
      ((rV.comp (comparisonSliceAdjunction X B V)).ofNatIsoRight eR).homEquiv _ _
        (comparisonSliceBaseMap X B V M)
    rw [Adjunction.homEquiv_ofNatIsoRight_apply]
    change adj₂.unit.app M =
      rV.homEquiv _ _
        ((comparisonSliceAdjunction X B V).homEquiv _ _
          (comparisonSliceBaseMap X B V M)) ≫ eR.hom.app _
    rw [comparisonSliceBaseMap, Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    dsimp only [adj₂]
    rw [Adjunction.comp_unit_app]
    ext W : 3
    let η := (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) X).unit.app M
    let N := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).obj M
    change η.hom.app W ≫ N.obj.map (prod.snd :
        (toProEt X).obj V ⨯ (toProEt X).obj W.unop ⟶ _).op =
      (M.obj.map (prod.snd : V ⨯ W.unop ⟶ _).op ≫
        η.hom.app (op (V ⨯ W.unop))) ≫
          N.obj.map (inv (prodComparison (toProEt X) V W.unop)).op
    have hn : M.obj.map (prod.snd : V ⨯ W.unop ⟶ W.unop).op ≫
        η.hom.app (op (V ⨯ W.unop)) =
      η.hom.app W ≫ N.obj.map ((toProEt X).map prod.snd).op :=
        η.hom.naturality (prod.snd : V ⨯ W.unop ⟶ W.unop).op
    rw [hn]
    simp only [Category.assoc, ← Functor.map_comp, ← op_comp]
    rw [inv_prodComparison_map_snd]
  constructor
  · intro M
    rw [← he M]
    infer_instance
  · intro M N f
    simpa only [he, Functor.comp_map] using e.hom.naturality f

/-- The natural isomorphism formed from the specified invertible slice base-change map.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable def comparisonSliceBaseIso (V : X.Etale) :
    X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} B) V ⋙
      comparisonSliceUpperStar X B V ≅
    ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X ⋙
      (ProEt.topology X).overPullback (ModuleCat.{u + 1} B) ((toProEt X).obj V) :=
  NatIso.ofComponents (fun M ↦
    @asIso _ _ _ _ (comparisonSliceBaseMap X B V M)
      ((comparisonSliceBaseMap_properties X B V).1 M))
    ((comparisonSliceBaseMap_properties X B V).2 _ _)

/-- The induced canonical commutation of comparison inverse image and restriction on derived
categories.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable def derivedComparisonSliceIso (V : X.Etale) :
    derivedSliceRestriction X.smallEtaleTopology B V ⋙
      (comparisonSliceUpperStar X B V).mapDerivedCategory ≅
    derivedComparison X B ⋙
      derivedSliceRestriction (ProEt.topology X) B ((toProEt X).obj V) :=
  (Functor.mapDerivedCategoryCompIso _ _) ≪≫
    Functor.mapDerivedCategoryNatIso (comparisonSliceBaseIso X B V) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm

private noncomputable def comparisonPullbackIso {V W : X.Etale} (g : W ⟶ V) :
    Over.pullback g ⋙ Over.post (toProEt X) ≅
      Over.post (toProEt X) ⋙ Over.pullback ((toProEt X).map g) :=
  NatIso.ofComponents (fun T ↦ Over.isoMk
    (asIso (pullbackComparison (toProEt X) T.hom g)) (by
      exact pullbackComparison_comp_snd (toProEt X) T.hom g)) (by
        intro T S f
        ext
        apply pullback.hom_ext
        · simp [Over.pullback, Over.post, pullbackComparison, ← Functor.map_comp]
        · simp [Over.pullback, Over.post, pullbackComparison, ← Functor.map_comp])

private noncomputable def comparisonSliceMap {V W : X.Etale} (g : W ⟶ V)
    (M : Sheaf (X.smallEtaleTopology.over V) (ModuleCat.{u + 1} B)) :
    (comparisonSliceUpperStar X B W).obj
        ((X.smallEtaleTopology.overMapPullback (ModuleCat.{u + 1} B) g).obj M) ⟶
      ((ProEt.topology X).overMapPullback (ModuleCat.{u + 1} B) ((toProEt X).map g)).obj
        ((comparisonSliceUpperStar X B V).obj M) :=
  ((comparisonSliceAdjunction X B W).homEquiv _ _).symm
    ((X.smallEtaleTopology.overMapPullback (ModuleCat.{u + 1} B) g).map
      ((comparisonSliceAdjunction X B V).unit.app M))

private noncomputable def comparisonSliceMapIso {V W : X.Etale} (g : W ⟶ V) :
    X.smallEtaleTopology.overMapPullback (ModuleCat.{u + 1} B) g ⋙
      comparisonSliceUpperStar X B W ≅
    comparisonSliceUpperStar X B V ⋙
      (ProEt.topology X).overMapPullback (ModuleCat.{u + 1} B) ((toProEt X).map g) := by
  let rV := (Over.mapPullbackAdj g).sheafPushforwardContinuous
    (E := ModuleCat.{u + 1} B)
    (X.smallEtaleTopology.over W) (X.smallEtaleTopology.over V)
  let rU := (Over.mapPullbackAdj ((toProEt X).map g)).sheafPushforwardContinuous
    (E := ModuleCat.{u + 1} B)
    ((ProEt.topology X).over ((toProEt X).obj W))
    ((ProEt.topology X).over ((toProEt X).obj V))
  have : (Over.post (X := V) (toProEt X) ⋙
      Over.pullback ((toProEt X).map g)).IsContinuous
      (X.smallEtaleTopology.over V)
      ((ProEt.topology X).over ((toProEt X).obj W)) :=
    Functor.isContinuous_comp _ _ _
      ((ProEt.topology X).over ((toProEt X).obj V)) _
  let eR :=
    Functor.sheafPushforwardContinuousComp' (comparisonPullbackIso X g)
      (ModuleCat.{u + 1} B) (X.smallEtaleTopology.over V)
      (X.smallEtaleTopology.over W)
      ((ProEt.topology X).over ((toProEt X).obj W)) ≪≫
    (Functor.sheafPushforwardContinuousComp (Over.post (X := V) (toProEt X))
      (Over.pullback ((toProEt X).map g)) (ModuleCat.{u + 1} B)
      (X.smallEtaleTopology.over V)
      ((ProEt.topology X).over ((toProEt X).obj V))
      ((ProEt.topology X).over ((toProEt X).obj W))).symm
  let adj₁ := (rV.comp (comparisonSliceAdjunction X B W)).ofNatIsoRight eR
  let adj₂ := (comparisonSliceAdjunction X B V).comp rU
  let e := Adjunction.leftAdjointUniq adj₁ adj₂
  have he (M : Sheaf (X.smallEtaleTopology.over V) (ModuleCat.{u + 1} B)) :
      e.hom.app M = comparisonSliceMap X B g M := by
    apply (adj₁.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    change adj₂.unit.app M =
      ((rV.comp (comparisonSliceAdjunction X B W)).ofNatIsoRight eR).homEquiv _ _
        (comparisonSliceMap X B g M)
    rw [Adjunction.homEquiv_ofNatIsoRight_apply]
    change adj₂.unit.app M = rV.homEquiv _ _
      ((comparisonSliceAdjunction X B W).homEquiv _ _
        (comparisonSliceMap X B g M)) ≫ eR.hom.app _
    rw [comparisonSliceMap, Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    dsimp only [adj₂]
    rw [Adjunction.comp_unit_app]
    ext T : 3
    let η := (comparisonSliceAdjunction X B V).unit.app M
    let N := (comparisonSliceUpperStar X B V).obj M
    let a := (Over.mapPullbackAdj g).counit.app T.unop
    let b := (Over.mapPullbackAdj ((toProEt X).map g)).counit.app
      ((Over.post (X := V) (toProEt X)).obj T.unop)
    let k := (Over.map ((toProEt X).map g)).map
      ((comparisonPullbackIso X g).inv.app T.unop)
    change η.hom.app T ≫ N.obj.map b.op =
      (M.obj.map a.op ≫ η.hom.app _) ≫ N.obj.map k.op
    erw [η.hom.naturality a.op]
    have hk : k ≫ (Over.post (X := V) (toProEt X)).map a = b := by
      ext
      change inv (pullbackComparison (toProEt X) T.unop.hom g) ≫
        (toProEt X).map (pullback.fst T.unop.hom g) = _
      rw [← cancel_epi (pullbackComparison (toProEt X) T.unop.hom g),
        IsIso.hom_inv_id_assoc]
      exact (pullbackComparison_comp_fst (toProEt X) T.unop.hom g).symm
    change η.hom.app T ≫ N.obj.map b.op =
      (η.hom.app T ≫ N.obj.map ((Over.post (X := V) (toProEt X)).map a).op) ≫
        N.obj.map k.op
    rw [Category.assoc, ← Functor.map_comp, ← op_comp, hk]
  exact NatIso.ofComponents (fun M ↦
    @asIso _ _ _ _ (comparisonSliceMap X B g M)
      (by rw [← he M]; infer_instance)) (by
        intro M N f
        simpa only [asIso_hom, ← he] using e.hom.naturality f)

private theorem comparisonSliceMapIso_coherence {V W : X.Etale} (g : W ⟶ V)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    (comparisonSliceUpperStar X B W).map
        ((sliceRestrictionMapIso X.smallEtaleTopology B g).hom.app M) ≫
      (comparisonSliceBaseIso X B W).hom.app M =
    (comparisonSliceMapIso X B g).hom.app (M.over V) ≫
      ((ProEt.topology X).overMapPullback (ModuleCat.{u + 1} B)
        ((toProEt X).map g)).map ((comparisonSliceBaseIso X B V).hom.app M) ≫
      (sliceRestrictionMapIso (ProEt.topology X) B ((toProEt X).map g)).hom.app
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).obj M) := by
  apply ((comparisonSliceAdjunction X B W).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  change _ = ((comparisonSliceAdjunction X B W).homEquiv _ _
    (comparisonSliceMap X B g (M.over V))) ≫ _
  rw [comparisonSliceMap, Equiv.apply_symm_apply]
  change (sliceRestrictionMapIso X.smallEtaleTopology B g).hom.app M ≫
    ((comparisonSliceAdjunction X B W).homEquiv _ _
      (comparisonSliceBaseMap X B W M)) = _
  rw [comparisonSliceBaseMap, Equiv.apply_symm_apply]
  ext T : 3
  let η := (comparisonSliceAdjunction X B V).unit.app (M.over V)
  let m := (comparisonSliceBaseMap X B V M)
  change _ = η.hom.app (op ((Over.map g).obj T.unop)) ≫
    m.hom.app (op ((Over.post (X := V) (toProEt X)).obj
      ((Over.map g).obj T.unop)))
  have hη := ((comparisonSliceAdjunction X B V).homEquiv (M.over V)
    (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).obj M).over
      ((toProEt X).obj V))).apply_symm_apply
    ((X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} B) V).map
      ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) X).unit.app M))
  have hη' := congrArg (fun k ↦ k.hom.app (op ((Over.map g).obj T.unop))) hη
  change η.hom.app (op ((Over.map g).obj T.unop)) ≫ m.hom.app _ = _ at hη'
  change 𝟙 _ ≫ ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) X).unit.app M).hom.app
    (op T.unop.left) = _
  rw [Category.id_comp]
  exact hη'.symm

private theorem derivedComparisonRestrictionCoherence {V W : X.Etale} (g : W ⟶ V)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (comparisonSliceUpperStar X B W).mapDerivedCategory.map
        ((derivedSliceMapIso X.smallEtaleTopology B g).hom.app K) ≫
      (derivedComparisonSliceIso X B W).hom.app K =
    (Functor.mapDerivedCategorySquareIso (comparisonSliceMapIso X B g)).hom.app
        ((derivedSliceRestriction X.smallEtaleTopology B V).obj K) ≫
      (derivedSliceMap (ProEt.topology X) B ((toProEt X).map g)).map
        ((derivedComparisonSliceIso X B V).hom.app K) ≫
      (derivedSliceMapIso (ProEt.topology X) B ((toProEt X).map g)).hom.app
        ((derivedComparison X B).obj K) := by
  have h := derivedSquareCoherence
    (X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} B) V)
    (X.smallEtaleTopology.overMapPullback (ModuleCat.{u + 1} B) g)
    (X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} B) W)
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X)
    (comparisonSliceUpperStar X B V) (comparisonSliceUpperStar X B W)
    ((ProEt.topology X).overMapPullback (ModuleCat.{u + 1} B) ((toProEt X).map g))
    ((ProEt.topology X).overPullback (ModuleCat.{u + 1} B) ((toProEt X).obj V))
    ((ProEt.topology X).overPullback (ModuleCat.{u + 1} B) ((toProEt X).obj W))
    (sliceRestrictionMapIso X.smallEtaleTopology B g) (comparisonSliceBaseIso X B W)
    (comparisonSliceBaseIso X B V)
    (sliceRestrictionMapIso (ProEt.topology X) B ((toProEt X).map g))
    (comparisonSliceMapIso X B g) (by
      apply Iso.ext
      apply NatTrans.ext
      funext M
      exact comparisonSliceMapIso_coherence X B g M)
  exact NatTrans.congr_app h K

variable (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))

/-- Pullback of an actual etale-local derived morphism under the localized comparison functor.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable def derivedComparisonLocalHom (V : X.Etale)
    (f : (derivedSliceRestriction X.smallEtaleTopology B V).obj A ⟶
      (derivedSliceRestriction X.smallEtaleTopology B V).obj D) :
    (derivedSliceRestriction (ProEt.topology X) B ((toProEt X).obj V)).obj
        ((derivedComparison X B).obj A) ⟶
      (derivedSliceRestriction (ProEt.topology X) B ((toProEt X).obj V)).obj
        ((derivedComparison X B).obj D) :=
  (derivedComparisonSliceIso X B V).inv.app A ≫
    (comparisonSliceUpperStar X B V).mapDerivedCategory.map f ≫
      (derivedComparisonSliceIso X B V).hom.app D

/-- Pullback of an actual etale-local derived isomorphism under that same functor.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable def derivedComparisonLocalIso (V : X.Etale)
    (f : (derivedSliceRestriction X.smallEtaleTopology B V).obj A ≅
      (derivedSliceRestriction X.smallEtaleTopology B V).obj D) :
    (derivedSliceRestriction (ProEt.topology X) B ((toProEt X).obj V)).obj
        ((derivedComparison X B).obj A) ≅
      (derivedSliceRestriction (ProEt.topology X) B ((toProEt X).obj V)).obj
        ((derivedComparison X B).obj D) :=
  ((derivedComparisonSliceIso X B V).app A).symm ≪≫
    (comparisonSliceUpperStar X B V).mapDerivedCategory.mapIso f ≪≫
      (derivedComparisonSliceIso X B V).app D

private theorem derivedComparisonLocalHom_natural {V W : X.Etale} (g : W ⟶ V)
    (f : (derivedSliceRestriction X.smallEtaleTopology B V).obj A ⟶
      (derivedSliceRestriction X.smallEtaleTopology B V).obj D) :
    derivedComparisonLocalHom X B A D W
        (derivedLocalHomRestriction X.smallEtaleTopology B A D g f) =
      derivedLocalHomRestriction (ProEt.topology X) B
        ((derivedComparison X B).obj A) ((derivedComparison X B).obj D)
        ((toProEt X).map g) (derivedComparisonLocalHom X B A D V f) := by
  let G := (comparisonSliceUpperStar X B W).mapDerivedCategory
  let T := derivedSliceMap (ProEt.topology X) B ((toProEt X).map g)
  let a := derivedSliceMapIso X.smallEtaleTopology B g
  let b := derivedComparisonSliceIso X B W
  let c := derivedComparisonSliceIso X B V
  let d := derivedSliceMapIso (ProEt.topology X) B ((toProEt X).map g)
  let e := Functor.mapDerivedCategorySquareIso (comparisonSliceMapIso X B g)
  have hA := derivedComparisonRestrictionCoherence X B g A
  have hD := derivedComparisonRestrictionCoherence X B g D
  change G.map (a.hom.app A) ≫ b.hom.app A =
    e.hom.app _ ≫ T.map (c.hom.app A) ≫ d.hom.app _ at hA
  change G.map (a.hom.app D) ≫ b.hom.app D =
    e.hom.app _ ≫ T.map (c.hom.app D) ≫ d.hom.app _ at hD
  change b.inv.app A ≫ G.map (a.inv.app A ≫ _ ≫ a.hom.app D) ≫ b.hom.app D =
    d.inv.app _ ≫ T.map (c.inv.app A ≫ _ ≫ c.hom.app D) ≫ d.hom.app _
  rw [← cancel_epi (G.map (a.hom.app A) ≫ b.hom.app A)]
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  simp only [← G.map_comp_assoc, Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% hA]
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  simp only [← T.map_comp_assoc, Iso.hom_inv_id_app_assoc]
  simp only [Functor.map_comp, Category.assoc]
  have hn := e.hom.naturality f
  simp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn, ← hD]

/-- The pro-etale sheafification of local derived Hom between the pulled-back objects.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable abbrev derivedComparisonHomTarget :=
  derivedLocalHomSheaf (ProEt.topology X) B
    ((derivedComparison X B).obj A) ((derivedComparison X B).obj D)

/-- The pro-etale sheafification of local derived Isom between the pulled-back objects.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable abbrev derivedComparisonIsoTarget :=
  derivedLocalIsoSheaf (ProEt.topology X) B
    ((derivedComparison X B).obj A) ((derivedComparison X B).obj D)

/-- Pull back a local derived morphism and apply the pro-etale sheafification unit.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable def derivedComparisonHomUnit (V : X.Etale)
    (f : (derivedLocalHomPresheaf X.smallEtaleTopology B A D).obj (op V)) :
    (derivedComparisonHomTarget X B A D).obj.obj (op ((toProEt X).obj V)) :=
  (toSheafify (ProEt.topology X)
    (derivedLocalHomPresheaf (ProEt.topology X) B
      ((derivedComparison X B).obj A) ((derivedComparison X B).obj D))).app
        (op ((toProEt X).obj V)) (derivedComparisonLocalHom X B A D V f)

/-- Pull back a local derived isomorphism and apply the pro-etale sheafification unit.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable def derivedComparisonIsoUnit (V : X.Etale)
    (f : (derivedLocalIsoPresheaf X.smallEtaleTopology B A D).obj (op V)) :
    (derivedComparisonIsoTarget X B A D).obj.obj (op ((toProEt X).obj V)) :=
  (toSheafify (ProEt.topology X)
    (derivedLocalIsoPresheaf (ProEt.topology X) B
      ((derivedComparison X B).obj A) ((derivedComparison X B).obj D))).app
        (op ((toProEt X).obj V)) (derivedComparisonLocalIso X B A D V f)

/-- Local derived pullback followed by sheafification commutes with restriction on the etale site.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison)

Proof: The canonical slice comparison is defined by adjunction units, so satisfies the
localization cocycle. Derive that cocycle. Expand the local pullback and restriction
conjugations; the cocycle and functoriality identify the two resulting derived morphisms. Apply
naturality of the pro-etale sheafification unit. For isomorphisms use the same argument on hom
components and then isomorphism extensionality. -/
theorem derivedComparisonUnits_natural :
    (∀ (V W : X.Etale) (g : W ⟶ V)
      (f : (derivedLocalHomPresheaf X.smallEtaleTopology B A D).obj (op V)),
      derivedComparisonHomUnit X B A D W
          (derivedLocalHomRestriction X.smallEtaleTopology B A D g f) =
        (derivedComparisonHomTarget X B A D).obj.map ((toProEt X).map g).op
          (derivedComparisonHomUnit X B A D V f)) ∧
    (∀ (V W : X.Etale) (g : W ⟶ V)
      (f : (derivedLocalIsoPresheaf X.smallEtaleTopology B A D).obj (op V)),
      derivedComparisonIsoUnit X B A D W
          (derivedLocalIsoRestriction X.smallEtaleTopology B A D g f) =
        (derivedComparisonIsoTarget X B A D).obj.map ((toProEt X).map g).op
          (derivedComparisonIsoUnit X B A D V f)) := by
  constructor
  · intro V W g f
    dsimp only [derivedComparisonHomUnit, derivedComparisonHomTarget,
      derivedLocalHomSheaf]
    rw [← NatTrans.naturality_apply]
    congr 1
    exact derivedComparisonLocalHom_natural X B A D g f
  · intro V W g f
    dsimp only [derivedComparisonIsoUnit, derivedComparisonIsoTarget,
      derivedLocalIsoSheaf]
    rw [← NatTrans.naturality_apply]
    congr 1
    apply Iso.ext
    exact derivedComparisonLocalHom_natural X B A D g f.hom

/-- The presheaf map formed from the specified local derived Hom pullbacks.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable def derivedComparisonHomPresheafMap :
    derivedLocalHomPresheaf X.smallEtaleTopology B A D ⟶
      ((toProEt X).sheafPushforwardContinuous (Type (u + 1))
        X.smallEtaleTopology (ProEt.topology X)).obj
          (derivedComparisonHomTarget X B A D) |>.obj where
  app V := ↾(derivedComparisonHomUnit X B A D V.unop)
  naturality := by
    intro V W f
    apply ConcreteCategory.hom_ext
    intro a
    exact (derivedComparisonUnits_natural X B A D).1 _ _ f.unop a

/-- The presheaf map formed from the specified local derived Isom pullbacks.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable def derivedComparisonIsoPresheafMap :
    derivedLocalIsoPresheaf X.smallEtaleTopology B A D ⟶
      ((toProEt X).sheafPushforwardContinuous (Type (u + 1))
        X.smallEtaleTopology (ProEt.topology X)).obj
          (derivedComparisonIsoTarget X B A D) |>.obj where
  app V := ↾(derivedComparisonIsoUnit X B A D V.unop)
  naturality := by
    intro V W f
    apply ConcreteCategory.hom_ext
    intro a
    exact (derivedComparisonUnits_natural X B A D).2 _ _ f.unop a

/-- The canonical comparison map on derived Hom sheaves: first transpose along sheafification, then
along the comparison adjunction. Its data comes from actual local derived pullback.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable def derivedHomSheafComparison :
    (comparisonSetUpperStar X).obj
      (derivedLocalHomSheaf X.smallEtaleTopology B A D) ⟶
        derivedComparisonHomTarget X B A D :=
  ((proEtaleSiteComparison X).homEquiv _ _).symm
    (((sheafificationAdjunction X.smallEtaleTopology (Type (u + 1))).homEquiv _ _).symm
      (derivedComparisonHomPresheafMap X B A D))

/-- The analogous canonical comparison map on derived Isom sheaves, using actual isomorphisms.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable def derivedIsoSheafComparison :
    (comparisonSetUpperStar X).obj
      (derivedLocalIsoSheaf X.smallEtaleTopology B A D) ⟶
        derivedComparisonIsoTarget X B A D :=
  ((proEtaleSiteComparison X).homEquiv _ _).symm
    (((sheafificationAdjunction X.smallEtaleTopology (Type (u + 1))).homEquiv _ _).symm
      (derivedComparisonIsoPresheafMap X B A D))

/-- The pro-etale sheafification unit on the local derived Hom presheaf at the specified object.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable abbrev proEtaleDerivedHomUnit (U : X.ProEt) :=
  (toSheafify (ProEt.topology X) (derivedLocalHomPresheaf (ProEt.topology X) B
    ((derivedComparison X B).obj A) ((derivedComparison X B).obj D))).app (op U)

/-- The pro-etale sheafification unit on the local derived Isom presheaf at the specified object.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable abbrev proEtaleDerivedIsoUnit (U : X.ProEt) :=
  (toSheafify (ProEt.topology X) (derivedLocalIsoPresheaf (ProEt.topology X) B
    ((derivedComparison X B).obj A) ((derivedComparison X B).obj D))).app (op U)

set_option backward.isDefEq.respectTransparency false in
private theorem splitFiniteCover (U : X.ProEt) [IsAffine U.left]
    (hU : (ProEt.topology X).IsWeaklyContractible.{u + 1} U)
    (S : Sieve U) (hS : S ∈ ProEt.topology X U) :
    ∃ (I : Type (u + 1)) (_ : Finite I) (W : I → X.ProEt) (c : Cofan W),
      Nonempty (IsColimit c) ∧
      (∀ H : Sheaf (ProEt.topology X) (Type (u + 1)),
        Function.Bijective (fun t : H.obj.obj (op c.pt) ↦
          fun i ↦ H.obj.map (c.inj i).op t)) ∧
      ∃ (p : c.pt ⟶ U) (σ : U ⟶ c.pt), σ ≫ p = 𝟙 U ∧ ∀ i, S (c.inj i ≫ p) := by
  classical
  let J := ProEt.topology X
  obtain ⟨T, hT, hTS⟩ := ProEt.mem_topology_iff.1 hS
  obtain ⟨𝒰, _, h𝒰⟩ := (mem_propQCPrecoverage_iff_exists_quasiCompactCover
    (P := @WeaklyEtale)).1 (ProEt.mem_precoverage_iff.1 hT)
  have hmem (i : 𝒰.I₀) :
      T.map (ProEt.forget X ⋙ Over.forget X) (𝒰.f i) := by
    rw [h𝒰]
    exact ⟨i⟩
  choose Z hZ a ha hZa using fun i ↦ Presieve.map_iff.1 (hmem i)
  obtain ⟨𝒱, r, hfin, _⟩ := QuasiCompactCover.exists_hom.{u + 1, u} 𝒰
  let I := 𝒱.I₀
  let := hfin
  have (i : I) : WeaklyEtale (𝒱.f i) := 𝒱.map_prop i
  let W : I → X.ProEt := fun i ↦ ProEt.mk (𝒱.f i ≫ U.hom)
  let f : ∀ i, W i ⟶ U := fun i ↦ MorphismProperty.Over.homMk (𝒱.f i)
  have hf (i : I) : S (f i) := by
    have ha' (j : 𝒰.I₀) : (a j).left = eqToHom (hZ j) ≫ 𝒰.f j := hZa j
    let d : (W i).left ⟶ (Z (r.s₀ i)).left := r.h₀ i ≫ eqToHom (hZ _).symm
    have hd : d ≫ (a (r.s₀ i)).left = (f i).left := by
      dsimp only [d]
      rw [ha', Category.assoc, eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp, r.w₀]
      rfl
    have heq : f i = MorphismProperty.Over.homMk d (by
        rw [← MorphismProperty.Over.w (a (r.s₀ i)), ← Category.assoc, hd]
        exact MorphismProperty.Over.w (f i)) ≫ a (r.s₀ i) :=
      MorphismProperty.Over.Hom.ext hd.symm
    rw [heq]
    exact S.downward_closed (hTS _ _ (ha _)) _
  have hcov : Sieve.ofArrows W f ∈ J U := by
    apply Precoverage.generate_mem_toGrothendieck
    change (Presieve.ofArrows W f).map (ProEt.forget X ⋙ Over.forget X) ∈
      proetalePrecoverage U.left
    rw [Presieve.map_ofArrows]
    change 𝒱.cover.presieve₀ ∈ proetalePrecoverage U.left
    exact ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.mpr inferInstance, 𝒱.cover.mem₀⟩
  have hqc (i : I) : CompactSpace (W i).left := by
    exact inferInstanceAs (CompactSpace (Spec _))
  have hqs (i : I) : QuasiSeparatedSpace (W i).left := by
    exact inferInstanceAs (QuasiSeparatedSpace (Spec _))
  obtain ⟨V, ι, e, hι, _, _, _, ⟨hr⟩, _, hsec, _, _⟩ :=
    ProEt.finite_coproduct_evaluation.{u, u + 1, u + 1} X I W hqc hqs
  let c : Cofan W := Cofan.mk V ι
  let yon := J.uliftYoneda.{u + 1}
  have hc : IsColimit c := isColimitOfReflects yon
    ((Cofan.isColimitMapCoconeEquiv yon W c).symm hr)
  let p : V ⟶ U := Cofan.IsColimit.desc hc f
  have hfac (i : I) : ι i ≫ p = f i := Cofan.IsColimit.fac hc f i
  have hp : Epi (yon.map p) := by
    constructor
    intro H g h hgh
    apply J.uliftYonedaEquiv.injective
    have hH := (isSheaf_iff_isSheaf_of_type J H.obj).mp H.property
    apply (hH.isSeparated _ hcov).ext
    rintro Z k ⟨T, a, _, ⟨i⟩, rfl⟩
    rw [op_comp, Functor.map_comp, types_comp_apply, types_comp_apply]
    congr 1
    rw [J.uliftYonedaEquiv_naturality, J.uliftYonedaEquiv_naturality]
    congr 1
    have heq := congrArg (fun q ↦ yon.map (ι i) ≫ q) hgh
    simpa only [← Category.assoc, ← Functor.map_comp, hfac] using heq
  obtain ⟨s, hs⟩ := hU (yon.map p)
    ((Sheaf.isLocallySurjective_iff_epi' (Type (u + 1)) _).mpr hp) (ULift.up (𝟙 U))
  let σ : U ⟶ V := s.down
  have hσ : σ ≫ p = 𝟙 U := congrArg ULift.down hs
  refine ⟨I, hfin, W, c, ⟨hc⟩, hsec, p, σ, hσ, ?_⟩
  intro i
  change S (ι i ≫ p)
  rw [hfac]
  exact hf i

private theorem isoFiniteProductsOfHom
    (I : Type (u + 1)) (W : I → X.ProEt) (c : Cofan W)
    (hHom : ∀ A D : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} B)),
      Function.Bijective (fun f : (derivedSliceRestriction (ProEt.topology X) B c.pt).obj A ⟶
        (derivedSliceRestriction (ProEt.topology X) B c.pt).obj D ↦
        fun i ↦ derivedLocalHomRestriction (ProEt.topology X) B A D (c.inj i) f))
    (A' D' : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} B))) :
    Function.Bijective (fun f :
      (derivedLocalIsoPresheaf (ProEt.topology X) B A' D').obj (op c.pt) ↦
        fun i ↦ derivedLocalIsoRestriction (ProEt.topology X) B A' D' (c.inj i) f) := by
  have hid (A) (i : I) :
      derivedLocalHomRestriction (ProEt.topology X) B A A (c.inj i) (𝟙 _) = 𝟙 _ := by
    dsimp only [derivedLocalHomRestriction]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app]
  have hcomp (A D G) (i : I)
      (a : (derivedSliceRestriction (ProEt.topology X) B c.pt).obj A ⟶
        (derivedSliceRestriction (ProEt.topology X) B c.pt).obj D)
      (b : (derivedSliceRestriction (ProEt.topology X) B c.pt).obj D ⟶
        (derivedSliceRestriction (ProEt.topology X) B c.pt).obj G) :
      derivedLocalHomRestriction (ProEt.topology X) B A G (c.inj i) (a ≫ b) =
        derivedLocalHomRestriction (ProEt.topology X) B A D (c.inj i) a ≫
          derivedLocalHomRestriction (ProEt.topology X) B D G (c.inj i) b := by
    simp only [derivedLocalHomRestriction, Functor.map_comp, Category.assoc,
      Iso.hom_inv_id_app_assoc]
  constructor
  · intro f g hfg
    apply Iso.ext
    apply (hHom A' D').1
    funext i
    exact congrArg Iso.hom (congrFun hfg i)
  · intro f
    obtain ⟨a, ha⟩ := (hHom A' D').2 (fun i ↦ (f i).hom)
    obtain ⟨b, hb⟩ := (hHom D' A').2 (fun i ↦ (f i).inv)
    dsimp only at ha hb
    have hab : a ≫ b = 𝟙 _ := by
      apply (hHom A' A').1
      funext i
      change derivedLocalHomRestriction _ _ _ _ _ (a ≫ b) =
        derivedLocalHomRestriction _ _ _ _ _ (𝟙 _)
      rw [hcomp, hid, congrFun ha i, congrFun hb i, (f i).hom_inv_id]
    have hba : b ≫ a = 𝟙 _ := by
      apply (hHom D' D').1
      funext i
      change derivedLocalHomRestriction _ _ _ _ _ (b ≫ a) =
        derivedLocalHomRestriction _ _ _ _ _ (𝟙 _)
      rw [hcomp, hid, congrFun hb i, congrFun ha i, (f i).inv_hom_id]
    refine ⟨⟨a, b, hab, hba⟩, ?_⟩
    funext i
    apply Iso.ext
    exact congrFun ha i

private theorem bijectiveUnitOfFiniteProducts
    (P : X.ProEtᵒᵖ ⥤ Type (u + 1))
    (hprod : ∀ (I : Type (u + 1)) [Finite I] (W : I → X.ProEt) (c : Cofan W),
      IsColimit c →
      (∀ H : Sheaf (ProEt.topology X) (Type (u + 1)),
        Function.Bijective (fun t : H.obj.obj (op c.pt) ↦
          fun i ↦ H.obj.map (c.inj i).op t)) →
      Function.Bijective (fun t : P.obj (op c.pt) ↦ fun i ↦ P.map (c.inj i).op t))
    (U : X.ProEt) [IsAffine U.left]
    (hU : (ProEt.topology X).IsWeaklyContractible.{u + 1} U) :
    Function.Bijective ((toSheafify (ProEt.topology X) P).app (op U)) := by
  classical
  let J := ProEt.topology X
  let η := toSheafify J P
  constructor
  · intro x y hxy
    obtain ⟨I, hI, W, c, ⟨hc⟩, hsec, p, σ, hσ, hf⟩ :=
      splitFiniteCover X U hU _ (Presheaf.equalizerSieve_mem J η x y hxy)
    have heq : P.map p.op x = P.map p.op y := by
      apply (hprod I W c hc hsec).1
      funext i
      have hi : P.map (c.inj i ≫ p).op x = P.map (c.inj i ≫ p).op y := hf i
      simpa only [op_comp, Functor.map_comp, types_comp_apply] using hi
    have heq' := congrArg (fun t ↦ P.map σ.op t) heq
    simpa only [← types_comp_apply, ← Functor.map_comp, ← op_comp, hσ, op_id,
      CategoryTheory.Functor.map_id, types_id_apply] using heq'
  · intro t
    obtain ⟨I, hI, W, c, ⟨hc⟩, hsec, p, σ, hσ, hf⟩ :=
      splitFiniteCover X U hU _ (Presheaf.imageSieve_mem J η t)
    choose x hx using hf
    obtain ⟨s, hs⟩ := (hprod I W c hc hsec).2 x
    have heq : η.app (op c.pt) s = (sheafify J P).map p.op t := by
      apply (hsec ((presheafToSheaf J _).obj P)).1
      funext i
      change (sheafify J P).map (c.inj i).op (η.app (op c.pt) s) =
        (sheafify J P).map (c.inj i).op ((sheafify J P).map p.op t)
      have hs' : P.map (c.inj i).op s = x i := congrFun hs i
      rw [← NatTrans.naturality_apply, hs', hx i]
      simp only [op_comp, Functor.map_comp, types_comp_apply]
    refine ⟨P.map σ.op s, ?_⟩
    rw [NatTrans.naturality_apply, heq]
    change (sheafify J P).map σ.op ((sheafify J P).map p.op t) = t
    simp only [← types_comp_apply, ← Functor.map_comp, ← op_comp, hσ, op_id,
      CategoryTheory.Functor.map_id, types_id_apply]

/-- The pro-etale sheafification units for these two presheaves are bijective on affine weakly
contractible objects.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison)

Proof: Restriction identifies module sheaves on a finite disjoint union of site objects with the
product of the module-sheaf categories of its components. This is an exact equivalence, and
hence gives the corresponding equivalence of derived categories. Thus both actual local derived
Hom and Isom presheaves send finite disjoint unions to products, including the empty union,
whose localized category is the zero category. Stacks Tag 0F63 now says their sheafification
units are bijective on an affine weakly contractible object. The hypothesis here is the
topos-theoretic weak contractibility used in that tag, not merely a property of the underlying
topological space. -/
theorem proEtaleDerivedUnits_bijective (U : X.ProEt) [IsAffine U.left]
    (hU : (ProEt.topology X).IsWeaklyContractible.{u + 1} U) :
    Function.Bijective (proEtaleDerivedHomUnit X B A D U) ∧
      Function.Bijective (proEtaleDerivedIsoUnit X B A D U) := by
  constructor
  · apply bijectiveUnitOfFiniteProducts X _ _ U hU
    intro I hI W c hc hsec
    exact proEtaleDerivedHom_finiteProducts X B I W c hc hsec _ _
  · apply bijectiveUnitOfFiniteProducts X _ _ U hU
    intro I hI W c hc hsec
    exact isoFiniteProductsOfHom X B I W c
      (proEtaleDerivedHom_finiteProducts X B I W c hc hsec) _ _

/-- The canonical evaluation map: the comparison map followed by the unique inverse of the bijective
pro-etale sheafification unit. Only the proof of bijectivity is postponed.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable def derivedHomEvaluation (U : X.ProEt) [IsAffine U.left]
    (hU : (ProEt.topology X).IsWeaklyContractible.{u + 1} U)
    (s : ((comparisonSetUpperStar X).obj
      (derivedLocalHomSheaf X.smallEtaleTopology B A D)).obj.obj (op U)) :
    (derivedSliceRestriction (ProEt.topology X) B U).obj ((derivedComparison X B).obj A) ⟶
      (derivedSliceRestriction (ProEt.topology X) B U).obj ((derivedComparison X B).obj D) :=
  (Equiv.ofBijective (proEtaleDerivedHomUnit X B A D U)
    (proEtaleDerivedUnits_bijective X B A D U hU).1).symm
      ((derivedHomSheafComparison X B A D).hom.app (op U) s)

/-- The same canonical evaluation construction on actual derived isomorphisms.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable def derivedIsoEvaluation (U : X.ProEt) [IsAffine U.left]
    (hU : (ProEt.topology X).IsWeaklyContractible.{u + 1} U)
    (s : ((comparisonSetUpperStar X).obj
      (derivedLocalIsoSheaf X.smallEtaleTopology B A D)).obj.obj (op U)) :
    (derivedSliceRestriction (ProEt.topology X) B U).obj ((derivedComparison X B).obj A) ≅
      (derivedSliceRestriction (ProEt.topology X) B U).obj ((derivedComparison X B).obj D) :=
  (Equiv.ofBijective (proEtaleDerivedIsoUnit X B A D U)
    (proEtaleDerivedUnits_bijective X B A D U hU).2).symm
      ((derivedIsoSheafComparison X B A D).hom.app (op U) s)

variable {B' : Type (u + 1)} [CommRing B']

/-- The canonical map commuting scalar restriction with comparison inverse image, obtained by
transposing the restriction of the comparison adjunction unit.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable def comparisonRestrictScalarsMap (φ : B →+* B')
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B')) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).obj
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj M) ⟶
      (Sheaf.restrictScalars (ProEt.topology X) φ).obj
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B') X).obj M) :=
  ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) X).homEquiv _ _).symm
    ((Sheaf.restrictScalars X.smallEtaleTopology φ).map
      ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B') X).unit.app M))

/-- The specified scalar-restriction comparison is invertible and natural.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison)

Proof: Restriction of scalars is computed on the same underlying sheaf with its scalar action
forgotten along the given ring map. Comparison inverse image is the inverse image on the
underlying sheaves with its induced scalar action. These operations commute. On sheafified
presheaves their canonical comparison is the identity before sheafification and is therefore
invertible; transposing the restricted adjunction unit gives exactly this comparison. Naturality
follows from naturality of that unit and naturality of the adjunction hom equivalence. -/
theorem comparisonRestrictScalarsMap_properties (φ : B →+* B') :
    (∀ M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B'),
      IsIso (comparisonRestrictScalarsMap X B φ M)) ∧
    (∀ (M N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B')) (f : M ⟶ N),
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).map
          ((Sheaf.restrictScalars X.smallEtaleTopology φ).map f) ≫
        comparisonRestrictScalarsMap X B φ N =
      comparisonRestrictScalarsMap X B φ M ≫
        (Sheaf.restrictScalars (ProEt.topology X) φ).map
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B') X).map f)) := by
  let adj₁ := (Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).comp
    (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) X)
  let adj₂ := (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B') X).comp
    (Sheaf.restrictCoextendScalarsAdj (ProEt.topology X) φ)
  let e := Adjunction.leftAdjointUniq adj₁ adj₂
  have he (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B')) :
      e.hom.app M = comparisonRestrictScalarsMap X B φ M := by
    apply (adj₁.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    change adj₂.unit.app M =
      (Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).homEquiv _ _
        ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) X).homEquiv _ _
          (comparisonRestrictScalarsMap X B φ M))
    rw [comparisonRestrictScalarsMap, Equiv.apply_symm_apply,
      Adjunction.homEquiv_unit]
    dsimp only [adj₂]
    rw [Adjunction.comp_unit_app]
    exact (Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).unit.naturality
      ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B') X).unit.app M)
  constructor
  · intro M
    rw [← he M]
    infer_instance
  · intro M N f
    simpa only [he, Functor.comp_map] using e.hom.naturality f

/-- The canonical scalar-restriction comparison isomorphism on module sheaves.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable def comparisonRestrictScalarsSheafIso (φ : B →+* B') :
    Sheaf.restrictScalars X.smallEtaleTopology φ ⋙
      ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X ≅
    ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B') X ⋙
      Sheaf.restrictScalars (ProEt.topology X) φ :=
  NatIso.ofComponents (fun M ↦
    @asIso _ _ _ _ (comparisonRestrictScalarsMap X B φ M)
      ((comparisonRestrictScalarsMap_properties X B φ).1 M))
    ((comparisonRestrictScalarsMap_properties X B φ).2 _ _)

/-- The canonical scalar-restriction comparison induced on derived categories.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable def comparisonRestrictScalarsIso (φ : B →+* B') :
    Sheaf.derivedRestrictScalars X.smallEtaleTopology φ ⋙ derivedComparison X B ≅
      derivedComparison X B' ⋙ Sheaf.derivedRestrictScalars (ProEt.topology X) φ :=
  (Functor.mapDerivedCategoryCompIso _ _) ≪≫
    Functor.mapDerivedCategoryNatIso (comparisonRestrictScalarsSheafIso X B φ) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm

end AlgebraicGeometry.Scheme
