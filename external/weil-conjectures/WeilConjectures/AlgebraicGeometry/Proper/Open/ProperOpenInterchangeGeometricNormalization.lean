/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenComparison
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenIdentificationNormalization
import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenDerivedUnitNormalization
import WeilConjectures.AlgebraicGeometry.Derived.DerivedExtensionZeroBaseChangeSupplement
import WeilConjectures.SixFunctors.BaseChange.Pasting
import WeilConjectures.AlgebraicGeometry.ProperSupportSheafComposition
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionCalculus
import WeilConjectures.AlgebraicGeometry.EtaleSectionProperSupport
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import Mathlib.CategoryTheory.Sites.Subsheaf
import WeilConjectures.AlgebraicGeometry.EtaleModuleSectionClosedSupport
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.EtaleCohomology.EtaleSectionZeroOpen
import WeilConjectures.AlgebraicGeometry.EtaleSectionsEqualOpenEtaleCriterion
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionLocality
import WeilConjectures.AlgebraicGeometry.ClosedProperSupportLocality
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import WeilConjectures.AlgebraicGeometry.Morphisms.FpqcDescent
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.ProperMorphismFpqcDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.FieldExtensionDescent
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage
import WeilConjectures.AlgebraicGeometry.ProperSupportCompositeRange
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionImage
import WeilConjectures.AlgebraicGeometry.OpenExtensionProperSupportRange
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.AlgebraicGeometry.ProperSupportExchangeRange
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SecSmoothPurity.ProperSupportFibreRestrictionCompatibility
import WeilConjectures.SecSmoothPurity.ProperSupportPullbackSectionMap
import WeilConjectures.AlgebraicGeometry.ProperSupportGeometricStalk
import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Compactification.Defs
import WeilConjectures.SixFunctors.OpenClosed.Complex
import WeilConjectures.AlgebraicGeometry.ProperGeometricPointExchange
import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.ProperStrictLocalFibreSections
import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero
import WeilConjectures.AlgebraicGeometry.EtaleSectionsBaseFieldExtension
import WeilConjectures.AlgebraicGeometry.EtaleModuleSetPullbackComparison
import WeilConjectures.AlgebraicGeometry.QcqsGeometricExchangeFactorization
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointedMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationComparison
import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.AlgebraicGeometry.EtalePointedMapRigidity
import WeilConjectures.AlgebraicGeometry.StrictHenselizationMapExists
import WeilConjectures.AlgebraicGeometry.QcqsStrictLocalModuleComparison
import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeRepresentative
import WeilConjectures.AlgebraicGeometry.EtaleUnitSectionRestriction
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization
import WeilConjectures.AlgebraicGeometry.SmallStrictLocalSectionMaps
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointPullbackStalk
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointCanonicalGerm
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.AlgebraicGeometry.ProperSupportGeometricStalkCore
import WeilConjectures.Compactification.BaseChange
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.CategoryTheory.RightDerivedPlusCube

/-!
# Refinement and base change for normalized proper/open interchange

## References

* Stacks Project, More on Etale Cohomology, Tags 0F7B, 0F7C, 0F7D and 0F7F
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.unusedVariables false

private theorem adjoint_eq_of_unit
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (a : L ⊣ R) {K Z : C} {N : D} (η : K ⟶ Z) [Mono η]
    (θ : R.obj N ≅ K) (t : R.obj N ⟶ Z) (ht : θ.hom ≫ η = t)
    (g : L.obj K ⟶ N) (hn : a.unit.app K ≫ R.map g ≫ t = η) :
    g = L.map θ.inv ≫ a.counit.app N := by
  have he : a.unit.app K ≫ R.map g = θ.inv := by
    apply (cancel_mono θ.hom).1
    apply (cancel_mono η).1
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [ht]
    exact hn
  apply (a.homEquiv _ _).injective
  change a.unit.app K ≫ R.map g = _
  rw [he]
  exact ((a.homEquiv _ _).apply_symm_apply θ.inv).symm

private theorem derivedBaseChange_eq
    (Λ : Type (u + 1)) [CommRing Λ] {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g) :
    derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq =
      Functor.rightDerivedFunctorPlusBaseChange (baseChangeMap (ModuleCat.{u + 1} Λ) sq) := by
  rfl

private theorem derivedNatIso_symm
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    Functor.mapDerivedCategoryPlusNatIso e.symm =
      (Functor.mapDerivedCategoryPlusNatIso e).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply DerivedCategory.Plus.ι.map_injective
  simp only [ObjectProperty.ι_obj, Functor.mapDerivedCategoryPlusNatIso,
    Functor.mapDerivedCategoryPlusCompatibility, Functor.mapDerivedCategoryNatIso,
    Localization.liftNatIso, NatIso.mapHomologicalComplex, Iso.symm_hom, Iso.symm_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv, Iso.refl_symm, Iso.refl_trans,
    Functor.fullyFaithfulCancelRight_hom_app, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Iso.refl_hom, NatTrans.comp_app, Functor.comp_obj, Functor.whiskerLeft_app, NatTrans.id_app,
    ObjectProperty.ι_map, Functor.fullyFaithfulCancelRight_inv_app, Iso.trans_inv,
    Iso.refl_inv, Functor.isoWhiskerLeft_inv, Category.id_comp]
  congr 2
  exact Category.comp_id _

private theorem support_mono
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
    (k : X ⟶ Y) [IsOpenImmersion k]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Mono ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F) := by
  obtain ⟨L, ι, hi, _, ho, _⟩ := properSupportSheafComposition Λ
  have hι : Mono ((ι k).app F) := by
    refine ⟨fun {Z} a b hab ↦ ?_⟩
    ext V s
    apply (hi X Y k F V.unop).1
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (congrArg (fun z ↦ z.hom) hab) V) s
  obtain ⟨o, he⟩ := ho X Y k
  have he' := congr_app he F
  dsimp only [NatTrans.comp_app] at he'
  rw [← he']
  infer_instance

private theorem baseChange_comp (A : Type (u + 1)) [CommRing A]
    {X Y Z X' Y' Z' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
    (a : X' ⟶ X) (b : Y' ⟶ Y) (c : Z' ⟶ Z)
    (sqf : CommSq a f' f b) (sqg : CommSq b g' g c)
    (h : X ⟶ Z) (hh : h = f ≫ g) (h' : X' ⟶ Z') (hh' : h' = f' ≫ g')
    (sq : CommSq a h' h c) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (c)^*[ModuleCat.{u + 1} A].map
        ((lowerStarComp (ModuleCat.{u + 1} A) f g h hh).hom.app F) ≫
        (baseChangeMap (ModuleCat.{u + 1} A) sq).app F =
      (baseChangeMap (ModuleCat.{u + 1} A) sqg).app
          ((f)_*[ModuleCat.{u + 1} A].obj F) ≫
        (g')_*[ModuleCat.{u + 1} A].map
          ((baseChangeMap (ModuleCat.{u + 1} A) sqf).app F) ≫
        (lowerStarComp (ModuleCat.{u + 1} A) f' g' h' hh').hom.app
          ((a)^*[ModuleCat.{u + 1} A].obj F) := by
  subst h
  subst h'
  rw [baseChangeMap_paste_vert_app (ModuleCat.{u + 1} A) sqf sqg sq]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

-- The support cube contains eight sheaf functors and both direct-image compositors.
private theorem ordinary_cube (A : Type (u + 1)) [CommRing A]
    (θ : ∀ {U V W Z : Scheme.{u}}
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (_sq : CommSq k r p i),
        (r)_*[ModuleCat.{u + 1} A] ⋙ (i)_!open[ModuleCat.{u + 1} A] ≅
          (k)_!open[ModuleCat.{u + 1} A] ⋙ (p)_*[ModuleCat.{u + 1} A])
    (hθ : (∀ {U V W Z : Scheme.{u}}
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (sq : CommSq k r p i)
        (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)),
        (θ k r p i sq).hom.app F ≫
            (p)_*[ModuleCat.{u + 1} A].map
              ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F) ≫
            (lowerStarComp (ModuleCat.{u + 1} A) k p).hom.app F =
          (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).app
              ((r)_*[ModuleCat.{u + 1} A].obj F) ≫
            (lowerStarComp (ModuleCat.{u + 1} A) r i (k ≫ p) sq.w).hom.app F))
    {U V W Z U₁ V₁ W₁ Z₁ : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (k₁ : U₁ ⟶ V₁) (r₁ : U₁ ⟶ W₁) (p₁ : V₁ ⟶ Z₁) (i₁ : W₁ ⟶ Z₁)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    [IsOpenImmersion k₁] [IsOpenImmersion i₁] [IsProper r₁] [IsProper p₁]
    (sq : CommSq k r p i) (sq₁ : CommSq k₁ r₁ p₁ i₁)
    (a : V₁ ⟶ V) (b : Z₁ ⟶ Z) (c : W₁ ⟶ W) (d : U₁ ⟶ U)
    (sp : IsPullback a p₁ p b) (sr : IsPullback d r₁ r c)
    (si : IsPullback c i₁ i b) (sk : IsPullback d k₁ k a)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (b)^*[ModuleCat.{u + 1} A].map ((θ k r p i sq).hom.app F) ≫
        (baseChangeMap (ModuleCat.{u + 1} A) sp.toCommSq).app
          ((k)_!open[ModuleCat.{u + 1} A].obj F) ≫
        (p₁)_*[ModuleCat.{u + 1} A].map
          ((@asIso _ _ _ _ _
            (isIso_openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} A) sk)).inv.app F) =
      (@asIso _ _ _ _ _
          (isIso_openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} A) si)).inv.app
            ((r)_*[ModuleCat.{u + 1} A].obj F) ≫
        (i₁)_!open[ModuleCat.{u + 1} A].map
          ((baseChangeMap (ModuleCat.{u + 1} A) sr.toCommSq).app F) ≫
        (θ k₁ r₁ p₁ i₁ sq₁).hom.app ((d)^*[ModuleCat.{u + 1} A].obj F) := by
  let bk := @asIso _ _ _ _ _
    (isIso_openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} A) sk)
  let bi := @asIso _ _ _ _ _
    (isIso_openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} A) si)
  have hk M : bk.inv.app M ≫
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k₁).app
        ((d)^*[ModuleCat.{u + 1} A].obj M) =
      (a)^*[ModuleCat.{u + 1} A].map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app M) ≫
        (baseChangeMap (ModuleCat.{u + 1} A) sk.toCommSq).app M := by
    apply (cancel_epi (bk.hom.app M)).mp
    simp only [Iso.hom_inv_id_app_assoc]
    exact (openImmersionLowerShriekBaseChangeMap_comp_baseChangeMap_app
      (ModuleCat.{u + 1} A) sk.toCommSq M).symm
  have hi M : bi.inv.app M ≫
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i₁).app
        ((c)^*[ModuleCat.{u + 1} A].obj M) =
      (b)^*[ModuleCat.{u + 1} A].map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).app M) ≫
        (baseChangeMap (ModuleCat.{u + 1} A) si.toCommSq).app M := by
    apply (cancel_epi (bi.hom.app M)).mp
    simp only [Iso.hom_inv_id_app_assoc]
    exact (openImmersionLowerShriekBaseChangeMap_comp_baseChangeMap_app
      (ModuleCat.{u + 1} A) si.toCommSq M).symm
  have := support_mono A k₁ ((d)^*[ModuleCat.{u + 1} A].obj F)
  apply (cancel_mono ((p₁)_*[ModuleCat.{u + 1} A].map
    ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k₁).app
      ((d)^*[ModuleCat.{u + 1} A].obj F)) ≫
      (lowerStarComp (ModuleCat.{u + 1} A) k₁ p₁).hom.app
        ((d)^*[ModuleCat.{u + 1} A].obj F))).mp
  simp only [Category.assoc]
  rw [← (p₁)_*[ModuleCat.{u + 1} A].map_comp_assoc, hk]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  have hn := (baseChangeMap (ModuleCat.{u + 1} A) sp.toCommSq).naturality
    ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F)
  simp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  have s : CommSq d (k₁ ≫ p₁) (k ≫ p) b := ⟨by
    rw [← Category.assoc, sk.w, Category.assoc, sp.w, Category.assoc]⟩
  rw [← baseChange_comp A k p k₁ p₁ d a b sk.toCommSq sp.toCommSq
    (k ≫ p) rfl (k₁ ≫ p₁) rfl s F]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  simp only [Category.assoc]
  rw [hθ]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [baseChange_comp A r i r₁ i₁ d c b sr.toCommSq si.toCommSq
    (k ≫ p) sq.w (k₁ ≫ p₁) sq₁.w s F]
  rw [← reassoc_of% hi]
  rw [← reassoc_of% (openImmersionLowerShriekToLowerStar
    (ModuleCat.{u + 1} A) i₁).naturality
      ((baseChangeMap (ModuleCat.{u + 1} A) sr.toCommSq).app F)]
  rw [hθ k₁ r₁ p₁ i₁ sq₁]

/-- Refinement and base change for normalized proper/open interchange.
The ordinary and derived isomorphisms are supplied. The derived map is the
canonical rightDerivedFunctorPlusBaseChange of the ordinary map;
this theorem asserts only the indicated equalities for those fixed isomorphisms.
-/
theorem properOpenInterchangeGeometricNormalization_of_normalization (Λ : Type (u + 1)) [CommRing
  Λ] [Finite Λ]
    (δ : ∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion
        k] [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i), (lowerStar
        (ModuleCat.{u + 1} Λ) r) ⋙ (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i) ≅
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k) ⋙ (lowerStar (ModuleCat.{u + 1} Λ) p))
      (γ : ∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion
        k] [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i),
        ((lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlus) ⋙ (openImmersionLowerShriek
        (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus ≅ (openImmersionLowerShriek (ModuleCat.{u +
        1} Λ) k).mapDerivedCategoryPlus ⋙ ((lowerStar (ModuleCat.{u + 1} Λ)
          p).rightDerivedFunctorPlus))
    (hδ : (∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D)
      [IsOpenImmersion k]
        [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i), ∀ (F : (Sheaf
        A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (δ k i r p h).hom.app F ≫ (lowerStar (ModuleCat.{u + 1} Λ) p).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) k p).hom.app F =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) i).app ((lowerStar (ModuleCat.{u +
        1} Λ) r).obj F) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) r i (k ≫ p) h).hom.app F))
    (hγ : ∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D)
      (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion k] [IsOpenImmersion i]
      [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i),
      (γ k i r p h).hom = Functor.rightDerivedFunctorPlusBaseChange (δ k i r p h).hom) :
    (∀ {T₁ T₂ X : Scheme.{u}} (p : T₁ ⟶ T₂) [IsProper p]
      (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
      (h : j₁ ≫ p = j₂) (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
        Λ))),
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₂).mapDerivedCategoryPlus.map
        ((lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).inv.app K) ≫
        (γ j₁ j₂ (𝟙 X) p (h.trans (Category.id_comp j₂).symm)).hom.app K =
      properOpenComparison Λ p j₁ j₂ h K) ∧
    (∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion k]
        [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i), ∀ {A₁ B₁ C₁ D₁ :
        Scheme.{u}}
      (a : B₁ ⟶ B) (b : D₁ ⟶ D) (c : C₁ ⟶ C) (d : A₁ ⟶ A)
      (k₁ : A₁ ⟶ B₁) (i₁ : C₁ ⟶ D₁) (r₁ : A₁ ⟶ C₁) (p₁ : B₁ ⟶ D₁)
      [IsOpenImmersion k₁] [IsOpenImmersion i₁] [IsProper r₁] [IsProper p₁]
      (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
      (sk : IsPullback d k₁ k a) (si : IsPullback c i₁ i b)
      (sr : IsPullback d r₁ r c) (sp : IsPullback a p₁ p b)
      (K : DerivedCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (upperStar (ModuleCat.{u + 1} Λ) b).mapDerivedCategoryPlus.map ((γ k i r p h).hom.app K) ≫
        (derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sp.toCommSq).app ((openImmersionLowerShriek
        (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus.obj K) ≫
        ((lowerStar (ModuleCat.{u + 1} Λ) p₁).rightDerivedFunctorPlus).map
        ((extensionZeroBaseChangeDerivedPlusIso Λ sk).hom.app K) =
      (extensionZeroBaseChangeDerivedPlusIso Λ si).hom.app (((lowerStar (ModuleCat.{u + 1} Λ)
        r).rightDerivedFunctorPlus).obj K) ≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i₁).mapDerivedCategoryPlus.map
        ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sr.toCommSq).app K) ≫
        (γ k₁ i₁ r₁ p₁ h₁).hom.app ((upperStar (ModuleCat.{u + 1} Λ) d).mapDerivedCategoryPlus.obj
        K)) := by
  constructor
  · intro T₁ T₂ X p _ j₁ j₂ _ _ h K
    rw [hγ]
    let M := ModuleCat.{u + 1} Λ
    let a₁ := derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus M j₁
    let a₂ := derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus M j₂
    let g := (openImmersionLowerShriek M j₂).mapDerivedCategoryPlus.map
        ((lowerStarIdDerivedPlus M X).inv.app K) ≫
      (Functor.rightDerivedFunctorPlusBaseChange
        (δ j₁ j₂ (𝟙 X) p (h.trans (Category.id_comp j₂).symm)).hom).app K
    have hn := properOpenDerivedUnitNormalization Λ p j₁ j₂ h
      (δ j₁ j₂ (𝟙 X) p (h.trans (Category.id_comp j₂).symm)).hom
      (hδ j₁ j₂ (𝟙 X) p (h.trans (Category.id_comp j₂).symm)) K
    have hf := a₁.fullyFaithfulLOfCompIsoId
      ((Functor.mapDerivedCategoryPlusCompIso
        (openImmersionLowerShriek M j₁) (upperStar M j₁)).symm ≪≫
        Functor.mapDerivedCategoryPlusNatIso
          (asIso (openImmersionLowerShriekUpperStarAdjunction M j₁).unit).symm ≪≫
        Functor.mapDerivedCategoryPlusIdIso _)
    have := hf.full
    have := hf.faithful
    have : IsIso a₁.unit := inferInstance
    exact adjoint_eq_of_unit a₂ (a₁.unit.app K)
      (properOpenIdentification Λ p j₁ j₂ h K) _
      (properOpenIdentification_unit Λ p j₁ j₂ h K) g hn
  · intro A B C D k i r p _ _ _ _ h A₁ B₁ C₁ D₁ a b c d k₁ i₁ r₁ p₁ _ _ _ _
      h₁ sk si sr sp K
    rw [hγ k i r p h, hγ k₁ i₁ r₁ p₁ h₁]
    let M := ModuleCat.{u + 1} Λ
    let ek := @asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap M sk)
    let ei := @asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap M si)
    have hc := Functor.rightDerivedFunctorPlusBaseChange_cube
      (lowerStar M r) (lowerStar M p) (lowerStar M r₁) (lowerStar M p₁)
      (openImmersionLowerShriek M k) (openImmersionLowerShriek M i)
      (openImmersionLowerShriek M k₁) (openImmersionLowerShriek M i₁)
      (upperStar M d) (upperStar M c) (upperStar M a) (upperStar M b)
      (δ k i r p h).hom (δ k₁ i₁ r₁ p₁ h₁).hom
      (baseChangeMap M sr.toCommSq) (baseChangeMap M sp.toCommSq) ei ek
      (ordinary_cube Λ (fun k r p i _ _ _ _ sq ↦ δ k i r p sq.w)
        (fun k r p i _ _ _ _ sq F ↦ hδ k i r p sq.w F)
        k r p i k₁ r₁ p₁ i₁ ⟨h⟩ ⟨h₁⟩ a b c d sp sr si sk) K
    simpa only [derivedBaseChange_eq, extensionZeroBaseChangeDerivedPlusIso,
      derivedNatIso_symm,
      Iso.trans_inv, Iso.symm_inv, Iso.symm_hom, NatTrans.comp_app,
      Iso.trans_hom, ← Category.assoc, ek, ei, M] using hc

end AlgebraicGeometry.Etale
