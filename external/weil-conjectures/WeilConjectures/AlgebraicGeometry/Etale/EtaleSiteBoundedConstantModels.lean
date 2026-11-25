/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedMapPresheaves
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver

import WeilConjectures.AlgebraicGeometry.SiteBoundedConstantModel
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.SiteBoundedConstantGradedModel
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Abelian
import WeilConjectures.AlgebraicGeometry.SiteFiniteConstantExtensionTower
import WeilConjectures.AlgebraicGeometry.FiniteConstantExtensionTower
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.SiteFiniteConstantConeStep
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import WeilConjectures.AlgebraicGeometry.SiteFiniteLocallyConstantWeakSerre
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.CategoryTheory.ObjectProperty.Extensions
import WeilConjectures.CategoryTheory.Site.SiteModuleSheafConstantRingEquivalenceSupplement
import WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantSerre
import WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantModuleSheaf
import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageSupplement
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.CategoryTheory.FiniteTypeConstantExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import WeilConjectures.CategoryTheory.FiniteTypeRestrictionExact
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.FiniteTypeConstantLocalLinear
import WeilConjectures.CategoryTheory.SiteConstantModuleHomSurjective
import WeilConjectures.Algebra.Homology.SmoothPurity.ConstantLocalModuleHomSupplement
import WeilConjectures.CategoryTheory.SiteConstantModuleFunctor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.CategoryTheory.Site.SiteConstantModuleUnitSupplement
import Mathlib.Algebra.Module.FinitePresentation
import WeilConjectures.CategoryTheory.SiteConstantModuleOverHom
import WeilConjectures.CategoryTheory.FinitePresentationLocalLift
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.CategoryTheory.Sites.ConstantForget
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.CategoryTheory.FiniteTypeExtensionLocalPresentation
import WeilConjectures.CategoryTheory.ConstantFiniteFreeLocalLift
import WeilConjectures.CategoryTheory.FiniteSectionsEpiLift
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.CategoryTheory.Abelian.Exact
import WeilConjectures.CategoryTheory.ExtensionCokernelPresentation
import WeilConjectures.Algebra.Homology.SmoothPurity.LocalModuleIsoSupplement
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.RingTheory.Finiteness.Cardinality
import WeilConjectures.CategoryTheory.FiniteTypeRestrictionMapExact
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.LinearAlgebra.StdBasis
import WeilConjectures.AlgebraicGeometry.BoundedTopMorphisms
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.RingTheory.Finiteness.Basic
import WeilConjectures.AlgebraicGeometry.SiteFiniteConstantComplexDescent
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Homology.Additive
import Mathlib.Data.Int.Interval
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Defs

/-! # Bounded constant models on the mixed-universe small etale site -/

@[expose] public section

universe u
open CategoryTheory Limits AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
private noncomputable def overRestrictionIso
    {X : Scheme.{u}} (B : Type (u + 1)) [CommRing B] (U : X.Etale) :
    X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} B) U ⋙
      (Scheme.Etale.overSheafEquiv U (ModuleCat.{u + 1} B)).functor ≅
        upperStar (ModuleCat.{u + 1} B) U.hom :=
  let R := GrothendieckTopology.localizationRestriction (ModuleCat.{u + 1} B)
    @AlgebraicGeometry.Etale @AlgebraicGeometry.Etale le_rfl U.hom U.prop
  let e : X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} B) U ⋙
      (Scheme.Etale.overSheafEquiv U (ModuleCat.{u + 1} B)).functor ≅ R :=
    ((fullyFaithfulSheafToPresheaf U.left.smallEtaleTopology
      (ModuleCat.{u + 1} B)).whiskeringRight _).preimageIso
        (NatIso.ofComponents
          (fun F ↦ by
            change ((Scheme.Etale.etaleToOver U).op ⋙
              (Over.forget U).op ⋙ F.obj) ≅ _
            exact Functor.isoWhiskerRight
              (NatIso.op (Scheme.Etale.etaleToOverCompForgetIso U).symm) F.obj)
          (by
            intro F G φ
            apply NatTrans.ext
            funext T
            dsimp
            exact (φ.hom.naturality _).symm))
  e ≪≫ (GrothendieckTopology.upperStarIsoLocalizationRestriction
    (ModuleCat.{u + 1} B) @AlgebraicGeometry.Etale @AlgebraicGeometry.Etale
    le_rfl U.hom U.prop).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Local finite cohomology models give bounded finite complex models on an etale cover.

Source: Stacks Project, Tag 094G, proof of lemma-locally-constant; transport of
`CategoryTheory.exists_site_bounded_constant_model` along `AsSmall.equiv`.
(blueprint: lem-weil-pbc-etale-site-bounded-constant-models)

Proof: Replace X.Etale by AsSmall X.Etale. Both its objects and morphisms then lie
in Type (u + 1). Transport the topology along AsSmall.down and use its associated
precoverage, whose covering families are all families generating a covering sieve.
The equivalence transports the terminal etale object and induces exact equivalences
on sheaf categories and their slices. These commute with constant sheaves and
slice restriction. Their derived functors preserve homology and identify the given
bounded object and local cohomology trivializations with ones on this small site.
Apply exists_site_bounded_constant_model there; a finite ring is Noetherian and
finite modules are finitely generated. Transport the resulting constant-complex
models and covering family back through the slice equivalences. Choose an arrow
above each point of X from the resulting jointly surjective family, making the cover
index a type in universe u. This does not change any model or degree bound. Finite
modules over the finite ring have finite underlying sets. On an empty scheme use
the empty cover. Zero complexes and bounds a = b satisfy the same construction. -/
theorem etale_site_bounded_constant_models
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] [Finite B]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (a b : ℤ) (hab : a ≤ b)
    (hvan : ∀ q : ℤ, q < a ∨ b < q → IsZero
      ((DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) q).obj K))
    (hloc : ∀ (q : ℤ) (V : X.Etale),
      ∃ (I : Type (u + 1)) (U : I → X.Etale) (f : ∀ i, U i ⟶ V),
        Sieve.ofArrows U f ∈ X.smallEtaleTopology V ∧
        ∀ i, ∃ M : ModuleCat.{u + 1} B, Module.Finite B M ∧ Nonempty
          (((DerivedCategory.homologyFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) q).obj K).over (U i) ≅
            (constantSheaf (X.smallEtaleTopology.over (U i))
              (ModuleCat.{u + 1} B)).obj M)) :
    ∃ 𝒰 : Cover.{u} etalePrecoverage X, ∀ i : 𝒰.I₀,
      ∃ E : CochainComplex (ModuleCat.{u + 1} B) ℤ,
        (∀ n : ℤ, Finite (E.X n)) ∧
        (∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n)) ∧ Nonempty
          ((upperStar (ModuleCat.{u + 1} B) (𝒰.f i)).mapDerivedCategory.obj K ≅
            DerivedCategory.Q.obj
              (((constantSheaf (𝒰.X i).smallEtaleTopology
                (ModuleCat.{u + 1} B)).mapHomologicalComplex (ComplexShape.up ℤ)).obj E))  := by
  classical
  let e : X.Etale ≌ AsSmall.{u + 1} X.Etale := AsSmall.equiv
  let J := e.inverse.inducedTopology X.smallEtaleTopology
  let S := e.sheafCongr X.smallEtaleTopology J (ModuleCat.{u + 1} B)
  have : S.functor.Additive := Functor.additive_of_preserves_binary_products _
  let K' := S.functor.mapDerivedCategory.obj K
  let T := e.functor.obj (Scheme.Etale.mk (𝟙 X))
  have hT : IsTerminal T := (Scheme.Etale.isTerminalMkId X).isTerminalObj e.functor
  let P := J.toPrecoverage
  have hP : P.toGrothendieck = J := by
    apply le_antisymm J.toGrothendieck_toPrecoverage_le
    intro V R hR
    simpa only [Sieve.generate_sieve] using
      Precoverage.generate_mem_toGrothendieck ((J.arrows_mem_toPrecoverage_iff R).mpr hR)
  have site := exists_site_bounded_constant_model P T hT B
  rw [hP] at site
  have hvan' (q : ℤ) (hq : q < a ∨ b < q) : IsZero
      ((DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{u + 1} B)) q).obj K') :=
    (S.functor.map_isZero (hvan q hq)).of_iso
      ((S.functor.mapDerivedCategoryHomologyFunctorIso q).app K).symm
  have hloc' : ∀ (q : ℤ) (V : AsSmall.{u + 1} X.Etale),
      ∃ (I : Type (u + 1)) (U : I → AsSmall.{u + 1} X.Etale) (f : ∀ i, U i ⟶ V),
        Sieve.ofArrows U f ∈ J V ∧
        ∀ i, ∃ M : ModuleCat.{u + 1} B, Module.Finite B M ∧ Nonempty
          (((DerivedCategory.homologyFunctor
            (Sheaf J (ModuleCat.{u + 1} B)) q).obj K').over (U i) ≅
            (constantSheaf (J.over (U i)) (ModuleCat.{u + 1} B)).obj M) := by
    intro q V
    rcases V with ⟨V⟩
    obtain ⟨I, U, f, hf, hM⟩ := hloc q V
    refine ⟨I, fun i ↦ e.functor.obj (U i), fun i ↦ e.functor.map (f i), ?_, ?_⟩
    · rw [← Sieve.functorPushforward_ofArrows]
      exact (e.functor.functorPushforward_mem_iff X.smallEtaleTopology J).mpr hf
    · intro i
      obtain ⟨M, hM, ⟨hi⟩⟩ := hM i
      let ei := Over.postEquiv (X := U i) e
      have : ei.functor.IsCocontinuous (X.smallEtaleTopology.over (U i))
          (J.over (e.functor.obj (U i))) := by
        change (Over.post (X := U i) e.functor).IsCocontinuous _ _
        infer_instance
      have : ei.inverse.IsCocontinuous (J.over (e.functor.obj (U i)))
          (X.smallEtaleTopology.over (U i)) := by
        change (Over.post (X := e.functor.obj (U i)) e.inverse ⋙
          Over.map (e.unitIso.inv.app (U i))).IsCocontinuous _ _
        have : (Over.map (e.unitIso.inv.app (U i))).IsCocontinuous
            (X.smallEtaleTopology.over (e.inverse.obj (e.functor.obj (U i))))
            (X.smallEtaleTopology.over (U i)) := by
          constructor
          intro A R hR
          change Sieve.overEquiv A (R.functorPullback _) ∈ X.smallEtaleTopology A.left
          rw [Sieve.overEquiv_functorPullback_map]
          exact hR
        exact isCocontinuous_comp _ _
          (J.over (e.functor.obj (U i)))
          (X.smallEtaleTopology.over (e.inverse.obj (e.functor.obj (U i))))
      have : ei.inverse.IsDenseSubsite (J.over (e.functor.obj (U i)))
          (X.smallEtaleTopology.over (U i)) :=
        ei.isDenseSubsite_inverse_of_isCocontinuous _ _
      let Si := ei.sheafCongr (X.smallEtaleTopology.over (U i))
        (J.over (e.functor.obj (U i))) (ModuleCat.{u + 1} B)
      refine ⟨M, hM, ⟨?_⟩⟩
      let H := (DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) q).obj K
      have hr : (S.functor.obj H).over (e.functor.obj (U i)) ≅
          Si.functor.obj (H.over (U i)) := Iso.refl _
      exact (J.overPullback (ModuleCat.{u + 1} B) (e.functor.obj (U i))).mapIso
          ((S.functor.mapDerivedCategoryHomologyFunctorIso q).app K).symm ≪≫
        hr ≪≫ Si.functor.mapIso hi ≪≫
        (ei.constantSheafSheafCongrIso (X.smallEtaleTopology.over (U i))
          (J.over (e.functor.obj (U i))) (ModuleCat.{u + 1} B)
          CategoryTheory.Over.mkIdTerminal).app M
  obtain ⟨I, U, f, hf, hM⟩ := site K' a b hab hvan' hloc'
  let V (i : I) := e.inverse.obj (U i)
  let g (i : I) : V i ⟶ Scheme.Etale.mk (𝟙 X) := e.inverse.map (f i)
  have hc : Sieve.ofArrows V g ∈ X.smallEtaleTopology (Scheme.Etale.mk (𝟙 X)) := by
    have hf' : Sieve.ofArrows U f ∈ J T := hf
    change Sieve.ofArrows (fun i ↦ e.inverse.obj (U i))
      (fun i ↦ e.inverse.map (f i)) ∈ X.smallEtaleTopology (e.inverse.obj T)
    rw [← Sieve.functorPushforward_ofArrows]
    exact (e.inverse.functorPushforward_mem_iff J X.smallEtaleTopology).mpr hf'
  have hs : ∀ x : X, ∃ i : I, ∃ y : (V i).left, (g i).left y = x := by
    have hr := (ofArrows_mem_smallEtaleTopology_iff (f := g)).mp hc
    intro x
    have hx : x ∈ ⋃ i, Set.range (g i).left := hr.symm ▸ Set.mem_univ x
    simpa only [Set.mem_iUnion, Set.mem_range] using hx
  choose index point hpoint using hs
  let 𝒰 : Cover.{u} etalePrecoverage X :=
    Cover.mkOfCovers X (fun x ↦ (V (index x)).left)
      (fun x ↦ (V (index x)).hom)
      (fun x ↦ ⟨x, point x, by
        have hw : (g (index x)).left = (V (index x)).hom := by
          have hh := MorphismProperty.Over.w (g (index x))
          change (g (index x)).left ≫ 𝟙 X = (V (index x)).hom at hh
          exact (Category.comp_id _).symm.trans hh
        exact (congrArg (fun q : (V (index x)).left ⟶ X ↦ q (point x)) hw).symm.trans
          (hpoint x)⟩)
      (fun _ ↦ inferInstance)
  refine ⟨𝒰, fun x ↦ ?_⟩
  obtain ⟨E, hfinite, hsupport, ⟨hmodel⟩⟩ := hM (index x)
  have hfinite' (n : ℤ) : Finite (E.X n) := by
    have := hfinite n
    exact Module.finite_of_finite B
  refine ⟨E, hfinite', hsupport, ⟨?_⟩⟩
  let W := V (index x)
  let ei := Over.postEquiv (X := W) e
  have : ei.functor.IsCocontinuous (X.smallEtaleTopology.over W)
      (J.over (e.functor.obj W)) := by
    change (Over.post (X := W) e.functor).IsCocontinuous _ _
    infer_instance
  have : ei.inverse.IsCocontinuous (J.over (e.functor.obj W))
      (X.smallEtaleTopology.over W) := by
    change (Over.post (X := e.functor.obj W) e.inverse ⋙
      Over.map (e.unitIso.inv.app W)).IsCocontinuous _ _
    have : (Over.map (e.unitIso.inv.app W)).IsCocontinuous
        (X.smallEtaleTopology.over (e.inverse.obj (e.functor.obj W)))
        (X.smallEtaleTopology.over W) := by
      constructor
      intro A R hR
      change Sieve.overEquiv A (R.functorPullback _) ∈ X.smallEtaleTopology A.left
      rw [Sieve.overEquiv_functorPullback_map]
      exact hR
    exact isCocontinuous_comp _ _ (J.over (e.functor.obj W))
      (X.smallEtaleTopology.over (e.inverse.obj (e.functor.obj W)))
  have : ei.inverse.IsDenseSubsite (J.over (e.functor.obj W))
      (X.smallEtaleTopology.over W) := ei.isDenseSubsite_inverse_of_isCocontinuous _ _
  let Si := ei.sheafCongr (X.smallEtaleTopology.over W)
    (J.over (e.functor.obj W)) (ModuleCat.{u + 1} B)
  let F := X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} B) W
  let F' := J.overPullback (ModuleCat.{u + 1} B) (e.functor.obj W)
  have : Si.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : F.Additive := Functor.additive_of_preserves_binary_products _
  have : F'.Additive := Functor.additive_of_preserves_binary_products _
  let hr : F ⋙ Si.functor ≅ S.functor ⋙ F' :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)
  let c := ei.constantSheafSheafCongrIso (X.smallEtaleTopology.over W)
    (J.over (e.functor.obj W)) (ModuleCat.{u + 1} B) CategoryTheory.Over.mkIdTerminal
  have he : Si.functor.mapDerivedCategory.obj (F.mapDerivedCategory.obj K) ≅
      Si.functor.mapDerivedCategory.obj (DerivedCategory.Q.obj
        (((constantSheaf (X.smallEtaleTopology.over W)
          (ModuleCat.{u + 1} B)).mapHomologicalComplex (ComplexShape.up ℤ)).obj E)) :=
    (Functor.mapDerivedCategoryCompIso F Si.functor).app K ≪≫
      (Functor.mapDerivedCategoryNatIso hr).app K ≪≫
      ((Functor.mapDerivedCategoryCompIso S.functor F').app K).symm ≪≫ hmodel ≪≫
      (DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso c
        (ComplexShape.up ℤ)).app E)).symm ≪≫
      (Si.functor.mapDerivedCategoryFactors.app _).symm
  let emodel := Si.functor.mapDerivedCategory.preimageIso he
  let Z := Scheme.Etale.overSheafEquiv W (ModuleCat.{u + 1} B)
  have : Z.functor.Additive := Functor.additive_of_preserves_binary_products _
  let hz := (Functor.mapDerivedCategoryNatIso (overRestrictionIso B W)).app K
  let cz : constantSheaf (X.smallEtaleTopology.over W) (ModuleCat.{u + 1} B) ⋙
      Z.functor ≅ constantSheaf W.left.smallEtaleTopology (ModuleCat.{u + 1} B) :=
    (Scheme.Etale.overEquiv W).constantSheafSheafCongrIso
    (X.smallEtaleTopology.over W) W.left.smallEtaleTopology (ModuleCat.{u + 1} B)
    CategoryTheory.Over.mkIdTerminal
  exact hz.symm ≪≫ ((Functor.mapDerivedCategoryCompIso F Z.functor).app K).symm ≪≫
    Z.functor.mapDerivedCategory.mapIso emodel ≪≫
    Z.functor.mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso cz
      (ComplexShape.up ℤ)).app E)

end AlgebraicGeometry.Etale
