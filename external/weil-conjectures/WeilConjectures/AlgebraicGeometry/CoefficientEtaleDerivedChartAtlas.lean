/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicResidueLiftComparisons
public import WeilConjectures.AlgebraicGeometry.CoefficientEtaleDerivedStalk
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import WeilConjectures.AlgebraicGeometry.CoefficientEtaleChartComparison
import WeilConjectures.AlgebraicGeometry.CoefficientEtaleChartStalk
import all WeilConjectures.AlgebraicGeometry.LisseCoefficientConstructible
import WeilConjectures.AlgebraicGeometry.SiteBoundedConstantModel
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Etale charts for bounded lisse coefficient complexes

Source: Stacks Project, Cohomology on Sites, lemma-locally-constant (Tag 094G),
and Etale Cohomology, lemma-connected-ctf-locally-constant (Tag 09BI).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

universe u v w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem precoverage_topology {C : Type*} [Category C]
    (J : GrothendieckTopology C) : J.toPrecoverage.toGrothendieck = J := by
  apply le_antisymm J.toGrothendieck_toPrecoverage_le
  intro U S hS
  simpa only [Sieve.generate_sieve] using J.toPrecoverage.generate_mem_toGrothendieck
    ((J.arrows_mem_toPrecoverage_iff S).2 hS)

attribute [-instance] HasDerivedCategory.ofIsGrothendieckAbelian in
private theorem topology_models
    {C : Type w} [SmallCategory C] [HasPullbacks C]
    (P : Precoverage C) [P.HasIsos] [P.IsStableUnderComposition]
    [P.IsStableUnderBaseChange] [P.HasPullbacks]
    (J : GrothendieckTopology C) (hJ : P.toGrothendieck = J)
    (X : C) (hX : IsTerminal X) (B : Type w) [CommRing B] [IsNoetherianRing B] :
    letI (S : GrothendieckTopology C) :
        HasDerivedCategory.{w + 1} (Sheaf S (ModuleCat.{w} B)) :=
      HasDerivedCategory.standard _
    ∀ (K : DerivedCategory (Sheaf J (ModuleCat.{w} B)))
      (a b : ℤ) (_ : a ≤ b)
      (_ : ∀ q : ℤ, q < a ∨ b < q →
        IsZero ((DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{w} B)) q).obj K))
      (_ : ∀ (q : ℤ) (V : C),
        ∃ (I : Type w) (U : I → C) (f : ∀ i, U i ⟶ V),
          Presieve.ofArrows U f ∈ P V ∧
          ∀ i, ∃ M : ModuleCat.{w} B, Module.Finite B M ∧ Nonempty
            ((J.overPullback (ModuleCat.{w} B) (U i)).obj
              ((DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{w} B)) q).obj K) ≅
              (constantSheaf (J.over (U i)) (ModuleCat.{w} B)).obj M)),
      ∃ (I : Type w) (U : I → C) (f : ∀ i, U i ⟶ X),
        Presieve.ofArrows U f ∈ P X ∧
        ∀ i, ∃ M : CochainComplex (ModuleCat.{w} B) ℤ,
          (∀ q, Module.Finite B (M.X q)) ∧
          (∀ q, q < a ∨ b < q → IsZero (M.X q)) ∧
          letI := HasDerivedCategory.standard (Sheaf (J.over (U i)) (ModuleCat.{w} B))
          Nonempty ((J.overPullback (ModuleCat.{w} B) (U i)).mapDerivedCategory.obj K ≅
            DerivedCategory.Q.obj
              (((constantSheaf (J.over (U i)) (ModuleCat.{w} B)).mapHomologicalComplex
                (.up ℤ)).obj M)) := by
  subst J
  let (S : GrothendieckTopology C) :
      HasDerivedCategory.{w + 1} (Sheaf S (ModuleCat.{w} B)) :=
    HasDerivedCategory.standard _
  let : ∀ U : C, HasDerivedCategory.{w + 1}
      (Sheaf (P.toGrothendieck.over U) (ModuleCat.{w} B)) :=
    fun U ↦ HasDerivedCategory.standard _
  exact exists_site_bounded_constant_model P X hX B

attribute [-instance] HasDerivedCategory.ofIsGrothendieckAbelian in
private theorem fixed_models
    (X : Scheme.{u})
    (B : Type (max v (u + 1))) [CommRing B] [IsNoetherianRing B]
    (K : ConstantCompletion.D
      (ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, v} X) B))
    (hbounded : ∃ c d : ℤ, ∀ q : ℤ, q < c ∨ d < q →
      IsZero ((coefficientModelCohomology _ q).obj K))
    (hlisse : ∀ q : ℤ, SheafOfModules.IsLocallyConstantFiniteTypeModules
      (smallModelComparisonEtaleTopology.{u, v} X) B
      ((coefficientModelCohomology _ q).obj K)) :
    ∃ (I : Type (max v (u + 1)))
      (U : I → smallModelComparisonEtaleSite.{u, v} X),
      (∀ x : X, ∃ i, x ∈ Set.range (AsSmall.down.obj (U i) : X.Etale).hom.base) ∧
      ∀ i, ∃ M : CochainComplex (ModuleCat.{max v (u + 1)} B) ℤ,
        CoefficientFixedLocalModel (smallModelComparisonEtaleTopology.{u, v} X) B K (U i) M := by
  classical
  let T := smallModelComparisonEtaleTopology.{u, v} X
  let C := smallModelComparisonEtaleSite.{u, v} X
  let F := coefficientModelFixedScalars T B
  let := HasDerivedCategory.standard (ConstantCompletion.Mod (ConstantCompletion.constant T B))
  have (S : GrothendieckTopology (smallModelComparisonEtaleSite.{u, v} X)) :
      HasSheafify S (ModuleCat.{max v (u + 1)} B) :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian S _
  let := HasDerivedCategory.standard (Sheaf T (ModuleCat.{max v (u + 1)} B))
  let (U : smallModelComparisonEtaleSite.{u, v} X) :
      HasDerivedCategory.{max v (u + 1) + 1}
        (Sheaf (T.over U) (ModuleCat.{max v (u + 1)} B)) :=
    HasDerivedCategory.standard (Sheaf (T.over U) (ModuleCat.{max v (u + 1)} B))
  have hT := precoverage_topology T
  have : (AsSmall.down : C ⥤ X.Etale).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).isEquivalence_inverse
  have : HasPullbacks C :=
    Adjunction.hasLimitsOfShape_of_equivalence (AsSmall.down : C ⥤ X.Etale)
  let top : C := AsSmall.up.obj (Etale.mk (𝟙 X))
  have htop : IsTerminal top :=
    (Etale.isTerminalMkId X).isTerminalOfObj AsSmall.down top
  let L := (coefficientFixedDerivedScalars T B).obj K
  have hcoh (q : ℤ) : F.obj ((coefficientModelCohomology _ q).obj K) ≅
      (DerivedCategory.homologyFunctor (Sheaf T (ModuleCat.{max v (u + 1)} B)) q).obj L :=
    (F.mapDerivedCategoryHomologyFunctorIso q).app K
  obtain ⟨c, d, hvan⟩ := hbounded
  have hb (q : ℤ) (hq : q < min c d ∨ d < q) :
      IsZero ((DerivedCategory.homologyFunctor
        (Sheaf T (ModuleCat.{max v (u + 1)} B)) q).obj L) :=
    (F.map_isZero (hvan q (by omega))).of_iso (hcoh q).symm
  have hloc (q : ℤ) (V : C) :
      ∃ (I : Type (max v (u + 1))) (U : I → C) (f : ∀ i, U i ⟶ V),
        Presieve.ofArrows U f ∈ T.toPrecoverage V ∧
        ∀ i, ∃ M : ModuleCat.{max v (u + 1)} B, Module.Finite B M ∧ Nonempty
          ((T.overPullback (ModuleCat.{max v (u + 1)} B) (U i)).obj
            ((DerivedCategory.homologyFunctor
              (Sheaf T (ModuleCat.{max v (u + 1)} B)) q).obj L) ≅
            (constantSheaf (T.over (U i)) (ModuleCat.{max v (u + 1)} B)).obj M) := by
    obtain ⟨S, hS, hmodels⟩ :=
      fixed_lisse T B _ (hlisse q) V
    let I := Σ U : C, {f : U ⟶ V // S f}
    let U : I → C := fun i ↦ i.1
    let f : ∀ i, U i ⟶ V := fun i ↦ i.2.1
    have heq : Sieve.generate (Presieve.ofArrows U f) = S := by
      apply le_antisymm
      · rw [Sieve.generate_le_iff]
        rintro _ _ ⟨i⟩
        exact i.2.2
      · intro W g hg
        exact Sieve.le_generate _ _ _ (Presieve.ofArrows.mk (⟨W, g, hg⟩ : I))
    refine ⟨I, U, f, ?_, fun i ↦ ?_⟩
    · change Sieve.generate (Presieve.ofArrows U f) ∈ T V
      rwa [heq]
    · obtain ⟨M, hM, ⟨e⟩⟩ := hmodels (U i) (f i) i.2.2
      exact ⟨M, hM, ⟨(T.overPullback _ (U i)).mapIso (hcoh q).symm ≪≫ e⟩⟩
  have models := topology_models T.toPrecoverage T hT top htop B
  obtain ⟨I, U, f, hf, hm⟩ := models L (min c d) d (min_le_right _ _) hb hloc
  refine ⟨I, U, ?_, fun i ↦ ?_⟩
  · have hc : Sieve.ofArrows U f ∈ T top := hf
    have hc' := (CoverPreserving.of_isContinuous (AsSmall.down : C ⥤ X.Etale)
      T X.smallEtaleTopology).cover_preserve hc
    rw [Sieve.functorPushforward_ofArrows] at hc'
    have hs := (ofArrows_mem_smallEtaleTopology_iff _).mp hc'
    intro x
    have hx : x ∈ ⋃ i, Set.range ((AsSmall.down : C ⥤ X.Etale).map (f i)).left := by
      rw [hs]
      trivial
    obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp hx
    refine ⟨i, y, ?_⟩
    have hw := MorphismProperty.Over.w ((AsSmall.down : C ⥤ X.Etale).map (f i))
    have hw' : ((AsSmall.down : C ⥤ X.Etale).map (f i)).left ≫
        (AsSmall.down.obj top : X.Etale).hom = (AsSmall.down.obj (U i) : X.Etale).hom := hw
    change ((AsSmall.down : C ⥤ X.Etale).map (f i)).left ≫ 𝟙 X = _ at hw'
    let a : (AsSmall.down.obj (U i) : X.Etale).left ⟶ X :=
      ((AsSmall.down : C ⥤ X.Etale).map (f i)).left
    have ha : a = (AsSmall.down.obj (U i) : X.Etale).hom :=
      (Category.comp_id a).symm.trans hw'
    exact (congrArg (fun g : (AsSmall.down.obj (U i) : X.Etale).left ⟶ X ↦ g y)
      ha).symm.trans hy
  · obtain ⟨M, _, _, hM⟩ := hm i
    exact ⟨M, hM⟩

/-- A bounded lisse complex admits etale charts with individual algebraic models.
The models identify all geometric stalks over the chart image and realize the
comparison pullback on every pro-etale object factoring through that chart.
There is no assertion that different charts have isomorphic models.

Source: Stacks Project, sites-cohomology.tex, lemma-locally-constant (094G);
etale-cohomology.tex, proof of lemma-connected-ctf-locally-constant (09BI),
through the choice of the individual complexes; Tags 03PT, 04EQ, 099R and 03DJ.
(auxiliary; not a blueprint node).

Proof: Restrict constant scalars to obtain a complex of B-module-valued sheaves
on the coefficient-sized etale site. This is an exact equivalence and takes
finite locally constant cohomology to finite locally constant cohomology.
Use the existing bounded constant-model theorem (094G), with lower bound min(c,d)
if the given bounds are reversed. It supplies an etale covering by bounded
complexes of finite B-modules. Transport the covering through AsSmall.down.
For each point of X choose one chart above it; retain that entire chart and its
algebraic derived model. This selection is only inside the existential proof.
For any point y in the image of a chart, lift X.algClosurePoint(y) to that
chart using the etale geometric-point lifting lemma. Restrict the local model
to this pointed chart and apply its exact geometric stalk. A constant sheaf
has stalk its coefficient module, naturally in that module. Applying these
natural isomorphisms termwise and localizing gives the displayed isomorphism
from the algebraic model to the specified derived stalk at y. Finally pull
the chart isomorphism through the etale/pro-etale comparison and restrict along
the given factorization from V. Inverse image and slice restriction are exact
and commute with constant sheaves; their termwise natural isomorphisms descend
to the derived categories. The canonical constant-coefficient ring comparison
identifies the result with adicFinitePullback and the commutative constant
realization displayed below. No connectedness, Tor amplitude, affineness or
weak contractibility is used. If X is empty the chart family is empty; empty
charts and zero models give the same exact restriction formulas. -/
theorem coefficient_etale_derived_chart_atlas
    (X : Scheme.{u})
    (B : Type (max v (u + 1))) [CommRing B] [IsNoetherianRing B]
    (K : ConstantCompletion.D
      (ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, v} X) B))
    (hbounded : ∃ c d : ℤ, ∀ q : ℤ, q < c ∨ d < q →
      IsZero ((coefficientModelCohomology _ q).obj K))
    (hlisse : ∀ q : ℤ, SheafOfModules.IsLocallyConstantFiniteTypeModules
      (smallModelComparisonEtaleTopology.{u, v} X) B
      ((coefficientModelCohomology _ q).obj K)) :
    letI := HasDerivedCategory.standard (ConstantCompletion.Mod
      (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X) B))
    ∃ (W : X → X.Etale) (M : X → DerivedCategory (ModuleCat.{max v (u + 1)} B)),
      (∀ x : X, x ∈ Set.range (W x).hom.base) ∧
      (∀ (i x : X), x ∈ Set.range (W i).hom.base →
        Nonempty (M i ≅ (coefficientEtaleDerivedStalk X B (X.algClosurePoint x)).obj K)) ∧
      ∀ (i : X) (V : coefficientProEtaleSiteModel.{u, v} X),
        ((AsSmall.down : coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt).obj V ⟶
          (toProEt X).obj (W i)) →
        Nonempty ((adicResidueRestriction
          (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X) B) V).obj
            ((commutativeSiteDerivedConstantModuleFunctor.{max v (u + 1), max v (u + 1),
              max v (u + 1), max v (u + 1) + 1}
              (coefficientProEtaleModelTopology.{u, v} X) B).obj (M i)) ≅
          (adicResidueRestriction
            (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X) B) V).obj
              ((adicFinitePullback.{u, v} X B).obj K))  := by
  classical
  obtain ⟨I, U, hcover, hmodels⟩ := fixed_models X B K hbounded hlisse
  choose j hj using hcover
  choose M hM using hmodels
  refine ⟨fun x ↦ AsSmall.down.obj (U (j x)),
    fun x ↦ DerivedCategory.Q.obj (M (j x)), hj, ?_, ?_⟩
  · intro i x hx
    obtain ⟨y, hy⟩ := hx
    obtain ⟨t, ht, _⟩ := exists_fac_of_etale_of_isSepClosed
      (AsSmall.down.obj (U (j i)) : X.Etale).hom (X.algClosurePoint x) y
      (hy.trans (X.algClosurePoint_base x default).symm)
    exact coefficient_etale_chart_stalk X B K (U (j i)) (M (j i)) (hM (j i))
      (X.algClosurePoint x) t ht
  · intro i V f
    exact coefficient_etale_chart_comparison X B K (U (j i)) (M (j i)) (hM (j i)) V f

end AlgebraicGeometry.Scheme
