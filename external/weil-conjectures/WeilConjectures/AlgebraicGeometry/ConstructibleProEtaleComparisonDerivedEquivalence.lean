/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonData
import WeilConjectures.AlgebraicGeometry.CoefficientBoundedClassicalDescent
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonModuleCriteria
import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleConstructibleIso
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonClassical

/-! Constructible pro-etale comparison: bounded restriction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite

-- The universe-polymorphic `hasSheafify_of_essentiallySmall` gets stuck on the universe of
-- `ModuleCat.{max v (u + 1)}`; Mathlib's concrete-category instance applies instead.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
namespace AlgebraicGeometry.ProEtale
/-- Restrict derived comparison to bounded constructible objects.
Source: blueprint constructible-comparison-equivalence, part (2), Stacks Tag 09AL
(auxiliary; not a blueprint node).

Proof: the cohomology comparison and the module constructibility test show that
derived inverse image preserves constructible cohomology. Its zero preservation
preserves the stated finite cohomological interval. Lift to the full subcategories.
Bounded classical full faithfulness supplies injectivity and surjectivity on all
morphisms. For essential surjectivity, a bounded constructible target has continuous
cohomology by classicality of each constructible cohomology module. Bounded
classical descent gives a derived antecedent. Cohomology comparison identifies its
cohomology images with the given constructible cohomology modules. Reflection of
module constructibility makes the antecedent constructible. Full faithfulness of
module inverse image reflects zero objects, so its cohomology vanishes outside the
same interval; hence the antecedent is bounded. The equivalence therefore has the
lifted canonical functor as its actual forward functor. -/
theorem constructibleComparison_boundedRestriction (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A] :
    ∀ [CompactSpace X] [QuasiSeparatedSpace X]
      (D : ConstantCompletion.D (ConstantCompletion.constant
          (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A) ⥤
            ConstantCompletion.D (ConstantCompletion.constant
              (Scheme.coefficientProEtaleModelTopology.{u, v} X) A)),
      Nonempty (ConstantCompletion.Q _ ⋙ D ≅
        constructibleComparisonComplexPullback X A ⋙ ConstantCompletion.Q _) →
      (∀ q : ℤ, Nonempty (D ⋙ coefficientModelCohomology _ q ≅
        coefficientModelCohomology _ q ⋙ constructibleComparisonPullback X A)) →
        ∃ e : Scheme.CoefficientBoundedConstructibleEtaleCategory.{u, v} X A ≌
            (coefficientBoundedConstructibleProEtale X A).FullSubcategory,
          Nonempty (e.functor ⋙ (coefficientBoundedConstructibleProEtale X A).ι ≅
            ObjectProperty.ι (Scheme.IsCoefficientBoundedConstructibleEtale X A) ⋙ D) := by
  intro _ _ D hD hH
  obtain ⟨hfull, hfaithful, horigin, htest⟩ := coefficientComparison_moduleCriteria X A
  have := hfull
  have := hfaithful
  obtain ⟨hff, hdesc⟩ := coefficientComparison_boundedClassical X A D hD
  let L := constructibleComparisonPullback X A
  have : L.IsLeftAdjoint := (SheafOfModules.pullbackPushforwardAdjunction.{max v (u + 1)}
    (F := Scheme.smallModelComparisonInclusion.{u, v} X)
    (constructibleComparisonRingMap X A)).isLeftAdjoint
  have : L.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint L
  let P : ObjectProperty (ConstantCompletion.D (ConstantCompletion.constant
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A)) :=
    Scheme.IsCoefficientBoundedConstructibleEtale X A
  let Q := coefficientBoundedConstructibleProEtale X A
  have hobj (K) (hK : P K) : Q (D.obj K) := by
    constructor
    · intro q
      obtain ⟨e⟩ := hH q
      exact coefficientProEtale_constructible_of_iso X A (e.app K).symm
        ((htest _).mp (hK.1 q))
    · obtain ⟨a, b, hab, hv⟩ := hK.2
      refine ⟨a, b, hab, ?_⟩
      intro q hq
      obtain ⟨e⟩ := hH q
      exact (L.map_isZero (hv q hq)).of_iso (e.app K)
  let T : P.FullSubcategory ⥤ Q.FullSubcategory :=
    Q.lift (P.ι ⋙ D) (fun K ↦ hobj K.obj K.property)
  have : T.Faithful := by
    constructor
    intro K M f g h
    apply ObjectProperty.hom_ext
    apply (hff K.obj M.obj K.property.2 M.property.2).injective
    exact congrArg (fun f : T.obj K ⟶ T.obj M ↦ Q.ι.map f) h
  have : T.Full := by
    constructor
    intro K M f
    obtain ⟨g, hg⟩ := (hff K.obj M.obj K.property.2 M.property.2).surjective f.hom
    exact ⟨ObjectProperty.homMk g, ObjectProperty.hom_ext _ hg⟩
  have : T.EssSurj := by
    constructor
    intro K
    obtain ⟨M, ⟨e⟩⟩ := hdesc K.obj K.property.2
      (fun q ↦ constructibleComparison_classical X A _ (K.property.1 q))
    have hM : P M := by
      constructor
      · intro q
        obtain ⟨eh⟩ := hH q
        let i := ((coefficientModelCohomology _ q).mapIso e).symm ≪≫ eh.app M
        exact (htest _).mpr
          (coefficientProEtale_constructible_of_iso X A i (K.property.1 q))
      · obtain ⟨a, b, hab, hv⟩ := K.property.2
        refine ⟨a, b, hab, ?_⟩
        intro q hq
        obtain ⟨eh⟩ := hH q
        let i := ((coefficientModelCohomology _ q).mapIso e).symm ≪≫ eh.app M
        exact IsZero.of_full_of_faithful_of_isZero L _ ((hv q hq).of_iso i.symm)
    exact ⟨⟨M, hM⟩, ⟨Q.isoMk e⟩⟩
  have : T.IsEquivalence := ⟨inferInstance, inferInstance, inferInstance⟩
  exact ⟨T.asEquivalence, ⟨Iso.refl _⟩⟩

end AlgebraicGeometry.ProEtale
