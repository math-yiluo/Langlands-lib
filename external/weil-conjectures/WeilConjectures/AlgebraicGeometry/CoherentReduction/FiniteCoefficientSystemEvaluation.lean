/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoherentReduction.CoherentIntegralReduction
public import WeilConjectures.CategoryTheory.Sites.FixedCoefficientDerivedChangeOfRings
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedMorphismSheafComparison
public import WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement
public import WeilConjectures.Algebra.Homology.RingIsomorphismTensorTransport
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryNatTrans
public import WeilConjectures.AlgebraicGeometry.Derived.ComparisonScalarExtensionMate

/-! # Finite-coefficient presentations of the genuine system evaluations

Source: Zheng, Construction 4.1; Bhatt--Scholze, finite coefficient comparison.
(blueprint: def-sfb-finite-coefficient-system-evaluation)

The functors change only the presentation of the same module sheaves. In
particular the horizontal arrows below are those of the actual sequence topos.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.CoherentReduction

attribute [local instance] WeilConjectures.instEssentiallySmallProEt_weilConjectures
  AlgebraicGeometry.ProEtale.VaryingRing.sequenceSiteSmall

/-- Proof alias of the existing exactness-reflection criteria for scalar restriction.
The underlying abelian sheaf is unchanged; no new exactness theorem is postulated.
Source: Stacks 03D7 (blueprint: def-sfb-finite-coefficient-system-evaluation).
Proof: compose with the faithful exact forgetful functor to abelian sheaves, which
reflects finite limits and finite colimits, and use the corresponding forgetful
functor on the source ring. -/
private abbrev ringRestriction_exact (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1}} (a : R ⟶ S) :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{u + 1} a) ∧
      PreservesFiniteColimits (SheafOfModules.restrictScalars.{u + 1} a) := by
  let U := SheafOfModules.toSheaf.{u + 1} R
  have : PreservesFiniteLimits (SheafOfModules.restrictScalars.{u + 1} a ⋙ U) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{u + 1} S))
  have : PreservesFiniteColimits (SheafOfModules.restrictScalars.{u + 1} a ⋙ U) :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf.{u + 1} S))
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves _ U,
    preservesFiniteColimits_of_reflects_of_preserves _ U⟩

/-- The existing equivalence from constant-ring module sheaves to fixed-ring sheaves.
Source: Stacks 03DA (blueprint: def-sfb-finite-coefficient-system-evaluation). -/
def fixedEquivalence (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  (constant_ring_module_sheaves.{u + 1, u} (Scheme.ProEt.topology X) A).1.choose

/-- Its forward maps are the original scalar restrictions.
Source: Stacks 03DA (blueprint: def-sfb-finite-coefficient-system-evaluation). -/
instance fixedEquivalence_additive (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (fixedEquivalence X A).functor.Additive :=
  (constant_ring_module_sheaves.{u + 1, u}
    (Scheme.ProEt.topology X) A).1.choose_spec.2.1

/-- Its inverse retains the original additive sections and maps.
Source: Stacks 03DA (blueprint: def-sfb-finite-coefficient-system-evaluation). -/
instance fixedEquivalence_inverse_additive (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (fixedEquivalence X A).inverse.Additive :=
  (constant_ring_module_sheaves.{u + 1, u}
    (Scheme.ProEt.topology X) A).1.choose_spec.2.2.1

/-- Canonical finite realization on the pro-etale site, through the constant-section iso.
Source: finite coefficient comparison
(blueprint: def-sfb-finite-coefficient-system-evaluation). -/
def finiteRealization (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) ⥤
      WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (sectionRing X A) :=
  (fixedEquivalence X A).inverse ⋙
    SheafOfModules.restrictScalars (realizationRingIso.{u + 1, u}
      (Scheme.ProEt.topology X) A).hom ⋙
    res.{u + 1, u, u + 1} (finiteConstantIso X A).inv

/-- The inverse finite presentation, with its unchanged underlying additive maps.
Source: finite coefficient comparison
(blueprint: def-sfb-finite-coefficient-system-evaluation). -/
def finiteUnrealization (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] :
    WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (sectionRing X A) ⥤
      Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) :=
  res.{u + 1, u, u + 1} (finiteConstantIso X A).hom ⋙
    CategoryTheory.ConstantScalarRestriction.restriction (Scheme.ProEt.topology X) A

/-- Finite realization is additive.
Source: Stacks 03DA (blueprint: def-sfb-finite-coefficient-system-evaluation). -/
instance finiteRealization_additive (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    [Finite A] [TopologicalSpace A] [DiscreteTopology A] :
    (finiteRealization X A).Additive := by
  unfold finiteRealization
  infer_instance

/-- Finite realization preserves finite limits.
Source: Stacks 03DA (blueprint: def-sfb-finite-coefficient-system-evaluation). -/
instance finiteRealization_limits (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    [Finite A] [TopologicalSpace A] [DiscreteTopology A] :
    PreservesFiniteLimits (finiteRealization X A) := by
  unfold finiteRealization
  have h := ringRestriction_exact X
    (realizationRingIso.{u + 1, u} (Scheme.ProEt.topology X) A).hom
  let := h.1
  let := h.2
  infer_instance

/-- Finite realization preserves finite colimits.
Source: Stacks 03DA (blueprint: def-sfb-finite-coefficient-system-evaluation). -/
instance finiteRealization_colimits (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    [Finite A] [TopologicalSpace A] [DiscreteTopology A] :
    PreservesFiniteColimits (finiteRealization X A) := by
  unfold finiteRealization
  have h := ringRestriction_exact X
    (realizationRingIso.{u + 1, u} (Scheme.ProEt.topology X) A).hom
  let := h.1
  let := h.2
  infer_instance

/-- The inverse presentation is additive.
Source: Stacks 03DA (blueprint: def-sfb-finite-coefficient-system-evaluation). -/
instance finiteUnrealization_additive (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    [Finite A] [TopologicalSpace A] [DiscreteTopology A] :
    (finiteUnrealization X A).Additive := by
  let := CategoryTheory.ConstantScalarRestriction.additive (Scheme.ProEt.topology X) A
  unfold finiteUnrealization
  change (SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
    (finiteConstantIso X A).hom ⋙ _).Additive
  infer_instance

/-- The inverse presentation preserves finite limits.
Source: Stacks 03DA (blueprint: def-sfb-finite-coefficient-system-evaluation). -/
instance finiteUnrealization_limits (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    [Finite A] [TopologicalSpace A] [DiscreteTopology A] :
    PreservesFiniteLimits (finiteUnrealization X A) := by
  let r := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (finiteConstantIso X A).hom
  have hr : PreservesFiniteLimits (SheafOfModules.restrictScalars.{u + 1} r) :=
    (ringRestriction_exact X r).1
  have hs : PreservesFiniteLimits
      (CategoryTheory.ConstantScalarRestriction.restriction.{u + 1, u}
        (Scheme.ProEt.topology X) A) :=
    (CategoryTheory.ConstantScalarRestriction.exact.{u + 1, u}
      (Scheme.ProEt.topology X) A).1
  change PreservesFiniteLimits (SheafOfModules.restrictScalars.{u + 1} r ⋙ _)
  infer_instance

/-- The inverse presentation preserves finite colimits.
Source: Stacks 03DA (blueprint: def-sfb-finite-coefficient-system-evaluation). -/
instance finiteUnrealization_colimits (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    [Finite A] [TopologicalSpace A] [DiscreteTopology A] :
    PreservesFiniteColimits (finiteUnrealization X A) := by
  let r := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (finiteConstantIso X A).hom
  have hr : PreservesFiniteColimits (SheafOfModules.restrictScalars.{u + 1} r) :=
    (ringRestriction_exact X r).2
  have hs : PreservesFiniteColimits
      (CategoryTheory.ConstantScalarRestriction.restriction.{u + 1, u}
        (Scheme.ProEt.topology X) A) :=
    (CategoryTheory.ConstantScalarRestriction.exact.{u + 1, u}
      (Scheme.ProEt.topology X) A).2
  change PreservesFiniteColimits (SheafOfModules.restrictScalars.{u + 1} r ⋙ _)
  infer_instance

/-- The finite presentation is an exact equivalence, with its original section maps.
Source: Stacks 03CY (blueprint: def-sfb-finite-coefficient-system-evaluation). -/
instance finiteUnrealization_isEquivalence (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    [Finite A] [TopologicalSpace A] [DiscreteTopology A] :
    (finiteUnrealization X A).IsEquivalence := by
  let t := (SheafOfModules.ringIso_tensor_transport (finiteConstantIso X A)).some
  have : (res.{u + 1, u, u + 1} (finiteConstantIso X A).hom).IsEquivalence := by
    change (SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
      (finiteConstantIso X A).hom).IsEquivalence
    rw [← t.functor_eq]
    infer_instance
  let := CategoryTheory.ConstantScalarRestriction.isEquivalence (Scheme.ProEt.topology X) A
  unfold finiteUnrealization
  infer_instance

/-- The ordinary tensor comparison sends local pure tensors to the same pure tensors.
Both factors use published, proved tensor-transport constructions.
Source: Stacks 03CY, 06YT
(blueprint: def-sfb-finite-coefficient-system-evaluation). -/
@[instance_reducible]
def finiteUnrealizationMonoidal (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    [Finite A] [TopologicalSpace A] [DiscreteTopology A] :
    (finiteUnrealization X A).Monoidal := by
  let t := (SheafOfModules.ringIso_tensor_transport (finiteConstantIso X A)).some
  letI : (res.{u + 1, u, u + 1} (finiteConstantIso X A).hom).Monoidal :=
    t.monoidal.toMonoidal
  letI := CategoryTheory.ConstantScalarRestriction.restrictionBraided (Scheme.ProEt.topology X) A
  unfold finiteUnrealization
  infer_instance

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Ordinary fixed-module evaluation of the actual system.
Source: Zheng 4.1 (blueprint: def-sfb-finite-coefficient-system-evaluation). -/
def fixedEvaluation (X : Scheme.{u}) (n : ℕ) :
    Systems.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (coefficients l E X) (transitions l E X) ⥤
      Sheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} (Etale.FiniteProperQuotient.Ring l E n)) :=
  evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
    (coefficients l E X) (transitions l E X) n ⋙
      finiteUnrealization X (Etale.FiniteProperQuotient.Ring l E n)

/-- Fixed evaluation preserves addition through the exact finite presentation.
Source: Zheng 4.1 (blueprint: def-sfb-finite-coefficient-system-evaluation). -/
instance fixedEvaluation_additive (X : Scheme.{u}) (n : ℕ) :
    (fixedEvaluation l E X n).Additive := by unfold fixedEvaluation; infer_instance

/-- Fixed evaluation preserves finite limits through the exact finite presentation.
Source: Stacks 0941 (blueprint: def-sfb-finite-coefficient-system-evaluation). -/
instance fixedEvaluation_limits (X : Scheme.{u}) (n : ℕ) :
    PreservesFiniteLimits (fixedEvaluation l E X n) := by
  unfold fixedEvaluation
  infer_instance

/-- Fixed evaluation preserves finite colimits through the exact finite presentation.
Source: Stacks 0941 (blueprint: def-sfb-finite-coefficient-system-evaluation). -/
instance fixedEvaluation_colimits (X : Scheme.{u}) (n : ℕ) :
    PreservesFiniteColimits (fixedEvaluation l E X n) := by
  unfold fixedEvaluation
  infer_instance

/-- Its exact derived evaluation, without choosing level objects.
Source: Zheng 4.1 (blueprint: def-sfb-finite-coefficient-system-evaluation). -/
def fixedDerivedEvaluation (X : Scheme.{u}) (n : ℕ) :
    DS.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (coefficients l E X) (transitions l E X) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} (Etale.FiniteProperQuotient.Ring l E n))) :=
  e.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
    (coefficients l E X) (transitions l E X) n ⋙
      (finiteUnrealization X (Etale.FiniteProperQuotient.Ring l E n)).mapDerivedCategory

/-- Exact derived etale-to-pro-etale comparison with the original fixed coefficients.
Source: Bhatt--Scholze, finite coefficient comparison
(blueprint: def-sfb-finite-coefficient-system-evaluation). -/
def nu (X : Scheme.{u}) (n : ℕ) :=
  (comparisonUpperStar (ModuleCat.{u + 1} (Etale.FiniteProperQuotient.Ring l E n))
    X).mapDerivedCategory

/-- The canonical derived comparison between scalar extension and `nu^*`.
Source: Stacks 09B1 and 0F63, via the scalar-restriction comparison square
(blueprint: def-sfb-finite-coefficient-system-evaluation).
The map is the mate of the existing comparison isomorphism, hence it is tied
to the derived scalar-extension adjunction and is not an arbitrary natural map. -/
noncomputable def nuFixedScalarExtensionComparisonMap (X : Scheme.{u})
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory ⋙
      CategoryTheory.Sheaf.fixedCoefficientDerivedScalarExtension
        (Scheme.ProEt.topology X) φ ⟶
    CategoryTheory.Sheaf.fixedCoefficientDerivedScalarExtension
      X.smallEtaleTopology φ ⋙
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory := by
  letI := CategoryTheory.Sheaf.fixedCoefficientDerivedRestriction_isRightAdjoint
    (Scheme.ProEt.topology X) φ
  letI := CategoryTheory.Sheaf.fixedCoefficientDerivedRestriction_isRightAdjoint
    X.smallEtaleTopology φ
  exact ((mateEquiv
    (G := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory)
    (H := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory)
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ))
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ))
    ).symm (TwoSquare.mk _ _ _ _ (Scheme.comparisonRestrictScalarsIso X A φ).hom))

/-- The canonical `nu^*`/scalar-extension comparison is invertible.
Source: Stacks 09B1 and 0F63 (blueprint: def-sfb-finite-coefficient-system-evaluation).
Proof: compute derived scalar extension on K-flat complexes. Exact comparison
pullback preserves flat sheaves and commutes with sheafified scalar tensor.
The ordinary scalar tensor comparison is an isomorphism on every term. Passing
to the localization gives the displayed mate, because its restriction mate is
exactly comparisonRestrictScalarsIso. Hence the derived mate is invertible. -/
theorem nuFixedScalarExtensionComparisonMap_isIso (X : Scheme.{u})
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) :
    IsIso (nuFixedScalarExtensionComparisonMap X φ) := by
  exact ProEtale.isIso_mate_comparisonRestrictScalarsIso φ X

/-- The canonical comparison isomorphism used by the finite reduction maps.
Source: Stacks 09B1 and 0F63 (blueprint: def-sfb-finite-coefficient-system-evaluation). -/
noncomputable def nuFixedScalarExtensionComparison (X : Scheme.{u})
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory ⋙
      CategoryTheory.Sheaf.fixedCoefficientDerivedScalarExtension
        (Scheme.ProEt.topology X) φ ≅
    CategoryTheory.Sheaf.fixedCoefficientDerivedScalarExtension
      X.smallEtaleTopology φ ⋙
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory := by
  letI := nuFixedScalarExtensionComparisonMap_isIso X φ
  exact asIso (nuFixedScalarExtensionComparisonMap X φ)

/-- Constant continuous functions commute with continuous postcomposition. -/
theorem pointConstants_naturality {T S : Type (u + 1)} [CommRing T] [CommRing S]
    [TopologicalSpace T] [TopologicalSpace S] [IsTopologicalRing T] [IsTopologicalRing S]
    (f : T →+* S) (hf : Continuous f) :
    (constantSheaf (coherentTopology Profinite.{u}) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom f) ≫ pointConstants S =
      pointConstants T ≫ continuousPointMap f hf := by
  dsimp only [pointConstants, continuousPointMap, constantSheaf, Functor.comp_map]
  exact (Functor.map_comp _ _ _).symm.trans
    ((congrArg _ (by ext; rfl)).trans (Functor.map_comp _ _ _))

/-- The additive constant-section map commutes with continuous postcomposition. -/
theorem schemeConstants_naturality (X : Scheme.{u}) {T S : Type (u + 1)} [CommRing T]
    [CommRing S] [TopologicalSpace T] [TopologicalSpace S] [IsTopologicalRing T]
    [IsTopologicalRing S] (f : T →+* S) (hf : Continuous f) :
    (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
        (AddCommGrpCat.ofHom f.toAddMonoidHom) ≫ schemeConstants X S =
      schemeConstants X T ≫ (upperStarFromPoint X).map
        ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (continuousPointMap f hf))) := by
  let : HasSheafify (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1} :=
    SheafOfModules.hasSheafify_coefficientUniverse
  let : (coherentTopology Profinite.{u}).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  have h := ((constantCommuteCompose (coherentTopology Profinite.{u})
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1})).inv.naturality (CommRingCat.ofHom f))
  have hp := congrArg (fun g ↦ (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map g))
    (pointConstants_naturality f hf)
  simp only [Functor.map_comp] at hp
  dsimp only [schemeConstants]
  rw [← Category.assoc, (constantSchemeIso X).hom.naturality]
  simp only [Functor.comp_map, Category.assoc, ← Functor.map_comp]
  congr 2
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) h).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  exact congrArg (_ ≫ ·) hp

/-- The constant-section homomorphisms commute with the section maps induced by continuous
postcomposition. -/
theorem constantSections_naturality (X : Scheme.{u}) {T S : Type (u + 1)} [CommRing T]
    [CommRing S] [TopologicalSpace T] [TopologicalSpace S] [IsTopologicalRing T]
    [IsTopologicalRing S] (f : T →+* S) (hf : Continuous f) :
    (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map (CommRingCat.ofHom f) ≫
        constantSections X S = constantSections X T ≫ sectionMap X f hf := by
  apply (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1})).map_injective
  have hT := eq_of_heq (constantSections_existsUnique X T).exists.choose_spec
  have hS := eq_of_heq (constantSections_existsUnique X S).exists.choose_spec
  have h := (constantCommuteCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1})).hom.naturality (CommRingCat.ofHom f)
  rw [Functor.map_comp, Functor.map_comp]
  unfold constantSections
  rw [hT, hS]
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) h).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  exact congrArg (_ ≫ ·) (schemeConstants_naturality X f hf)

/-- On the actual finite coefficient system, the constant-section isomorphisms intertwine the
horizontal coefficient maps with the constant quotient maps. -/
theorem finiteConstantIso_hom_coefficientMap (X : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    (finiteConstantIso X (Etale.FiniteProperQuotient.Ring l E m)).hom ≫
        WeilConjectures.SemilinearSections.coefficientMap.{u + 1, u, u + 1}
          (Scheme.ProEt.topology X) (coefficients l E X) (transitions l E X) h =
      (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (Etale.FiniteProperQuotient.quotient l E h)) ≫
        (finiteConstantIso X (Etale.FiniteProperQuotient.Ring l E n)).hom := by
  induction m, h using Nat.le_induction with
  | base =>
    have hq : CommRingCat.ofHom (Etale.FiniteProperQuotient.quotient l E (le_refl n)) = 𝟙 _ := by
      ext x
      rfl
    have hc : WeilConjectures.SemilinearSections.coefficientMap.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) (coefficients l E X) (transitions l E X) (le_refl n) = 𝟙 _ :=
      (WeilConjectures.SemilinearSections.rings.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
        (coefficients l E X) (transitions l E X)).map_id _
    rw [hq, hc, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  | succ m h ih =>
    have hc : WeilConjectures.SemilinearSections.coefficientMap.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) (coefficients l E X) (transitions l E X) (h.trans m.le_succ) =
        transitions l E X m ≫ WeilConjectures.SemilinearSections.coefficientMap.{u + 1, u, u + 1}
          (Scheme.ProEt.topology X) (coefficients l E X) (transitions l E X) h :=
      ((WeilConjectures.SemilinearSections.rings.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) (coefficients l E X) (transitions l E X)).map_comp _ _).trans
        (congrArg (· ≫ _) (Functor.ofOpSequence_map_homOfLE_succ (transitions l E X) m))
    have hq : CommRingCat.ofHom (Etale.FiniteProperQuotient.quotient l E (h.trans m.le_succ)) =
        CommRingCat.ofHom (Etale.FiniteProperQuotient.quotient l E m.le_succ) ≫
          CommRingCat.ofHom (Etale.FiniteProperQuotient.quotient l E h) := by
      ext x
      rfl
    rw [hc, hq, CategoryTheory.Functor.map_comp, Category.assoc, ← ih, ← Category.assoc,
      ← Category.assoc]
    congr 1
    exact (constantSections_naturality X _ _).symm

/-- Constant scalars are carried to constant scalars by the constant ring-sheaf map of a ring
homomorphism, in the `RingCat` presentation of the constant ring sheaves. -/
theorem constantSheaf_map_toSheafify_apply (X : Scheme.{u})
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (q : A →+* B) (U : X.ProEtᵒᵖ) (a : A) :
    ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom q)).hom.app U
        (((constantCommuteCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app (CommRingCat.of A)).hom.app U
          ((toSheafify (Scheme.ProEt.topology X)
            ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of A))).app U a)) =
      ((constantCommuteCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app (CommRingCat.of B)).hom.app U
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of B))).app U (q a)) := by
  have h1 := (constantCommuteCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.naturality (CommRingCat.ofHom q)
  have h2 := toSheafify_naturality (Scheme.ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).map (RingCat.ofHom q))
  have e1 := congrArg (fun g ↦ g.hom.app U ((toSheafify (Scheme.ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of A))).app U a)) h1
  exact e1.symm.trans (congrArg (fun y ↦ ((constantCommuteCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app (CommRingCat.of B)).hom.app U y)
    (congrArg (fun g ↦ g.app U a) h2).symm)

/-- A map of section-ring module sheaves which is semilinear over a coefficient map compatible
with `q : A →+* B` is a `q`-linear map of the finite fixed-coefficient presentations, with the
same underlying sections. -/
def finiteUnrealizationSemilinearMap (X : Scheme.{u}) {A B : Type (u + 1)} [CommRing A]
    [CommRing B] [Finite A] [Finite B] [TopologicalSpace A] [TopologicalSpace B]
    [DiscreteTopology A] [DiscreteTopology B] (q : A →+* B)
    (κ : sectionRing X A ⟶ sectionRing X B)
    (hκ : (finiteConstantIso X A).hom ≫ κ =
      (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map (CommRingCat.ofHom q) ≫
        (finiteConstantIso X B).hom)
    {N : WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (sectionRing X A)}
    {N' : WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (sectionRing X B)}
    (f : N ⟶ (res.{u + 1, u, u + 1} κ).obj N') :
    (finiteUnrealization X A).obj N ⟶ (Sheaf.restrictScalars (Scheme.ProEt.topology X) q).obj
      ((finiteUnrealization X B).obj N') :=
  ObjectProperty.homMk
    { app := fun U ↦ ModuleCat.homEquiv.symm
        { toFun := fun x ↦ (f.val.app U).hom x
          map_add' := fun x y ↦ (f.val.app U).hom.map_add x y
          map_smul' := fun a x ↦ by
            have key := (congrArg (fun g ↦ g.hom.app U
              (((constantCommuteCompose (Scheme.ProEt.topology X)
                (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app
                  (CommRingCat.of A)).hom.app U
                ((toSheafify (Scheme.ProEt.topology X)
                  ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of A))).app U a))) hκ).trans
              (congrArg (fun y ↦ (finiteConstantIso X B).hom.hom.app U y)
                (constantSheaf_map_toSheafify_apply X q U a))
            exact ((f.val.app U).hom.map_smul _ x).trans
              (congrArg (fun r : (WeilConjectures.SemilinearSections.ring.{u + 1, u, u + 1}
                (Scheme.ProEt.topology X) (sectionRing X B)).obj.obj U ↦
                  r • (show N'.val.obj U from (f.val.app U).hom x)) key) }
      naturality := fun U V g ↦ by
        ext x
        exact PresheafOfModules.naturality_apply f.val g x }

/-- The fixed-coefficient presentations of semilinear maps are natural. -/
theorem finiteUnrealizationSemilinearMap_naturality (X : Scheme.{u}) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B] [TopologicalSpace A] [TopologicalSpace B]
    [DiscreteTopology A] [DiscreteTopology B] (q : A →+* B)
    (κ : sectionRing X A ⟶ sectionRing X B)
    (hκ : (finiteConstantIso X A).hom ≫ κ =
      (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map (CommRingCat.ofHom q) ≫
        (finiteConstantIso X B).hom)
    {N₁ N₂ : WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (sectionRing X A)}
    {N₁' N₂' : WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (sectionRing X B)}
    (f₁ : N₁ ⟶ (res.{u + 1, u, u + 1} κ).obj N₁') (f₂ : N₂ ⟶ (res.{u + 1, u, u + 1} κ).obj N₂')
    (a : N₁ ⟶ N₂) (b : N₁' ⟶ N₂') (w : a ≫ f₂ = f₁ ≫ (res.{u + 1, u, u + 1} κ).map b) :
    (finiteUnrealization X A).map a ≫ finiteUnrealizationSemilinearMap X q κ hκ f₂ =
      finiteUnrealizationSemilinearMap X q κ hκ f₁ ≫
        (Sheaf.restrictScalars (Scheme.ProEt.topology X) q).map
          ((finiteUnrealization X B).map b) := by
  ext U x
  exact congrArg (fun φ ↦ (φ.val.app U).hom x) w

/-- The fixed-coefficient presentation of a semilinear map has the original underlying map of
abelian sheaves. -/
theorem finiteUnrealizationSemilinearMap_forget (X : Scheme.{u}) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B] [TopologicalSpace A] [TopologicalSpace B]
    [DiscreteTopology A] [DiscreteTopology B] (q : A →+* B)
    (κ : sectionRing X A ⟶ sectionRing X B)
    (hκ : (finiteConstantIso X A).hom ≫ κ =
      (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map (CommRingCat.ofHom q) ≫
        (finiteConstantIso X B).hom)
    {N : WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (sectionRing X A)}
    {N' : WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (sectionRing X B)}
    (f : N ⟶ (res.{u + 1, u, u + 1} κ).obj N') :
    HEq ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).map
          (finiteUnrealizationSemilinearMap X q κ hκ f))
      ((SheafOfModules.toSheaf (WeilConjectures.SemilinearSections.ring.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) (sectionRing X A))).map f) :=
  HEq.rfl
/-- The fixed coefficient transition is the original horizontal additive map.
Source: Zheng 4.1 (blueprint: def-sfb-finite-coefficient-system-evaluation).

Proof: evaluate a module system at m and n. Its horizontal map is linear over
A_m through the original quotient A_m to A_n. The constant-section maps commute
with continuous postcomposition. Consequently forgetting the two constant-ring
presentations turns this into precisely a map of fixed A_m-module sheaves.
The naturality square is the square already present in the module system.
Conversely the faithful forgetful functor to additive sheaves determines every
component and hence the natural transformation uniquely. No flatness is used.
-/
theorem fixedTransition_existsUnique (X : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    ∃! δ : fixedEvaluation l E X m ⟶ fixedEvaluation l E X n ⋙
        Sheaf.restrictScalars (Scheme.ProEt.topology X)
          (Etale.FiniteProperQuotient.quotient l E h),
      ∀ M : Systems.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
          (coefficients l E X) (transitions l E X),
        HEq ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ (ModuleCat.{u + 1} (Etale.FiniteProperQuotient.Ring l E m))
            AddCommGrpCat.{u + 1})).map (δ.app M))
          ((SheafOfModules.toSheaf (ring.{u + 1, u, u + 1}
            (Scheme.ProEt.topology X) (coefficients l E X m))).map
              ((transition.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
                (coefficients l E X) (transitions l E X) h).app M)) := by
  let T := transition.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
    (coefficients l E X) (transitions l E X) h
  have hκ := finiteConstantIso_hom_coefficientMap l E X h
  refine ⟨
    { app := fun M ↦ finiteUnrealizationSemilinearMap X _ _ hκ (T.app M)
      naturality := fun M M' g ↦ finiteUnrealizationSemilinearMap_naturality X _ _ hκ _ _ _ _
        (T.naturality g) },
    fun M ↦ finiteUnrealizationSemilinearMap_forget X _ _ hκ (T.app M), fun δ' hδ' ↦ ?_⟩
  refine NatTrans.ext (funext fun M ↦ ?_)
  apply (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ (ModuleCat.{u + 1} (Etale.FiniteProperQuotient.Ring l E m))
      AddCommGrpCat.{u + 1})).map_injective
  exact eq_of_heq ((hδ' M).trans (finiteUnrealizationSemilinearMap_forget X _ _ hκ (T.app M)).symm)

/-- The uniquely normalized fixed-coefficient horizontal map.
Source: Zheng 4.1 (blueprint: def-sfb-finite-coefficient-system-evaluation). -/
def fixedTransition (X : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :=
  (fixedTransition_existsUnique l E X h).exists.choose

/-- Derived descent of the original horizontal map, including the localization compositors.
Source: Zheng 4.1 (blueprint: def-sfb-finite-coefficient-system-evaluation). -/
def fixedDerivedTransition (X : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    fixedDerivedEvaluation l E X m ⟶ fixedDerivedEvaluation l E X n ⋙
      Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X)
        (Etale.FiniteProperQuotient.quotient l E h) :=
  (Functor.mapDerivedCategoryCompIso
    (evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (coefficients l E X) (transitions l E X) m)
    (finiteUnrealization X (Etale.FiniteProperQuotient.Ring l E m))).hom ≫
  Functor.mapDerivedCategoryNatTrans (fixedTransition l E X h) ≫
  (Functor.mapDerivedCategoryCompIso
    (fixedEvaluation l E X n)
    (Sheaf.restrictScalars (Scheme.ProEt.topology X)
      (Etale.FiniteProperQuotient.quotient l E h))).inv ≫
  Functor.whiskerRight (Functor.mapDerivedCategoryCompIso
    (evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (coefficients l E X) (transitions l E X) n)
    (finiteUnrealization X (Etale.FiniteProperQuotient.Ring l E n))).inv
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X)
      (Etale.FiniteProperQuotient.quotient l E h))

/-- Scalar-adjunction transpose of that map: the actual derived reduction of a system.
Source: Zheng 4.1 (blueprint: def-sfb-finite-coefficient-system-evaluation). -/
def fixedReduction (X : Scheme.{u}) {m n : ℕ} (h : n ≤ m)
    (M : DS.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (coefficients l E X) (transitions l E X)) :
    (CategoryTheory.Sheaf.fixedCoefficientDerivedScalarExtension
      (Scheme.ProEt.topology X)
      (Etale.FiniteProperQuotient.quotient l E h)).obj
        ((fixedDerivedEvaluation l E X m).obj M) ⟶
      (fixedDerivedEvaluation l E X n).obj M :=
  letI := CategoryTheory.Sheaf.fixedCoefficientDerivedRestriction_isRightAdjoint
    (Scheme.ProEt.topology X) (Etale.FiniteProperQuotient.quotient l E h)
  ((Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X)
      (Etale.FiniteProperQuotient.quotient l E h))).homEquiv _ _).symm
    ((fixedDerivedTransition l E X h).app M)

end AlgebraicGeometry.ProEtale.CoherentReduction
