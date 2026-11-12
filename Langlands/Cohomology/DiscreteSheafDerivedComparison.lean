import Langlands.Cohomology.DiscreteSheafDerivedComplex
import Langlands.Cohomology.DerivedExactComposition
import Langlands.Cohomology.AcyclicResolution.DerivedCompositeComparison
import Langlands.Cohomology.ExtendMap

/-!
# Derived comparison for equivariant compactly supported cohomology

A natural transformation of additive functors induces a natural transformation of
their derived complexes. On a twisted site with points compatible with the group
action, the derived complex of smooth compactly supported global sections of a
discrete sheaf, with the group action forgotten, maps to the derived complex of
compactly supported sections of its restriction to the site over `X`: the
derived-category form of the maps `H^q_c(X{G}, F) → H^q_c(X, b^*F)`.
-/

noncomputable section

namespace Langlands.Cohomology.DiscreteSheafDerivedComparison

open CategoryTheory CategoryTheory.Limits
open Langlands.Cohomology.AcyclicResolution

universe w w₁ w₂ w₃ w₄ vC vD uC uD v u uG uI

section NatTrans

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  [HasDerivedCategory.{w₁} C] [EnoughInjectives C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  {G H : C ⥤ D} [G.Additive] [H.Additive] (τ : G ⟶ H)

/-- A natural transformation of additive functors on the localized image of an
arbitrary natural-indexed complex. -/
def resolutionNatTrans : derivedResolutionFunctor G ⟶ derivedResolutionFunctor H :=
  Functor.whiskerLeft (ComplexShape.embeddingUpNat.extendFunctor C)
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ))
      DerivedCategory.Q)

/-- The map of derived complexes induced by `τ`, computed with a specified
injective resolution. -/
def derivedComplexMapOfResolution {X : C} (I : InjectiveResolution X) :
    (DerivedPlus.derivedComplex G ⋙ DerivedCategory.Plus.ι).obj X ⟶
      (DerivedPlus.derivedComplex H ⋙ DerivedCategory.Plus.ι).obj X :=
  (derivedResolutionIso G I).hom ≫ (resolutionNatTrans τ).app I.cocomplex ≫
    (derivedResolutionIso H I).inv

set_option backward.isDefEq.respectTransparency false in
/-- The resolution formula commutes with every morphism of injective
resolutions over a coefficient morphism. -/
@[reassoc]
theorem derivedComplexMapOfResolution_naturality
    {X Y : C} {f : X ⟶ Y} {I : InjectiveResolution X} {J : InjectiveResolution Y}
    (φ : InjectiveResolution.Hom I J f) :
    (DerivedPlus.derivedComplex G ⋙ DerivedCategory.Plus.ι).map f ≫
        derivedComplexMapOfResolution τ J =
      derivedComplexMapOfResolution τ I ≫
        (DerivedPlus.derivedComplex H ⋙ DerivedCategory.Plus.ι).map f := by
  have h₁ := derivedResolutionIso_hom_naturality G φ
  have h₂ := (resolutionNatTrans τ).naturality φ.hom
  have h₃ := derivedResolutionIso_hom_naturality H φ
  have h₃' :
      (derivedResolutionFunctor H).map φ.hom ≫ (derivedResolutionIso H J).inv =
        (derivedResolutionIso H I).inv ≫
          (DerivedPlus.derivedComplex H ⋙ DerivedCategory.Plus.ι).map f := by
    rw [← cancel_mono (derivedResolutionIso H J).hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [h₃, Iso.inv_hom_id_assoc]
  simp only [derivedComplexMapOfResolution, Category.assoc]
  rw [← Category.assoc, h₁, Category.assoc,
    ← Category.assoc ((derivedResolutionFunctor G).map φ.hom), h₂, Category.assoc, h₃']

/-- The map is independent of the injective resolution used to compute it. -/
theorem derivedComplexMapOfResolution_eq {X : C} (I J : InjectiveResolution X) :
    derivedComplexMapOfResolution τ I = derivedComplexMapOfResolution τ J := by
  have h := derivedComplexMapOfResolution_naturality τ (DerivedPlus.descHom (𝟙 X) I J)
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id] at h
  exact h.symm

/-- A natural transformation of additive functors induces a natural
transformation of their derived complexes in the unbounded derived category. -/
def derivedComplexMap :
    DerivedPlus.derivedComplex G ⋙ DerivedCategory.Plus.ι ⟶
      DerivedPlus.derivedComplex H ⋙ DerivedCategory.Plus.ι where
  app X := derivedComplexMapOfResolution τ (injectiveResolution X)
  naturality _ _ f := derivedComplexMapOfResolution_naturality τ (DerivedPlus.descHom f _ _)

/-- Every injective resolution computes the component of `derivedComplexMap`. -/
theorem derivedComplexMap_app {X : C} (I : InjectiveResolution X) :
    (derivedComplexMap τ).app X = derivedComplexMapOfResolution τ I :=
  derivedComplexMapOfResolution_eq τ _ I

omit [HasDerivedCategory C] [EnoughInjectives C] in
set_option backward.isDefEq.respectTransparency false in
/-- On cohomology, the localized map induced by `τ` on the image of a complex is
the map induced on the cohomology of the original natural-indexed images. -/
@[reassoc]
lemma derivedResolutionHomologyIso_hom_natTrans (K : CochainComplex C ℕ) (n : ℕ) :
    (DerivedCategory.homologyFunctor D (n : ℤ)).map ((resolutionNatTrans τ).app K) ≫
        (derivedResolutionHomologyIso H K n).hom =
      (derivedResolutionHomologyIso G K n).hom ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℕ)).app K) n := by
  have h₁ := (DerivedCategory.homologyFunctorFactors D (n : ℤ)).hom.naturality
    ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app
      (K.extend ComplexShape.embeddingUpNat))
  have h₂ := extendMapIso_hom_app ComplexShape.embeddingUpNat τ K
  have h₃ := HomologicalComplex.extendHomologyIso_hom_naturality
    ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℕ)).app K) ComplexShape.embeddingUpNat
    (j := n) (j' := (n : ℤ)) rfl
  have h₄ : HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app
          (K.extend ComplexShape.embeddingUpNat)) (n : ℤ) ≫
        HomologicalComplex.homologyMap
          (DerivedPlus.mapExtendIso H K ComplexShape.embeddingUpNat).inv (n : ℤ) =
      HomologicalComplex.homologyMap
          (DerivedPlus.mapExtendIso G K ComplexShape.embeddingUpNat).inv (n : ℤ) ≫
        HomologicalComplex.homologyMap
          (HomologicalComplex.extendMap
            ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℕ)).app K)
            ComplexShape.embeddingUpNat) (n : ℤ) :=
    (HomologicalComplex.homologyMap_comp _ _ _).symm.trans
      ((congrArg (fun f => HomologicalComplex.homologyMap f (n : ℤ)) h₂).trans
        (HomologicalComplex.homologyMap_comp _ _ _))
  simp only [Functor.comp_map] at h₁
  simp only [resolutionNatTrans, derivedResolutionHomologyIso, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom]
  erw [reassoc_of% h₁, reassoc_of% h₄, h₃]
  simp only [Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- On cohomology in degree `n`, the map of derived complexes induced by `τ` is
Mathlib's `NatTrans.rightDerived τ n`, through the published identifications
`DerivedPlus.homologyIso` computed with the same injective resolution. -/
@[reassoc]
theorem derivedComplexMapOfResolution_homology {X : C} (I : InjectiveResolution X) (n : ℕ) :
    (DerivedCategory.homologyFunctor D (n : ℤ)).map (derivedComplexMapOfResolution τ I) ≫
        (DerivedPlus.homologyIso H I n).hom =
      (DerivedPlus.homologyIso G I n).hom ≫ (NatTrans.rightDerived τ n).app X := by
  rw [← derivedResolutionIso_homology H I n, ← derivedResolutionIso_homology G I n,
    InjectiveResolution.rightDerived_app_eq τ I n]
  simp only [derivedComplexMapOfResolution, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc (DerivedCategory.homologyFunctor D (n : ℤ))
      (derivedResolutionIso H I).inv (derivedResolutionIso H I).hom,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp,
    derivedResolutionHomologyIso_hom_natTrans_assoc, Iso.inv_hom_id_assoc]
  rfl

/-- On cohomology in degree `n`, `derivedComplexMap τ` is `NatTrans.rightDerived τ n`. -/
@[reassoc]
theorem derivedComplexMap_homology (X : C) (n : ℕ) :
    (DerivedCategory.homologyFunctor D (n : ℤ)).map ((derivedComplexMap τ).app X) ≫
        (DerivedPlus.homologyIso H (injectiveResolution X) n).hom =
      (DerivedPlus.homologyIso G (injectiveResolution X) n).hom ≫
        (NatTrans.rightDerived τ n).app X :=
  derivedComplexMapOfResolution_homology τ (injectiveResolution X) n

end NatTrans

section Compact

open Langlands.Sheaf.Equivariant Langlands.Sheaf.PointSupport
open Langlands.Sheaf.Equivariant.TwistedOver Langlands.Cohomology.DiscreteSheafDerivedComplex

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} [P.RespectsIso] {X : C}
variable {G : Type uG} [Group G] {ρ : G →* Aut X}
variable (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]
variable (R : Type w) [CommRing R] [TopologicalSpace G]
variable (L : LocalActionSystem (TwistedOver P ρ) G)

/-- Restriction of discrete sheaves on the twisted site to the site over `X`. -/
abbrev discreteRestriction :
    L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J) ⥤ Sheaf J (ModuleCat.{w} R) :=
  L.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J) ⋙
    restriction ρ J (ModuleCat.{w} R)

variable [HasSheafify J (ModuleCat.{w} R)]
variable [HasSheafify (twistedTopology ρ J) (ModuleCat.{w} R)]
variable [L.HasFiniteEquivariantRefinements (twistedTopology ρ J)]
variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R, (ι P ρ).op.HasPointwiseRightKanExtension F]
variable [EnoughInjectives (Sheaf (twistedTopology ρ J) (ModuleCat.{w} R))]

/-- The positive right derived functors of the exact restriction functor vanish. -/
theorem isZero_discreteRestriction_rightDerived
    (F : L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J)) (q : ℕ) :
    IsZero (((discreteRestriction J R L).rightDerived (q + 1)).obj F) :=
  Langlands.AlgebraicGeometry.Modules.DerivedSections.isZero_rightDerived_succ_of_preservesHomology
    (discreteRestriction J R L) F q

variable {I : Type uI} [TopologicalSpace I] {Φ : I → J.Point.{w}}
variable [P.ContainsIdentities] [LocallySmall.{w} (P.Over ⊤ X)]
variable [EnoughInjectives (Sheaf J (ModuleCat.{w} R))]
variable [HasDerivedCategory.{w₁} (L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J))]
variable [HasDerivedCategory.{w₂} (Sheaf J (ModuleCat.{w} R))]
variable [HasDerivedCategory.{w₄} (ModuleCat.{w} R)]

variable (Φ) in
/-- The derived composite comparison for the exact restriction functor: from the
derived complex of compactly supported sections over `X` of the restriction, as a
functor of the discrete sheaf, to the derived complex of compactly supported
sections evaluated at the restriction. -/
def restrictionCompactComparison :
    DerivedPlus.derivedComplex
        (discreteRestriction J R L ⋙ sheafCompactSections J Φ R (base P ρ).obj) ⋙
          DerivedCategory.Plus.ι ⟶
      discreteRestriction J R L ⋙
        (sheafCompactComplex J Φ R (base P ρ).obj ⋙ DerivedCategory.Plus.ι) where
  app F := derivedCompComparison (sheafCompactSections J Φ R (base P ρ).obj)
    (Iso.refl (discreteRestriction J R L ⋙ sheafCompactSections J Φ R (base P ρ).obj)) F
    (isZero_discreteRestriction_rightDerived J R L F)
  naturality _ _ f := derivedCompComparison_naturality (sheafCompactSections J Φ R (base P ρ).obj)
    (Iso.refl (discreteRestriction J R L ⋙ sheafCompactSections J Φ R (base P ρ).obj)) f
    (isZero_discreteRestriction_rightDerived J R L _)
    (isZero_discreteRestriction_rightDerived J R L _)

variable [MulAction G I] [ContinuousConstSMul G I] [IsTopologicalGroup G]

set_option backward.isDefEq.respectTransparency false in
/-- On cohomology in degree `n`, the map induced by `smoothCompactInclusion`
followed by the derived composite comparison for restriction is the published
`compactComparison J R L E n`, precomposed with the comparison
`LeftExactHomology.derivedNatTrans` for the exact functor `smoothForget`, which
that construction inverts. -/
@[reassoc]
theorem inclusionRestrictionComparison_homology (E : PointEquivariance ρ Φ)
    (F : L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J)) (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{w} R) (n : ℤ)).map
        ((derivedComplexMap (smoothCompactInclusion J R L E)).app F ≫
          (restrictionCompactComparison J R L Φ).app F) ≫
        (DerivedPlus.homologyIso (sheafCompactSections J Φ R (base P ρ).obj)
          (injectiveResolution ((discreteRestriction J R L).obj F)) n).hom =
      (DerivedPlus.homologyIso (discreteCompactSections J R L E ⋙ smoothForget R G)
          (injectiveResolution F) n).hom ≫
        (LeftExactHomology.derivedNatTrans (smoothForget R G)
          (discreteCompactSections J R L E) n).app F ≫
        (compactComparison J R L E n).app F := by
  have h := derivedCompComparison_homology (sheafCompactSections J Φ R (base P ρ).obj)
    (Iso.refl (discreteRestriction J R L ⋙ sheafCompactSections J Φ R (base P ρ).obj)) F
    (isZero_discreteRestriction_rightDerived J R L F) n
  have h' := derivedComplexMap_homology (smoothCompactInclusion J R L E) F n
  rw [Functor.map_comp, Category.assoc]
  erw [h, reassoc_of% h']
  congr 1
  simp only [compactComparison, ExactBaseChange.baseChangeNatTrans, NatTrans.comp_app,
    NatIso.isIso_inv_app, IsIso.hom_inv_id_assoc, ExactBaseChange.compComparisonNatTrans_app]

variable [HasDerivedCategory.{w₃} (SmoothRep.{w, uG, w} R G)]

/-- The derived comparison from the derived complex of smooth compactly supported
global sections of a discrete sheaf, with the action of `G` forgotten, to the
derived complex of compactly supported sections over `X` of its restriction to
the site over `X`. It is the exact postcomposition isomorphism for `smoothForget`,
followed by the map induced by `smoothCompactInclusion` and the derived composite
comparison for the exact restriction functor. -/
def compactComplexComparison (E : PointEquivariance ρ Φ) :
    (compactComplex J R L E ⋙ DerivedCategory.Plus.ι) ⋙
        (smoothForget R G).mapDerivedCategory ⟶
      discreteRestriction J R L ⋙
        (sheafCompactComplex J Φ R (base P ρ).obj ⋙ DerivedCategory.Plus.ι) :=
  (DerivedPlus.derivedPostcompIso (discreteCompactSections J R L E) (smoothForget R G)).hom ≫
    derivedComplexMap (smoothCompactInclusion J R L E) ≫ restrictionCompactComparison J R L Φ

end Compact

end Langlands.Cohomology.DiscreteSheafDerivedComparison
