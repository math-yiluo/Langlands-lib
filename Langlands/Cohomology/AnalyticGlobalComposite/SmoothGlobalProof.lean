import Langlands.Cohomology.AnalyticGlobalComposite.InvariantsHom
import Langlands.Cohomology.EquivariantComposite.GlobalProof

/-! # Composite comparison for injective-preserving smooth section functors -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Cohomology.EquivariantComposite

namespace Langlands.Cohomology.AnalyticGlobalComposite

universe w wC uR uG uC vC

variable (R : Type uR) [CommRing R] (G : Type uG) [Group G] [TopologicalSpace G]
  {C : Type uC} [Category.{vC} C] [Abelian C] [EnoughInjectives C]
  [HasDerivedCategory.{wC} C]
  [HasDerivedCategory.{w} (SmoothRep.{uR, uG, uR} R G)]
  (S : C ⥤ SmoothRep.{uR, uG, uR} R G) [S.Additive] [S.PreservesInjectiveObjects]

/-- Sections of an extended injective resolution form a K-injective smooth representation complex. -/
instance smoothSectionResolution_isKInjective {F : C}
    (I : InjectiveResolution F) :
    CochainComplex.IsKInjective
      ((S.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex) := by
  have (n : ℤ) : Injective
      (((S.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).X n) := S.injective_obj_of_injective
      (inferInstanceAs (Injective (I.cochainComplex.X n)))
  exact CochainComplex.isKInjective_of_injective _ 0

/-- The global composite comparison computed using a specified injective resolution. -/
def smoothGlobalComparisonOfResolution {F : C}
    (I : InjectiveResolution F) (n : ℕ) :
    ((S ⋙ smoothInvariantsFunctor R G).rightDerived n).obj F ≃+
      ShiftedHom ((DerivedCategory.singleFunctor (SmoothRep.{uR, uG, uR} R G) 0).obj (trivialSmoothRep R G))
        (DerivedCategory.Plus.ι.obj ((DerivedPlus.derivedComplex S).obj F))
        (n : ℤ) :=
  (((forget₂ (ModuleCat.{uR} R) AddCommGrpCat).mapIso
    (resolutionRightDerivedIso (S ⋙ smoothInvariantsFunctor R G)
      I n).symm).addCommGroupIsoToAddEquiv).trans
    (((invariantsHomologyIso R G (.up ℤ) (n : ℤ)).app
      ((S.mapHomologicalComplex (.up ℤ)).obj
        I.cochainComplex)).addCommGroupIsoToAddEquiv.trans
      ((homologyDerivedAddEquiv (trivialSmoothRep R G)
        ((S.mapHomologicalComplex (.up ℤ)).obj
          I.cochainComplex) (n : ℤ)).trans
        { toEquiv := ((shiftFunctor (DerivedCategory (SmoothRep.{uR, uG, uR} R G)) (n : ℤ)).mapIso
            (AcyclicResolution.derivedResolutionIso S I).symm).homToEquiv
          map_add' := fun _ _ => CategoryTheory.Preadditive.add_comp _ _ _ _ _ _ }))

/-- The comparison is natural with respect to a map of injective resolutions. -/
lemma smoothGlobalComparisonOfResolution_naturality
    {F F' : C} {f : F ⟶ F'}
    {I : InjectiveResolution F} {J : InjectiveResolution F'}
    (φ : InjectiveResolution.Hom I J f) (n : ℕ)
    (x : ((S ⋙ smoothInvariantsFunctor R G).rightDerived n).obj F) :
    smoothGlobalComparisonOfResolution R G S J n
        (((S ⋙ smoothInvariantsFunctor R G).rightDerived n).map f x) =
      smoothGlobalComparisonOfResolution R G S I n x ≫ (DerivedCategory.Plus.ι.map
        ((DerivedPlus.derivedComplex S).map f))⟦(n : ℤ)⟧' := by
  let T := (S ⋙ smoothInvariantsFunctor R G)
  let K := (S.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let L := (S.mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
  let g := (S.mapHomologicalComplex (.up ℤ)).map φ.hom'
  have h₁ : (T.rightDerived n).map f ≫ (resolutionRightDerivedIso T J n).inv =
      (resolutionRightDerivedIso T I n).inv ≫
        HomologicalComplex.homologyMap ((T.mapHomologicalComplex (.up ℤ)).map φ.hom')
          (n : ℤ) := by
    rw [← cancel_epi (resolutionRightDerivedIso T I n).hom, ← Category.assoc,
      ← resolutionRightDerivedIso_hom_naturality T φ n, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  have h₂ := (invariantsHomologyIso R G (.up ℤ) (n : ℤ)).hom.naturality g
  have h₃ : DerivedCategory.Q.map g ≫
        (AcyclicResolution.derivedResolutionIso S J).inv =
      (AcyclicResolution.derivedResolutionIso S I).inv ≫
        (DerivedPlus.derivedComplex S ⋙ DerivedCategory.Plus.ι).map f := by
    rw [← cancel_mono (AcyclicResolution.derivedResolutionIso S J).hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [AcyclicResolution.derivedResolutionIso_hom_naturality S φ,
      Iso.inv_hom_id_assoc]
    rfl
  have h₁x := ConcreteCategory.congr_hom h₁ x
  have h₂x := ConcreteCategory.congr_hom h₂ ((resolutionRightDerivedIso T I n).inv x)
  change homologyDerivedAddEquiv (trivialSmoothRep R G) L (n : ℤ)
      ((invariantsHomologyIso R G (.up ℤ) (n : ℤ)).hom.app L
        ((resolutionRightDerivedIso T J n).inv ((T.rightDerived n).map f x))) ≫
        (AcyclicResolution.derivedResolutionIso S J).inv⟦(n : ℤ)⟧' =
    (homologyDerivedAddEquiv (trivialSmoothRep R G) K (n : ℤ)
      ((invariantsHomologyIso R G (.up ℤ) (n : ℤ)).hom.app K
        ((resolutionRightDerivedIso T I n).inv x)) ≫
        (AcyclicResolution.derivedResolutionIso S I).inv⟦(n : ℤ)⟧') ≫
      ((DerivedPlus.derivedComplex S ⋙ DerivedCategory.Plus.ι).map f)⟦(n : ℤ)⟧'
  erw [h₁x, h₂x, homologyDerivedAddEquiv_naturality (trivialSmoothRep R G) g (n : ℤ)]
  rw [Category.assoc, ← Functor.map_comp, h₃, Functor.map_comp, ← Category.assoc]
  rfl

/-- The natural composite comparison for any additive section functor preserving injectives. -/
theorem smoothGlobalComposite (n : ℕ) :
    ∃ e : ∀ F : C, ((S ⋙ smoothInvariantsFunctor R G).rightDerived n).obj F ≃+
        ShiftedHom
          ((DerivedCategory.singleFunctor (SmoothRep.{uR, uG, uR} R G) 0).obj
            (trivialSmoothRep R G))
          (DerivedCategory.Plus.ι.obj ((DerivedPlus.derivedComplex S).obj F)) (n : ℤ),
      ∀ {F F' : C} (f : F ⟶ F')
        (x : ((S ⋙ smoothInvariantsFunctor R G).rightDerived n).obj F),
        e F' (((S ⋙ smoothInvariantsFunctor R G).rightDerived n).map f x) =
          e F x ≫ (DerivedCategory.Plus.ι.map
            ((DerivedPlus.derivedComplex S).map f))⟦(n : ℤ)⟧' := by
  refine ⟨fun F => smoothGlobalComparisonOfResolution R G S (injectiveResolution F) n, ?_⟩
  intro F F' f x
  exact smoothGlobalComparisonOfResolution_naturality R G S
    (DerivedPlus.descHom f (injectiveResolution F) (injectiveResolution F')) n x

end Langlands.Cohomology.AnalyticGlobalComposite
