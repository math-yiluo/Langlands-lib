import Langlands.Geometry.EtaleDeckAction
import Langlands.Shimura.Coefficients.HarrisEtaleDerivedPullback

/-! # Canonical deck actions on the full restricted Harris coefficient system -/

noncomputable section

universe u t wX wZ wT

namespace Langlands.Shimura.Coefficients

open CategoryTheory AlgebraicGeometry Opposite Langlands.Global
open Langlands.Geometry Langlands.Geometry.EtaleCohomologyAction
open Langlands.Cohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {A : Type u} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
variable {L : Type u} [Field L] [NumberField L]
variable {W : Type u} [AddCommGroup W] [Module L W] [Module.Finite L W]
variable {σ : AlgebraInvolution ℚ A} (ρ : (σ.baseChange L).AlgebraicRepresentation W)
variable (p : FinitePlace ℚ) (U : CompactOpenLevel σ.FiniteAdelicPoints) (m : ℕ)
variable (X : Scheme.{u})
variable (Y : EquivariantDiagram (harrisCongruenceGroups ρ p U m) X.Etale)
variable (hY : ∀ n, IsFiniteGeometricTorsor X (Y.action n))

local notation "R" => HarrisCoefficientIntegers L p
local notation "M" => harrisCoefficientDiagram ρ p U m
local notation "C" => harrisEtaleCoefficientSystem ρ p U m X Y hY

variable {G : Type t} [Group G] {Z : Scheme.{u}}
variable (τ : G →* (Aut Z)ᵐᵒᵖ) (f : Z ⟶ X) [Etale f]
variable (hf : ∀ g, (aut τ g).hom ≫ f = f)

/-- The full actual Harris system with canonical deck equivariance of every
restricted coefficient and transition, constructed from the geometric deck law. -/
def harrisEtaleDeckCoefficientSystem : ℕᵒᵖ ⥤ EquivariantSheaf R τ :=
  C ⋙ deckEquivariantFunctor R τ f hf

/-- Forgetting coefficient equivariance gives the existing restricted system. -/
def harrisEtaleDeckCoefficientForgetIso :
    harrisEtaleDeckCoefficientSystem ρ p U m X Y hY τ f hf ⋙
        TranslationAction.Equivariant.forget ≅
      harrisEtaleRestrictedCoefficientSystem ρ p U m X Y hY f := Iso.refl _

/-- Every coefficient arrow is the actual restricted Harris arrow. -/
@[simp] theorem harrisEtaleDeckCoefficientSystem_map_hom
    {i j : ℕᵒᵖ} (a : i ⟶ j) :
    ((harrisEtaleDeckCoefficientSystem ρ p U m X Y hY τ f hf).map a).hom =
      (harrisEtaleRestrictedCoefficientSystem ρ p U m X Y hY f).map a := rfl

/-- In particular, the original lattice reduction and inverse torsor comparison
remain the two factors of every underlying coefficient transition. -/
theorem harrisEtaleDeckCoefficientSystem_map_factors {i j : ℕᵒᵖ} (a : i ⟶ j) :
    ((harrisEtaleDeckCoefficientSystem ρ p U m X Y hY τ f hf).map a).hom =
      (EtalePullback.restriction f (ModuleCat.{u} R)).map
          ((etaleAssociatedReduction X Y a).app M) ≫
        (EtalePullback.restriction f (ModuleCat.{u} R)).map
          ((etaleAssociatedComparisonIso X Y hY a).inv.app M) :=
  harrisEtaleRestrictedCoefficientSystem_map ρ p U m X Y hY f a

/-- The full source section system with canonical trivial geometric action. -/
def harrisEtaleTrivialSectionsSystem : ℕᵒᵖ ⥤ Action (ModuleCat.{u} R) G :=
  C ⋙ trivialEquivariantFunctor X R G ⋙ pullbackSectionsFunctor R 1

/-- The full source cohomology system with canonical trivial equivariance. -/
def harrisEtaleTrivialCohomologySystem (q : ℕ) :
    ℕᵒᵖ ⥤ Action (ModuleCat.{u} R) G :=
  C ⋙ trivialEquivariantFunctor X R G ⋙ pullbackCohomologyFunctor R 1 q

/-- Ordinary sections with the constructed deck actions at every exponent. -/
def harrisEtaleDeckSectionsSystem : ℕᵒᵖ ⥤ Action (ModuleCat.{u} R) G :=
  C ⋙ deckSectionsFunctor R τ f hf

/-- Ordinary cohomology with deck actions and every coefficient transition. -/
def harrisEtaleDeckCohomologySystem (q : ℕ) : ℕᵒᵖ ⥤ Action (ModuleCat.{u} R) G :=
  C ⋙ deckCohomologyFunctor R τ f hf q

/-- Geometric restriction of the whole section system is equivariant. -/
def harrisEtaleDeckSectionsPullback :
    harrisEtaleTrivialSectionsSystem (G := G) ρ p U m X Y hY ⟶
      harrisEtaleDeckSectionsSystem ρ p U m X Y hY τ f hf :=
  Functor.whiskerLeft C (deckSectionsMap R τ f hf)

/-- Geometric restriction of the whole cohomology system is equivariant. -/
def harrisEtaleDeckCohomologyPullback (q : ℕ) :
    harrisEtaleTrivialCohomologySystem (G := G) ρ p U m X Y hY q ⟶
      harrisEtaleDeckCohomologySystem ρ p U m X Y hY τ f hf q :=
  Functor.whiskerLeft C (deckCohomologyMap R τ f hf q)

/-- Forgetting the section action gives the existing restricted section system. -/
def harrisEtaleDeckSectionsForgetIso :
    harrisEtaleDeckSectionsSystem ρ p U m X Y hY τ f hf ⋙ Action.forget _ G ≅
      harrisEtaleRestrictedSectionsSystem ρ p U m X Y hY f :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun {i j} a => by
    dsimp only [Iso.refl_hom]
    rw [Category.comp_id, Category.id_comp]
    exact pullbackSectionsFunctor_map_hom R τ
      ((harrisEtaleDeckCoefficientSystem ρ p U m X Y hY τ f hf).map a))

/-- Forgetting the cohomology action gives the existing restricted system. -/
def harrisEtaleDeckCohomologyForgetIso (q : ℕ) :
    harrisEtaleDeckCohomologySystem ρ p U m X Y hY τ f hf q ⋙ Action.forget _ G ≅
      harrisEtaleRestrictedCohomologySystem ρ p U m X Y hY f q := Iso.refl _

/-- Underlying section pullback is exactly the previously constructed map. -/
@[simp] theorem harrisEtaleDeckSectionsPullback_app_hom (n : ℕᵒᵖ) :
    ((harrisEtaleDeckSectionsPullback ρ p U m X Y hY τ f hf).app n).hom =
      (harrisEtaleSectionsPullback ρ p U m X Y hY f).app n :=
  deckSectionsMap_app_hom R τ f hf ((C).obj n)

/-- Underlying cohomology pullback is exactly the previously constructed map. -/
@[simp] theorem harrisEtaleDeckCohomologyPullback_app_hom (q : ℕ) (n : ℕᵒᵖ) :
    ((harrisEtaleDeckCohomologyPullback ρ p U m X Y hY τ f hf q).app n).hom =
      (harrisEtaleCohomologyPullback ρ p U m X Y hY f q).app n :=
  deckCohomologyMap_app_hom R τ f hf ((C).obj n) q

variable [HasDerivedCategory.{wX} (EtaleDerivedSections.ModuleSheaf X (HarrisCoefficientIntegers L p))]
  [HasDerivedCategory.{wZ} (EtaleDerivedSections.ModuleSheaf Z (HarrisCoefficientIntegers L p))]
  [HasDerivedCategory.{wT} (ModuleCat.{u} (HarrisCoefficientIntegers L p))]

/-- The original Harris derived system with constructed trivial source action. -/
def harrisEtaleTrivialDerivedPlusSystem :
    ℕᵒᵖ ⥤ Action (DerivedCategory.Plus (ModuleCat.{u} R)) G :=
  C ⋙ trivialEquivariantFunctor X R G ⋙ pullbackDerivedSectionsFunctor R 1

/-- The actual full restricted Harris derived system with canonical deck action. -/
def harrisEtaleDeckDerivedPlusSystem :
    ℕᵒᵖ ⥤ Action (DerivedCategory.Plus (ModuleCat.{u} R)) G :=
  C ⋙ deckDerivedSectionsFunctor R τ f hf

/-- The source action is actually the identity, by derived geometric identity. -/
theorem harrisEtaleTrivialDerivedPlusSystem_ρ (n : ℕᵒᵖ) (g : G) :
    ((harrisEtaleTrivialDerivedPlusSystem (G := G) ρ p U m X Y hY).obj n).ρ g =
      𝟙 ((harrisEtaleDerivedPlusSystem ρ p U m X Y hY).obj n) :=
  trivialEquivariantDerivedAction R ((C).obj n) g

omit [HasDerivedCategory.{wX} (EtaleDerivedSections.ModuleSheaf X (HarrisCoefficientIntegers L p))] in
/-- The deck action is actual geometric derived pullback followed by the
derived map of the canonically constructed coefficient structure morphism. -/
theorem harrisEtaleDeckDerivedPlusSystem_ρ (n : ℕᵒᵖ) (g : G) :
    ((harrisEtaleDeckDerivedPlusSystem ρ p U m X Y hY τ f hf).obj n).ρ g =
      (EtalePullback.derivedSectionsMap (aut τ g).hom R).app
          ((harrisEtaleRestrictedCoefficientSystem ρ p U m X Y hY f).obj n) ≫
        (EtaleDerivedSectionsPlus.derivedSections Z R).map
          (((harrisEtaleDeckCoefficientSystem ρ p U m X Y hY τ f hf).obj n).act g) := rfl

omit [HasDerivedCategory.{wX} (EtaleDerivedSections.ModuleSheaf X (HarrisCoefficientIntegers L p))] in
/-- Each derived coefficient transition is the existing restricted transition. -/
@[simp] theorem harrisEtaleDeckDerivedPlusSystem_map_hom
    {i j : ℕᵒᵖ} (a : i ⟶ j) :
    ((harrisEtaleDeckDerivedPlusSystem ρ p U m X Y hY τ f hf).map a).hom =
      (harrisEtaleRestrictedDerivedPlusSystem ρ p U m X Y hY f).map a := rfl

/-- Geometric derived pullback of the full Harris system, as a map of actions. -/
def harrisEtaleDeckDerivedPlusPullback :
    harrisEtaleTrivialDerivedPlusSystem (G := G) ρ p U m X Y hY ⟶
      harrisEtaleDeckDerivedPlusSystem ρ p U m X Y hY τ f hf :=
  Functor.whiskerLeft C (deckDerivedSectionsMap R τ f hf)

/-- Forgetting the source derived action recovers the original Harris system. -/
def harrisEtaleTrivialDerivedPlusForgetIso :
    harrisEtaleTrivialDerivedPlusSystem (G := G) ρ p U m X Y hY ⋙ Action.forget _ G ≅
      harrisEtaleDerivedPlusSystem ρ p U m X Y hY := Iso.refl _

/-- Forgetting deck actions recovers the previously constructed restricted system. -/
def harrisEtaleDeckDerivedPlusForgetIso :
    harrisEtaleDeckDerivedPlusSystem ρ p U m X Y hY τ f hf ⋙ Action.forget _ G ≅
      harrisEtaleRestrictedDerivedPlusSystem ρ p U m X Y hY f := Iso.refl _

/-- Its underlying derived map is precisely existing actual geometric pullback. -/
@[simp] theorem harrisEtaleDeckDerivedPlusPullback_app_hom (n : ℕᵒᵖ) :
    ((harrisEtaleDeckDerivedPlusPullback ρ p U m X Y hY τ f hf).app n).hom =
      (harrisEtaleDerivedPlusPullback ρ p U m X Y hY f).app n :=
  deckDerivedSectionsMap_app_hom R τ f hf ((C).obj n)

/-- Every deck element fixes the actual Harris derived pullback map. -/
theorem harrisEtaleDeckDerivedPlusPullback_invariant (n : ℕᵒᵖ) (g : G) :
    (harrisEtaleDerivedPlusPullback ρ p U m X Y hY f).app n ≫
        ((harrisEtaleDeckDerivedPlusSystem ρ p U m X Y hY τ f hf).obj n).ρ g =
      (harrisEtaleDerivedPlusPullback ρ p U m X Y hY f).app n := by
  have h := deckDerivedSectionsMap_invariant R τ f hf ((C).obj n) g
  rw [deckDerivedSectionsMap_app_hom] at h
  exact h

/-- Canonical equivariant cohomology recovery, natural in every exponent. -/
def harrisEtaleDeckDerivedPlusCohomologyIso (q : ℕ) :
    harrisEtaleDeckDerivedPlusSystem ρ p U m X Y hY τ f hf ⋙
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).mapAction G ≅
      harrisEtaleDeckCohomologySystem ρ p U m X Y hY τ f hf q :=
  NatIso.ofComponents (fun n => (deckDerivedHomologyIso R τ f hf q).app ((C).obj n))
    (fun {_ _} a => (deckDerivedHomologyIso R τ f hf q).hom.naturality ((C).map a))

/-- Canonical equivariant section recovery in degree zero for the whole system. -/
def harrisEtaleDeckDerivedPlusZeroIso :
    harrisEtaleDeckDerivedPlusSystem ρ p U m X Y hY τ f hf ⋙
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).mapAction G ≅
      harrisEtaleDeckSectionsSystem ρ p U m X Y hY τ f hf :=
  NatIso.ofComponents (fun n => (deckDerivedZeroIso R τ f hf).app ((C).obj n))
    (fun {_ _} a => (deckDerivedZeroIso R τ f hf).hom.naturality ((C).map a))

/-- The source canonical homology comparison also carries its constructed action. -/
def harrisEtaleTrivialDerivedPlusCohomologyIso (q : ℕ) :
    harrisEtaleTrivialDerivedPlusSystem (G := G) ρ p U m X Y hY ⋙
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).mapAction G ≅
      harrisEtaleTrivialCohomologySystem (G := G) ρ p U m X Y hY q :=
  NatIso.ofComponents
    (fun n => pullbackDerivedHomologyIso R 1 (trivialEquivariantSheaf X R G ((C).obj n)) q)
    (fun {_ _} a => (pullbackDerivedHomologyFunctorIso R (1 : G →* (Aut X)ᵐᵒᵖ) q).hom.naturality
      ((trivialEquivariantFunctor X R G).map ((C).map a)))

/-- The source degree-zero comparison uses the canonical section map. -/
def harrisEtaleTrivialDerivedPlusZeroIso :
    harrisEtaleTrivialDerivedPlusSystem (G := G) ρ p U m X Y hY ⋙
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).mapAction G ≅
      harrisEtaleTrivialSectionsSystem (G := G) ρ p U m X Y hY :=
  NatIso.ofComponents
    (fun n => (pullbackDerivedZeroFunctorIso R (1 : G →* (Aut X)ᵐᵒᵖ)).app
      (trivialEquivariantSheaf X R G ((C).obj n)))
    (fun {_ _} a => (pullbackDerivedZeroFunctorIso R (1 : G →* (Aut X)ᵐᵒᵖ)).hom.naturality
      ((trivialEquivariantFunctor X R G).map ((C).map a)))

omit [HasDerivedCategory.{wX} (EtaleDerivedSections.ModuleSheaf X (HarrisCoefficientIntegers L p))] in
/-- Forgetting the target homology comparison gives the existing canonical
comparison of the actual restricted Harris system. -/
@[simp] theorem harrisEtaleDeckDerivedPlusCohomologyIso_hom_app_hom
    (q : ℕ) (n : ℕᵒᵖ) :
    ((harrisEtaleDeckDerivedPlusCohomologyIso ρ p U m X Y hY τ f hf q).hom.app n).hom =
      (harrisEtaleRestrictedDerivedPlusCohomologyIso ρ p U m X Y hY f q).hom.app n := by
  change ((deckDerivedHomologyIso R τ f hf q).hom.app ((C).obj n)).hom = _
  dsimp only [deckDerivedHomologyIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.isoWhiskerLeft]
  erw [Category.id_comp]
  change _ = 𝟙 _ ≫ _
  rw [Category.id_comp]
  rfl

omit [HasDerivedCategory.{wX} (EtaleDerivedSections.ModuleSheaf X (HarrisCoefficientIntegers L p))] in
/-- Forgetting the target zero comparison gives the existing canonical section
comparison, including its prescribed component map. -/
@[simp] theorem harrisEtaleDeckDerivedPlusZeroIso_hom_app_hom (n : ℕᵒᵖ) :
    ((harrisEtaleDeckDerivedPlusZeroIso ρ p U m X Y hY τ f hf).hom.app n).hom =
      (harrisEtaleRestrictedDerivedPlusZeroIso ρ p U m X Y hY f).hom.app n := by
  change ((deckDerivedZeroIso R τ f hf).hom.app ((C).obj n)).hom = _
  dsimp only [deckDerivedZeroIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.isoWhiskerLeft]
  erw [Category.id_comp]
  change _ = 𝟙 _ ≫ _
  rw [Category.id_comp]
  exact pullbackDerivedZeroFunctorIso_hom_app_hom R τ _

/-- The source equivariant comparison is precisely the original Harris
canonical comparison after forgetting actions. -/
@[simp] theorem harrisEtaleTrivialDerivedPlusCohomologyIso_hom_app_hom
    (q : ℕ) (n : ℕᵒᵖ) :
    ((harrisEtaleTrivialDerivedPlusCohomologyIso (G := G) ρ p U m X Y hY q).hom.app n).hom =
      (harrisEtaleDerivedPlusCohomologyIso ρ p U m X Y hY q).hom.app n := by
  change (pullbackDerivedHomologyIso R 1
    (trivialEquivariantSheaf X R G ((C).obj n)) q).hom.hom = 𝟙 _ ≫ _
  rw [Category.id_comp]
  rfl

/-- The source degree-zero comparison preserves the previously specified
Harris comparison, rather than choosing a new section isomorphism. -/
@[simp] theorem harrisEtaleTrivialDerivedPlusZeroIso_hom_app_hom (n : ℕᵒᵖ) :
    ((harrisEtaleTrivialDerivedPlusZeroIso (G := G) ρ p U m X Y hY).hom.app n).hom =
      (harrisEtaleDerivedPlusZeroIso ρ p U m X Y hY).hom.app n := by
  rw [harrisEtaleDerivedPlusZeroIso_eq_system]
  change ((pullbackDerivedZeroFunctorIso R (1 : G →* (Aut X)ᵐᵒᵖ)).hom.app
    (trivialEquivariantSheaf X R G ((C).obj n))).hom = 𝟙 _ ≫ _
  rw [Category.id_comp]
  exact pullbackDerivedZeroFunctorIso_hom_app_hom R 1 _

/-- The canonical recovery square holds equivariantly for the whole Harris
system, with all coefficient transitions retained. -/
theorem harrisEtaleDeckDerivedPlusPullback_homology (q : ℕ) :
    Functor.whiskerRight (harrisEtaleDeckDerivedPlusPullback ρ p U m X Y hY τ f hf)
          ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).mapAction G) ≫
        (harrisEtaleDeckDerivedPlusCohomologyIso ρ p U m X Y hY τ f hf q).hom =
      (harrisEtaleTrivialDerivedPlusCohomologyIso (G := G) ρ p U m X Y hY q).hom ≫
        harrisEtaleDeckCohomologyPullback ρ p U m X Y hY τ f hf q := by
  apply NatTrans.ext
  funext n
  exact deckDerivedSectionsMap_homology R τ f hf ((C).obj n) q

/-- The corresponding canonical square in degree zero recovers actual
ordinary section restriction equivariantly over the entire inverse system. -/
theorem harrisEtaleDeckDerivedPlusPullback_zero :
    Functor.whiskerRight (harrisEtaleDeckDerivedPlusPullback ρ p U m X Y hY τ f hf)
          ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).mapAction G) ≫
        (harrisEtaleDeckDerivedPlusZeroIso ρ p U m X Y hY τ f hf).hom =
      (harrisEtaleTrivialDerivedPlusZeroIso (G := G) ρ p U m X Y hY).hom ≫
        harrisEtaleDeckSectionsPullback ρ p U m X Y hY τ f hf := by
  apply NatTrans.ext
  funext n
  exact deckDerivedSectionsMap_zero R τ f hf ((C).obj n)

end Langlands.Shimura.Coefficients
