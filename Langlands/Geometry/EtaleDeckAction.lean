import Langlands.Geometry.EtaleDerivedEquivariantMap

/-! # Canonical deck actions on restricted etale coefficients -/

noncomputable section

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.Cohomology EtalePullback

universe u t wX wZ wT

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (X : Scheme.{u}) (R : Type u) [CommRing R]
variable (G : Type t) [Group G]

/-- Every sheaf has canonical equivariance for the trivial scheme action. -/
def trivialEquivariantSheaf (F : EtaleDerivedSections.ModuleSheaf X R) :
    EquivariantSheaf R (1 : G →* (Aut X)ᵐᵒᵖ) where
  obj := F
  act _ := (restrictionId (ModuleCat.{u} R)).hom.app F
  act_one := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    dsimp [data, oneIso, EtaleAutomorphism.translateCongr,
      EtaleAutomorphism.translateId, restrictionId]
    simp only [Category.comp_id, ← F.obj.map_comp]
    congr 1
  act_mul g h := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    dsimp [data, compIso, EtaleAutomorphism.translateComp,
      EtaleAutomorphism.translateCongr, restrictionId, translateBy,
      EtaleAutomorphism.translate, EtaleAutomorphism.sheafEquivalence]
    simp only [Category.comp_id, ← F.obj.map_comp]
    congr 1

/-- Every coefficient morphism respects canonical trivial equivariance. -/
def trivialEquivariantFunctor :
    EtaleDerivedSections.ModuleSheaf X R ⥤
      EquivariantSheaf R (1 : G →* (Aut X)ᵐᵒᵖ) where
  obj := trivialEquivariantSheaf X R G
  map α :=
    { hom := α
      comm _ := ((restrictionId (ModuleCat.{u} R)).hom.naturality α).symm }
  map_id _ := by apply TranslationAction.Equivariant.Hom.ext; rfl
  map_comp _ _ := by apply TranslationAction.Equivariant.Hom.ext; rfl

/-- Forgetting canonical trivial equivariance recovers the original sheaf functor. -/
def trivialEquivariantForgetIso :
    trivialEquivariantFunctor X R G ⋙ TranslationAction.Equivariant.forget ≅
      𝟭 (EtaleDerivedSections.ModuleSheaf X R) :=
  Iso.refl _

variable {X} {G}
variable {Z : Scheme.{u}} (τ : G →* (Aut Z)ᵐᵒᵖ)
variable (f : Z ⟶ X) [Etale f]
variable (hf : ∀ g, (aut τ g).hom ≫ f = f)

include hf in
omit [Etale f] in
/-- A deck action makes the map to the base equivariant for its trivial action. -/
theorem deckEquivariantMap (g : G) :
    f ≫ (aut (1 : G →* (Aut X)ᵐᵒᵖ) g).hom = (aut τ g).hom ≫ f := by
  change f ≫ 𝟙 X = (aut τ g).hom ≫ f
  rw [Category.comp_id, hf g]

/-- Canonical deck equivariance of restricted coefficients, constructed from
restriction comparisons and the deck geometry. -/
def deckEquivariantFunctor :
    EtaleDerivedSections.ModuleSheaf X R ⥤ EquivariantSheaf R τ :=
  trivialEquivariantFunctor X R G ⋙
    equivariantPullback R 1 τ f (deckEquivariantMap τ f hf)

/-- The deck structure is the inverse geometric square followed by the
restricted identity comparison on the base coefficient. -/
theorem deckEquivariantFunctor_obj_act (F : EtaleDerivedSections.ModuleSheaf X R)
    (g : G) :
    ((deckEquivariantFunctor R τ f hf).obj F).act g =
      (equivariantRestrictionIso R 1 τ f (deckEquivariantMap τ f hf) g).inv.app F ≫
        (restriction f (ModuleCat.{u} R)).map
          ((restrictionId (ModuleCat.{u} R)).hom.app F) := rfl

/-- Its underlying coefficient functor is precisely ordinary restriction. -/
def deckEquivariantForgetIso :
    deckEquivariantFunctor R τ f hf ⋙ TranslationAction.Equivariant.forget ≅
      restriction f (ModuleCat.{u} R) := Iso.refl _

/-- Every restricted coefficient arrow is the actual restriction of the original arrow. -/
@[simp] theorem deckEquivariantFunctor_map_hom
    {F E : EtaleDerivedSections.ModuleSheaf X R} (α : F ⟶ E) :
    ((deckEquivariantFunctor R τ f hf).map α).hom =
      (restriction f (ModuleCat.{u} R)).map α := rfl

/-- Ordinary sections of restrictions with their canonical deck actions. -/
def deckSectionsFunctor : EtaleDerivedSections.ModuleSheaf X R ⥤
    Action (ModuleCat.{u} R) G :=
  deckEquivariantFunctor R τ f hf ⋙ pullbackSectionsFunctor R τ

/-- Ordinary cohomology of restrictions with its canonical deck action. -/
def deckCohomologyFunctor (q : ℕ) : EtaleDerivedSections.ModuleSheaf X R ⥤
    Action (ModuleCat.{u} R) G :=
  deckEquivariantFunctor R τ f hf ⋙ pullbackCohomologyFunctor R τ q

/-- Geometric section restriction is equivariant and natural in the original coefficients. -/
def deckSectionsMap :
    trivialEquivariantFunctor X R G ⋙ pullbackSectionsFunctor R 1 ⟶
      deckSectionsFunctor R τ f hf :=
  Functor.whiskerLeft (trivialEquivariantFunctor X R G)
    (equivariantPullbackSections R 1 τ f (deckEquivariantMap τ f hf))

/-- Geometric cohomology restriction is equivariant and natural in coefficients. -/
def deckCohomologyMap (q : ℕ) :
    trivialEquivariantFunctor X R G ⋙ pullbackCohomologyFunctor R 1 q ⟶
      deckCohomologyFunctor R τ f hf q :=
  Functor.whiskerLeft (trivialEquivariantFunctor X R G)
    (equivariantPullbackCohomology R 1 τ f (deckEquivariantMap τ f hf) q)

/-- Forgetting equivariance recovers actual section restriction. -/
@[simp] theorem deckSectionsMap_app_hom (F : EtaleDerivedSections.ModuleSheaf X R) :
    ((deckSectionsMap R τ f hf).app F).hom = (sectionsMap f R).app F :=
  equivariantPullbackSections_app_hom R 1 τ f (deckEquivariantMap τ f hf) _

/-- Forgetting equivariance recovers actual cohomology restriction. -/
@[simp] theorem deckCohomologyMap_app_hom (F : EtaleDerivedSections.ModuleSheaf X R)
    (q : ℕ) :
    ((deckCohomologyMap R τ f hf q).app F).hom = (cohomologyMap f R q).app F :=
  equivariantPullbackCohomology_app_hom R 1 τ f (deckEquivariantMap τ f hf) q _

variable [HasDerivedCategory.{wX} (EtaleDerivedSections.ModuleSheaf X R)]
  [HasDerivedCategory.{wZ} (EtaleDerivedSections.ModuleSheaf Z R)]
  [HasDerivedCategory.{wT} (ModuleCat.{u} R)]

/-- Derived sections of canonical trivial coefficients have trivial action:
this follows from the actual derived geometric identity law. -/
theorem trivialEquivariantDerivedAction (F : EtaleDerivedSections.ModuleSheaf X R)
    (g : G) :
    ((pullbackDerivedSectionsFunctor R (1 : G →* (Aut X)ᵐᵒᵖ)).obj
      (trivialEquivariantSheaf X R G F)).ρ g =
        𝟙 ((EtaleDerivedSectionsPlus.derivedSections X R).obj F) := by
  rw [pullbackDerivedSectionsFunctor_obj_ρ]
  exact derivedSectionsMap_id R F

/-- Actual bounded-below derived sections with canonical deck action. -/
def deckDerivedSectionsFunctor : EtaleDerivedSections.ModuleSheaf X R ⥤
    Action (DerivedCategory.Plus (ModuleCat.{u} R)) G :=
  deckEquivariantFunctor R τ f hf ⋙ pullbackDerivedSectionsFunctor R τ

omit [HasDerivedCategory.{wX} (EtaleDerivedSections.ModuleSheaf X R)] in
/-- The action is geometric derived pullback followed by the canonical
restriction-comparison map, rather than an assumed cohomology action. -/
theorem deckDerivedSectionsFunctor_obj_ρ
    (F : EtaleDerivedSections.ModuleSheaf X R) (g : G) :
    ((deckDerivedSectionsFunctor R τ f hf).obj F).ρ g =
      (derivedSectionsMap (aut τ g).hom R).app ((restriction f (ModuleCat.{u} R)).obj F) ≫
        (EtaleDerivedSectionsPlus.derivedSections Z R).map
          (((deckEquivariantFunctor R τ f hf).obj F).act g) := rfl

omit [HasDerivedCategory.{wX} (EtaleDerivedSections.ModuleSheaf X R)] in
/-- The actual derived coefficient map is restriction followed by derived sections. -/
@[simp] theorem deckDerivedSectionsFunctor_map_hom
    {F E : EtaleDerivedSections.ModuleSheaf X R} (α : F ⟶ E) :
    ((deckDerivedSectionsFunctor R τ f hf).map α).hom =
      (EtaleDerivedSectionsPlus.derivedSections Z R).map
        ((restriction f (ModuleCat.{u} R)).map α) := rfl

/-- Geometric derived restriction is equivariant for the canonical deck action. -/
def deckDerivedSectionsMap :
    trivialEquivariantFunctor X R G ⋙ pullbackDerivedSectionsFunctor R 1 ⟶
      deckDerivedSectionsFunctor R τ f hf :=
  Functor.whiskerLeft (trivialEquivariantFunctor X R G)
    (equivariantPullbackDerivedSections R 1 τ f (deckEquivariantMap τ f hf))

/-- Its underlying derived map is exactly the actual geometric derived restriction. -/
@[simp] theorem deckDerivedSectionsMap_app_hom
    (F : EtaleDerivedSections.ModuleSheaf X R) :
    ((deckDerivedSectionsMap R τ f hf).app F).hom = (derivedSectionsMap f R).app F :=
  equivariantPullbackDerivedSections_app_hom R 1 τ f (deckEquivariantMap τ f hf) _

/-- The actual geometric derived restriction is invariant under every deck element. -/
theorem deckDerivedSectionsMap_invariant
    (F : EtaleDerivedSections.ModuleSheaf X R) (g : G) :
    ((deckDerivedSectionsMap R τ f hf).app F).hom ≫
        ((deckDerivedSectionsFunctor R τ f hf).obj F).ρ g =
      ((deckDerivedSectionsMap R τ f hf).app F).hom := by
  have h := ((deckDerivedSectionsMap R τ f hf).app F).comm g
  change ((pullbackDerivedSectionsFunctor R (1 : G →* (Aut X)ᵐᵒᵖ)).obj
      (trivialEquivariantSheaf X R G F)).ρ g ≫ _ = _ at h
  erw [trivialEquivariantDerivedAction R F g, Category.id_comp] at h
  exact h.symm

/-- The canonical homology comparison recovers the ordinary deck action naturally. -/
def deckDerivedHomologyIso (q : ℕ) :
    deckDerivedSectionsFunctor R τ f hf ⋙
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).mapAction G ≅
        deckCohomologyFunctor R τ f hf q :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (deckEquivariantFunctor R τ f hf)
      (pullbackDerivedHomologyFunctorIso R τ q)

/-- Degree zero recovers the ordinary section action by the specified canonical map. -/
def deckDerivedZeroIso :
    deckDerivedSectionsFunctor R τ f hf ⋙
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).mapAction G ≅
        deckSectionsFunctor R τ f hf :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (deckEquivariantFunctor R τ f hf)
      (pullbackDerivedZeroFunctorIso R τ)

/-- The homology square uses the canonical comparisons on both sides. -/
theorem deckDerivedSectionsMap_homology (F : EtaleDerivedSections.ModuleSheaf X R)
    (q : ℕ) :
    ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).mapAction G).map
        ((deckDerivedSectionsMap R τ f hf).app F) ≫
        (deckDerivedHomologyIso R τ f hf q).hom.app F =
      (pullbackDerivedHomologyIso R 1 (trivialEquivariantSheaf X R G F) q).hom ≫
        (deckCohomologyMap R τ f hf q).app F := by
  dsimp only [deckDerivedHomologyIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.isoWhiskerLeft]
  erw [Category.id_comp]
  exact equivariantPullbackDerivedSections_homology R 1 τ f
        (deckEquivariantMap τ f hf) (trivialEquivariantSheaf X R G F) q

/-- The degree-zero square recovers actual section restriction equivariantly. -/
theorem deckDerivedSectionsMap_zero (F : EtaleDerivedSections.ModuleSheaf X R) :
    ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).mapAction G).map
        ((deckDerivedSectionsMap R τ f hf).app F) ≫
        (deckDerivedZeroIso R τ f hf).hom.app F =
      (pullbackDerivedZeroFunctorIso R (1 : G →* (Aut X)ᵐᵒᵖ)).hom.app
        (trivialEquivariantSheaf X R G F) ≫ (deckSectionsMap R τ f hf).app F := by
  dsimp only [deckDerivedZeroIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.isoWhiskerLeft]
  erw [Category.id_comp]
  exact equivariantPullbackDerivedSections_zero R 1 τ f
        (deckEquivariantMap τ f hf) (trivialEquivariantSheaf X R G F)

end Langlands.Geometry.EtaleCohomologyAction
