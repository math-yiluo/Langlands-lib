import Langlands.Geometry.EtaleSectionPullbackCoherence
import Langlands.Geometry.EtaleRestrictionSectionComparison
import Langlands.Geometry.EtaleConstantPullback

/-! # Inverse image of constant sheaves along arbitrary morphisms of schemes -/

noncomputable section

universe u

namespace Langlands.Geometry.EtaleInverseImage

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open EtaleDirectImage EtaleDerivedSections EtaleDerivedDirectImage EtaleDerivedGlobalPullback

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Z : Scheme.{u}} (f : Z ⟶ X) (R : Type u) [CommRing R]

/-- Constant sheaves on `Z` are left adjoint to the composite of direct image and sections
on `X`, through the canonical identification of that composite with sections on `Z`. -/
def constantDirectImageSectionsAdj :
    constantSheaf Z.smallEtaleTopology (ModuleCat.{u} R) ⊣
      directImage f (ModuleCat.{u} R) ⋙ sections X R :=
  (constantSheafΓAdj Z.smallEtaleTopology (ModuleCat.{u} R)).ofNatIsoRight
    (directImageSectionsIso f R).symm

/-- Inverse image of the constant sheaf with value `M` is the constant sheaf with value `M`,
naturally in `M`: both functors are left adjoint to sections on `Z`. -/
def inverseImageConstantIso :
    constantSheaf X.smallEtaleTopology (ModuleCat.{u} R) ⋙ inverseImage f R ≅
      constantSheaf Z.smallEtaleTopology (ModuleCat.{u} R) :=
  ((constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u} R)).comp
    (inverseImageAdjunction f R)).leftAdjointUniq (constantDirectImageSectionsAdj f R)

/-- Global-section pullback is sections of the inverse-image adjunction unit, followed by the
identification of sections of the direct image with sections on `Z`. -/
theorem sectionsPullback_app_eq (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (sectionsPullback f R).app F =
      (sections X R).map ((inverseImageAdjunction f R).unit.app F) ≫
        (directImageSectionsIso f R).hom.app ((inverseImage f R).obj F) := by
  simp only [sectionsPullback, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Category.id_comp]

/-- The unit of `constantDirectImageSectionsAdj` is the constant-sheaf unit on `Z` followed by
the inverse section comparison. -/
theorem constantDirectImageSectionsAdj_unit_app (M : ModuleCat.{u} R) :
    (constantDirectImageSectionsAdj f R).unit.app M =
      (constantSheafΓAdj Z.smallEtaleTopology (ModuleCat.{u} R)).unit.app M ≫
        (directImageSectionsIso f R).inv.app _ := by
  rw [← Adjunction.homEquiv_id, constantDirectImageSectionsAdj,
    Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_id]
  rfl

/-- Maps out of the inverse image of a constant sheaf are determined by the composite of the
constant-sheaf unit on `X`, global-section pullback and sections on `Z`. -/
theorem inverseImageConstant_hom_ext (M : ModuleCat.{u} R)
    {H : Sheaf Z.smallEtaleTopology (ModuleCat.{u} R)}
    {φ ψ : (inverseImage f R).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M) ⟶ H}
    (h : (constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u} R)).unit.app M ≫
        (sectionsPullback f R).app _ ≫ (sections Z R).map φ =
      (constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u} R)).unit.app M ≫
        (sectionsPullback f R).app _ ≫ (sections Z R).map ψ) :
    φ = ψ := by
  let adj := (constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u} R)).comp
    (inverseImageAdjunction f R)
  apply (adj.homEquiv M H).injective
  have key : ∀ χ : (inverseImage f R).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M) ⟶ H,
      adj.homEquiv M H χ ≫ (directImageSectionsIso f R).hom.app H =
        (constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u} R)).unit.app M ≫
          (sectionsPullback f R).app _ ≫ (sections Z R).map χ := by
    intro χ
    have hn := (directImageSectionsIso f R).hom.naturality χ
    dsimp only [Functor.comp_map] at hn
    rw [Adjunction.homEquiv_unit, Adjunction.comp_unit_app, sectionsPullback_app_eq]
    simp only [Functor.comp_map, Category.assoc]
    rw [← hn]
    rfl
  rw [← cancel_mono ((directImageSectionsIso f R).hom.app H), key, key, h]

/-- The isomorphism is normalized by global sections: the constant-sheaf unit on `X`,
followed by global-section pullback and the isomorphism, is the constant-sheaf unit on `Z`. -/
@[reassoc] theorem unit_sectionsPullback_inverseImageConstantIso (M : ModuleCat.{u} R) :
    (constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u} R)).unit.app M ≫
        (sectionsPullback f R).app _ ≫
          (sections Z R).map ((inverseImageConstantIso f R).hom.app M) =
      (constantSheafΓAdj Z.smallEtaleTopology (ModuleCat.{u} R)).unit.app M := by
  have hn : (directImageSectionsIso f R).hom.app
        ((inverseImage f R).obj ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M)) ≫
        (sections Z R).map ((inverseImageConstantIso f R).hom.app M) =
      (sections X R).map ((directImage f (ModuleCat.{u} R)).map
          ((inverseImageConstantIso f R).hom.app M)) ≫
        (directImageSectionsIso f R).hom.app
          ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u} R)).obj M) :=
    ((directImageSectionsIso f R).hom.naturality ((inverseImageConstantIso f R).hom.app M)).symm
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u} R)).comp
      (inverseImageAdjunction f R)) (constantDirectImageSectionsAdj f R) M
  rw [Adjunction.comp_unit_app, constantDirectImageSectionsAdj_unit_app] at h
  have h' := congrArg (· ≫ (directImageSectionsIso f R).hom.app
    ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u} R)).obj M)) h
  simp only [Category.assoc, Iso.inv_hom_id_app, Functor.comp_map] at h'
  rw [sectionsPullback_app_eq, Category.assoc, hn]
  exact h'.trans (Category.comp_id _)

section Coherence

variable {V : Scheme.{u}}

/-- Along the identity, the comparison is the identity comparison of inverse image. -/
theorem inverseImageConstantIso_id (M : ModuleCat.{u} R) :
    (inverseImageConstantIso (𝟙 X) R).hom.app M =
      (inverseImageId R X).hom.app
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M) := by
  apply inverseImageConstant_hom_ext (𝟙 X) R M
  rw [unit_sectionsPullback_inverseImageConstantIso, sectionsPullback_id]
  exact (Category.comp_id _).symm

/-- The comparison for a composite is the composite of the comparisons, through the
composition comparison of inverse images. -/
theorem inverseImageConstantIso_comp (g : V ⟶ Z) (M : ModuleCat.{u} R) :
    (inverseImageComp R f g).hom.app
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M) ≫
      (inverseImageConstantIso (g ≫ f) R).hom.app M =
    (inverseImage g R).map ((inverseImageConstantIso f R).hom.app M) ≫
      (inverseImageConstantIso g R).hom.app M := by
  rw [← cancel_epi ((inverseImageComp R f g).inv.app
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M)), Iso.inv_hom_id_app_assoc]
  apply inverseImageConstant_hom_ext (g ≫ f) R M
  have e : (sections V R).map ((inverseImageComp R f g).hom.app
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M)) ≫
      (sections V R).map ((inverseImageComp R f g).inv.app
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M) ≫
        (inverseImage g R).map ((inverseImageConstantIso f R).hom.app M) ≫
          (inverseImageConstantIso g R).hom.app M) =
      (sections V R).map ((inverseImage g R).map ((inverseImageConstantIso f R).hom.app M)) ≫
        (sections V R).map ((inverseImageConstantIso g R).hom.app M) := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app_assoc, Functor.map_comp]
  have hn := (sectionsPullback g R).naturality ((inverseImageConstantIso f R).hom.app M)
  dsimp only [Functor.comp_map] at hn
  rw [unit_sectionsPullback_inverseImageConstantIso, ← sectionsPullback_comp R f g]
  simp only [Category.assoc]
  rw [e, ← reassoc_of% hn]
  have h1 := unit_sectionsPullback_inverseImageConstantIso f R M
  have h2 := unit_sectionsPullback_inverseImageConstantIso g R M
  rw [← h1] at h2
  simpa only [Category.assoc] using h2.symm

end Coherence

section Etale

variable [Etale f]

/-- The constant-sheaf unit of global sections, evaluated at the terminal object, is the
sheafification unit of the constant presheaf there. -/
theorem constantSheafΓAdj_unit_sectionsIso (W : Scheme.{u}) (M : ModuleCat.{u} R) :
    (constantSheafΓAdj W.smallEtaleTopology (ModuleCat.{u} R)).unit.app M ≫
        (sectionsIso W R).hom.app
          ((constantSheaf W.smallEtaleTopology (ModuleCat.{u} R)).obj M) =
      (toSheafify W.smallEtaleTopology
        ((Functor.const W.Etaleᵒᵖ).obj M)).app (Opposite.op (⊤_ W.Etale)) := by
  rw [sectionsIso, Sheaf.ΓNatIsoSheafSections, Adjunction.unit_rightAdjointUniq_hom_app]
  simp [constantSheafAdj, Adjunction.comp_unit_app]

/-- The section map of etale restriction carries the constant-sheaf unit on `X`, followed by
the constant-sheaf comparison, to the constant-sheaf unit on `Z`. -/
theorem unit_sectionsMap_constantPullbackIso (M : ModuleCat.{u} R) :
    (constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u} R)).unit.app M ≫
        (EtalePullback.sectionsMap f R).app
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M) ≫
        (sections Z R).map ((EtalePullback.constantPullbackIso f (ModuleCat.{u} R)).hom.app M) =
      (constantSheafΓAdj Z.smallEtaleTopology (ModuleCat.{u} R)).unit.app M := by
  have hW : ∀ W : Scheme.{u},
      (constantSheafΓAdj W.smallEtaleTopology (ModuleCat.{u} R)).unit.app M =
        (toSheafify W.smallEtaleTopology
          ((Functor.const W.Etaleᵒᵖ).obj M)).app (Opposite.op (⊤_ W.Etale)) ≫
          (sectionsIso W R).inv.app
            ((constantSheaf W.smallEtaleTopology (ModuleCat.{u} R)).obj M) := by
    intro W
    rw [← constantSheafΓAdj_unit_sectionsIso, Category.assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  have hn : (sectionsIso Z R).inv.app ((EtalePullback.restriction f (ModuleCat.{u} R)).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M)) ≫
        (sections Z R).map ((EtalePullback.constantPullbackIso f (ModuleCat.{u} R)).hom.app M) =
      ((EtalePullback.constantPullbackIso f (ModuleCat.{u} R)).hom.app M).hom.app
          (Opposite.op (⊤_ Z.Etale)) ≫
        (sectionsIso Z R).inv.app
          ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u} R)).obj M) :=
    ((sectionsIso Z R).inv.naturality
      ((EtalePullback.constantPullbackIso f (ModuleCat.{u} R)).hom.app M)).symm
  have ht : (toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj M)).app (Opposite.op (⊤_ X.Etale)) ≫
      ((EtalePullback.terminalSectionsMap f (ModuleCat.{u} R)).app
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M)) ≫
      ((EtalePullback.constantPullbackIso f (ModuleCat.{u} R)).hom.app M).hom.app
          (Opposite.op (⊤_ Z.Etale)) =
      (toSheafify Z.smallEtaleTopology
        ((Functor.const Z.Etaleᵒᵖ).obj M)).app (Opposite.op (⊤_ Z.Etale)) := by
    have hu := congrArg (fun a => a.app (Opposite.op (⊤_ Z.Etale)))
      (EtalePullback.constantPullbackIso_hom_unit f (ModuleCat.{u} R) M)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hu
    rw [← hu]
    change _ ≫ (sheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).map _ ≫ _ = _
    rw [← (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).naturality_assoc]
    simp only [Functor.const_obj_map]
    rfl
  simp only [EtalePullback.sectionsMap, NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [hW X, hW Z]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [hn, ← Category.assoc, ← Category.assoc, Category.assoc _ _
    (((EtalePullback.constantPullbackIso f (ModuleCat.{u} R)).hom.app M).hom.app _), ht]

/-- Along an etale morphism, the comparison agrees with the constant-sheaf comparison for
etale restriction, through the identification of inverse image with restriction. -/
theorem inverseImageConstantIso_etale (M : ModuleCat.{u} R) :
    (inverseImageIsoRestriction f R).hom.app
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M) ≫
      (EtalePullback.constantPullbackIso f (ModuleCat.{u} R)).hom.app M =
    (inverseImageConstantIso f R).hom.app M := by
  symm
  apply inverseImageConstant_hom_ext f R M
  rw [unit_sectionsPullback_inverseImageConstantIso, Functor.map_comp,
    sectionsPullback_restriction_assoc, unit_sectionsMap_constantPullbackIso]

end Etale

variable (G : Type u) [Monoid G]

/-- The constant-sheaf comparison preserves every coefficient group operator. -/
def inverseImageConstantActionIso :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).mapAction G ⋙
        (inverseImage f R).mapAction G ≅
      (constantSheaf Z.smallEtaleTopology (ModuleCat.{u} R)).mapAction G :=
  (Functor.mapActionComp G _ _).symm ≪≫
    Functor.mapActionCongr G (inverseImageConstantIso f R)

@[simp] theorem inverseImageConstantActionIso_hom_hom (M : Action (ModuleCat.{u} R) G) :
    ((inverseImageConstantActionIso f R G).hom.app M).hom =
      (inverseImageConstantIso f R).hom.app M.V := by
  simp [inverseImageConstantActionIso]

@[simp] theorem inverseImageConstantActionIso_inv_hom (M : Action (ModuleCat.{u} R) G) :
    ((inverseImageConstantActionIso f R G).inv.app M).hom =
      (inverseImageConstantIso f R).inv.app M.V := by
  simp [inverseImageConstantActionIso]

end Langlands.Geometry.EtaleInverseImage
