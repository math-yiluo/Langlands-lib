import Langlands.Geometry.EtaleInverseImageScalars
import Langlands.Geometry.EtaleInverseImageCoherence
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Coextension and arbitrary inverse image of restricted scalars -/

noncomputable section

universe u

namespace Langlands.Geometry.EtaleInverseImage

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
open EtaleDirectImage EtaleCohomologyAction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- Coextend each section module by the actual module Hom_R(S,-).
The right adjoint on modules preserves the sheaf condition. -/
def sheafCoextendScalars (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u} R) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u} S) :=
  sheafCompose X.smallEtaleTopology (ModuleCat.coextendScalars.{u, u, u} φ)

/-- Restriction/coextension of actual etale sheaves is the restriction of
the actual presheaf adjunction through fully faithful sheaf inclusions. -/
def sheafRestrictCoextendScalarsAdj (X : Scheme.{u}) :
    sheafRestrictScalars φ X ⊣ sheafCoextendScalars φ X :=
  ((ModuleCat.restrictCoextendScalarsAdj.{u, u, u} φ).whiskerRight X.Etaleᵒᵖ).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf X.smallEtaleTopology (ModuleCat.{u} S))
      (fullyFaithfulSheafToPresheaf X.smallEtaleTopology (ModuleCat.{u} R))
      (Iso.refl _) (Iso.refl _)

instance sheafRestrictScalars_isLeftAdjoint (X : Scheme.{u}) :
    (sheafRestrictScalars φ X).IsLeftAdjoint :=
  (sheafRestrictCoextendScalarsAdj φ X).isLeftAdjoint

instance sheafCoextendScalars_isRightAdjoint (X : Scheme.{u}) :
    (sheafCoextendScalars φ X).IsRightAdjoint :=
  (sheafRestrictCoextendScalarsAdj φ X).isRightAdjoint

instance sheafRestrictScalars_preservesLimits (X : Scheme.{u}) :
    PreservesLimitsOfSize.{u, u} (sheafRestrictScalars φ X) :=
  (sheafExtendRestrictScalarsAdj φ X).rightAdjoint_preservesLimits

instance sheafRestrictScalars_preservesColimits (X : Scheme.{u}) :
    PreservesColimitsOfSize.{u, u} (sheafRestrictScalars φ X) :=
  (sheafRestrictCoextendScalarsAdj φ X).leftAdjoint_preservesColimits

instance sheafRestrictScalars_preservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (sheafRestrictScalars φ X) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u}
  intro J _ _
  infer_instance

instance sheafRestrictScalars_preservesFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits (sheafRestrictScalars φ X) := by
  apply preservesFiniteColimits_of_preservesFiniteColimitsOfSize.{u}
  intro J _ _
  infer_instance

/-- Scalar restriction is exact on actual module sheaves, independently
of flatness of the coefficient homomorphism. -/
def sheafRestrictScalarsExactFunctor (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u} S) ⥤ₑ
      Sheaf X.smallEtaleTopology (ModuleCat.{u} R) :=
  ExactFunctor.of (sheafRestrictScalars φ X)

@[simp] theorem sheafRestrictScalarsExactFunctor_obj (X : Scheme.{u}) :
    (sheafRestrictScalarsExactFunctor φ X).obj = sheafRestrictScalars φ X := rfl

instance sheafCoextendScalars_preservesInjectives (X : Scheme.{u}) :
    (sheafCoextendScalars φ X).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (sheafRestrictCoextendScalarsAdj φ X)

variable {X Z : Scheme.{u}} (f : Z ⟶ X)

/-- Geometric direct image and actual coefficient coextension commute
strictly, by precomposition and postcomposition. -/
def directImageCoextendScalarsIso :
    directImage f (ModuleCat.{u} R) ⋙ sheafCoextendScalars φ X ≅
      sheafCoextendScalars φ Z ⋙ directImage f (ModuleCat.{u} S) :=
  Iso.refl _

/-- Scalar restriction then inverse image has the expected actual
coextension/geometric direct-image right adjoint. -/
def restrictScalarsInverseImageAdjunction :
    sheafRestrictScalars φ X ⋙ inverseImage f R ⊣
      sheafCoextendScalars φ Z ⋙ directImage f (ModuleCat.{u} S) :=
  ((sheafRestrictCoextendScalarsAdj φ X).comp (inverseImageAdjunction f R)).ofNatIsoRight
    (directImageCoextendScalarsIso φ f)

/-- Inverse image then scalar restriction has the same right adjoint. -/
def inverseImageRestrictScalarsAdjunction :
    inverseImage f S ⋙ sheafRestrictScalars φ Z ⊣
      sheafCoextendScalars φ Z ⋙ directImage f (ModuleCat.{u} S) :=
  (inverseImageAdjunction f S).comp (sheafRestrictCoextendScalarsAdj φ Z)

/-- Actual arbitrary-morphism inverse image commutes with restriction of
coefficient scalars. -/
def inverseImageRestrictScalarsIso :
    sheafRestrictScalars φ X ⋙ inverseImage f R ≅
      inverseImage f S ⋙ sheafRestrictScalars φ Z :=
  Adjunction.leftAdjointUniq (restrictScalarsInverseImageAdjunction φ f)
    (inverseImageRestrictScalarsAdjunction φ f)

@[reassoc (attr := simp)] theorem inverseImageRestrictScalarsIso_unit
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} S)) :
    (restrictScalarsInverseImageAdjunction φ f).unit.app F ≫
        (sheafCoextendScalars φ Z ⋙ directImage f (ModuleCat.{u} S)).map
          ((inverseImageRestrictScalarsIso φ f).hom.app F) =
      (inverseImageRestrictScalarsAdjunction φ f).unit.app F :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ F

@[reassoc (attr := simp)] theorem inverseImageRestrictScalarsIso_counit
    (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u} R)) :
    (inverseImageRestrictScalarsIso φ f).hom.app
        ((sheafCoextendScalars φ Z ⋙ directImage f (ModuleCat.{u} S)).obj F) ≫
      (inverseImageRestrictScalarsAdjunction φ f).counit.app F =
        (restrictScalarsInverseImageAdjunction φ f).counit.app F :=
  Adjunction.leftAdjointUniq_hom_app_counit _ _ F

variable {V : Scheme.{u}}

private theorem conjugate_restrictScalarUniqueness
    {C D : Type*} [Category* C] [Category* D]
    {L L' : C ⥤ D} {G G' : D ⥤ C}
    (a : L ⊣ G) (b : L' ⊣ G') (e : G ≅ G') :
    conjugateEquiv b a ((a.ofNatIsoRight e).leftAdjointUniq b).hom = e.inv := by
  ext Y
  apply ((a.homEquiv _ _).symm).injective
  simp only [Adjunction.homEquiv_counit]
  rw [conjugateEquiv_counit]
  exact Adjunction.leftAdjointUniq_hom_app_counit (a.ofNatIsoRight e) b Y

private theorem conjugate_restrictScalar_associator_inv
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B}
    {L₃ : C ⥤ D} {R₃ : D ⥤ C}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (c : L₃ ⊣ R₃) :
    conjugateEquiv ((a.comp b).comp c) (a.comp (b.comp c))
        (associator L₁ L₂ L₃).inv =
      (associator R₃ R₂ R₁).inv := by
  have h : conjugateIsoEquiv (a.comp (b.comp c)) ((a.comp b).comp c)
      (associator L₁ L₂ L₃) = associator R₃ R₂ R₁ := by
    apply Iso.ext
    exact conjugateEquiv_associator_hom a b c
  exact congrArg Iso.inv h

/-- The constructed scalar comparison is conjugate to the inverse of the
strict geometric direct-image/coextension interchange. -/
theorem conjugate_inverseImageRestrictScalarsIso (f : Z ⟶ X) :
    conjugateEquiv
        ((inverseImageAdjunction f S).comp (sheafRestrictCoextendScalarsAdj φ Z))
        ((sheafRestrictCoextendScalarsAdj φ X).comp (inverseImageAdjunction f R))
        (inverseImageRestrictScalarsIso φ f).hom =
      (directImageCoextendScalarsIso φ f).inv :=
  conjugate_restrictScalarUniqueness _ _ _

/-- Coefficient restriction commutes with the actual identity inverse-image
comparison, retaining both functor unitors. -/
theorem inverseImageRestrictScalarsIso_id (X : Scheme.{u}) :
    (inverseImageRestrictScalarsIso φ (𝟙 X)).hom ≫
        whiskerRight (inverseImageId S X).hom (sheafRestrictScalars φ X) ≫
        (sheafRestrictScalars φ X).leftUnitor.hom =
      whiskerLeft (sheafRestrictScalars φ X) (inverseImageId R X).hom ≫
        (sheafRestrictScalars φ X).rightUnitor.hom := by
  apply (conjugateEquiv (sheafRestrictCoextendScalarsAdj φ X)
    ((sheafRestrictCoextendScalarsAdj φ X).comp
      (inverseImageAdjunction (𝟙 X) R))).injective
  rw [← conjugateEquiv_comp _
      ((inverseImageAdjunction (𝟙 X) S).comp (sheafRestrictCoextendScalarsAdj φ X)),
    ← conjugateEquiv_comp _ (Adjunction.id.comp (sheafRestrictCoextendScalarsAdj φ X)),
    ← conjugateEquiv_comp _ ((sheafRestrictCoextendScalarsAdj φ X).comp Adjunction.id)]
  simp only [conjugate_inverseImageRestrictScalarsIso, conjugateEquiv_whiskerRight,
    conjugateEquiv_whiskerLeft, conjugate_inverseImageId,
    conjugateEquiv_leftUnitor_hom, conjugateEquiv_rightUnitor_hom]
  apply NatTrans.ext
  funext F
  dsimp [directImageCoextendScalarsIso]
  simp only [Category.id_comp]
  apply Sheaf.hom_ext
  rfl

/-- The two orders of scalar interchange and geometric composition agree
as actual natural transformations, including the functor associators. -/
theorem inverseImageRestrictScalarsIso_comp (f : Z ⟶ X) (g : V ⟶ Z) :
    whiskerRight (inverseImageRestrictScalarsIso φ f).hom (inverseImage g R) ≫
        (associator (inverseImage f S) (sheafRestrictScalars φ Z) (inverseImage g R)).hom ≫
        whiskerLeft (inverseImage f S) (inverseImageRestrictScalarsIso φ g).hom ≫
        (associator (inverseImage f S) (inverseImage g S)
          (sheafRestrictScalars φ V)).inv ≫
        whiskerRight (inverseImageComp S f g).hom (sheafRestrictScalars φ V) =
      (associator (sheafRestrictScalars φ X) (inverseImage f R) (inverseImage g R)).hom ≫
        whiskerLeft (sheafRestrictScalars φ X) (inverseImageComp R f g).hom ≫
        (inverseImageRestrictScalarsIso φ (g ≫ f)).hom := by
  apply (conjugateEquiv
    ((inverseImageAdjunction (g ≫ f) S).comp (sheafRestrictCoextendScalarsAdj φ V))
    (((sheafRestrictCoextendScalarsAdj φ X).comp (inverseImageAdjunction f R)).comp
      (inverseImageAdjunction g R))).injective
  rw [← conjugateEquiv_comp _
      (((inverseImageAdjunction f S).comp (sheafRestrictCoextendScalarsAdj φ Z)).comp
        (inverseImageAdjunction g R)),
    ← conjugateEquiv_comp _
      ((inverseImageAdjunction f S).comp
        ((sheafRestrictCoextendScalarsAdj φ Z).comp (inverseImageAdjunction g R))),
    ← conjugateEquiv_comp _
      ((inverseImageAdjunction f S).comp
        ((inverseImageAdjunction g S).comp (sheafRestrictCoextendScalarsAdj φ V))),
    ← conjugateEquiv_comp _
      (((inverseImageAdjunction f S).comp (inverseImageAdjunction g S)).comp
        (sheafRestrictCoextendScalarsAdj φ V)),
    ← conjugateEquiv_comp _
      ((sheafRestrictCoextendScalarsAdj φ X).comp
        ((inverseImageAdjunction f R).comp (inverseImageAdjunction g R))),
    ← conjugateEquiv_comp _
      ((sheafRestrictCoextendScalarsAdj φ X).comp (inverseImageAdjunction (g ≫ f) R))]
  simp only [conjugate_inverseImageRestrictScalarsIso, conjugate_inverseImageComp,
    conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight,
    conjugateEquiv_associator_hom, conjugate_restrictScalar_associator_inv]
  apply NatTrans.ext
  funext F
  dsimp [directImageCoextendScalarsIso]
  simp only [Category.comp_id]
  apply Sheaf.hom_ext
  rfl

/-- The actual two-step scalar comparison, with geometric-composition
coherence recorded by the equality below. -/
def inverseImageRestrictScalarsTwoStepIso (f : Z ⟶ X) (g : V ⟶ Z) :
    (sheafRestrictScalars φ X ⋙ inverseImage f R) ⋙ inverseImage g R ≅
      inverseImage (g ≫ f) S ⋙ sheafRestrictScalars φ V :=
  isoWhiskerRight (inverseImageRestrictScalarsIso φ f) (inverseImage g R) ≪≫
    associator (inverseImage f S) (sheafRestrictScalars φ Z) (inverseImage g R) ≪≫
    isoWhiskerLeft (inverseImage f S) (inverseImageRestrictScalarsIso φ g) ≪≫
    (associator (inverseImage f S) (inverseImage g S) (sheafRestrictScalars φ V)).symm ≪≫
    isoWhiskerRight (inverseImageComp S f g) (sheafRestrictScalars φ V)

theorem inverseImageRestrictScalarsTwoStepIso_eq (f : Z ⟶ X) (g : V ⟶ Z) :
    inverseImageRestrictScalarsTwoStepIso φ f g =
      associator (sheafRestrictScalars φ X) (inverseImage f R) (inverseImage g R) ≪≫
        isoWhiskerLeft (sheafRestrictScalars φ X) (inverseImageComp R f g) ≪≫
        inverseImageRestrictScalarsIso φ (g ≫ f) := by
  apply Iso.ext
  simpa only [inverseImageRestrictScalarsTwoStepIso, Iso.trans_hom, Iso.symm_hom,
    isoWhiskerLeft_hom, isoWhiskerRight_hom] using inverseImageRestrictScalarsIso_comp φ f g

end Langlands.Geometry.EtaleInverseImage
