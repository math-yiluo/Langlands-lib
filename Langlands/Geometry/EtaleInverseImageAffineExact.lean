/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The proof of affineLanEvaluationIso adapts Mathlib
CategoryTheory/Functor/Flat.lean, lanEvaluationIsoColim, to the universes
of the small etale sites, as in EtalePullbackAdjunction.lanEvaluationIso.
-/
import Langlands.Geometry.EtaleInverseImageLinear
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-! # Exactness of constructed etale inverse image over an affine base -/

noncomputable section

universe u

namespace Langlands.Geometry.EtaleInverseImage

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.Shimura.Coefficients EtaleDirectImage

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section AffineBase

variable (X : Scheme.{u}) [IsAffine X]

/-- The affine etale object representing the identity of an affine base. -/
def affineSiteTerminal : X.AffineEtale :=
  Scheme.AffineEtale.mk X.isoSpec.inv

/-- The identity affine object maps to the identity small-etale object. -/
def affineSiteTerminalIso :
    (Scheme.AffineEtale.Spec X).obj (affineSiteTerminal X) ≅
      MorphismProperty.Over.mk ⊤ (𝟙 X) (inferInstance : Etale (𝟙 X)) :=
  MorphismProperty.Over.isoMk X.isoSpec.symm (by simp [affineSiteTerminal])

def affineSiteTerminalImageIsTerminal :
    IsTerminal ((Scheme.AffineEtale.Spec X).obj (affineSiteTerminal X)) :=
  (MorphismProperty.Over.mkIdTerminal (@Etale) X).ofIso (affineSiteTerminalIso X).symm

def affineSiteTerminalIsTerminal : IsTerminal (affineSiteTerminal X) :=
  IsTerminal.isTerminalOfObj (Scheme.AffineEtale.Spec X) _
    (affineSiteTerminalImageIsTerminal X)

instance affineSite_hasTerminal : HasTerminal X.AffineEtale :=
  (affineSiteTerminalIsTerminal X).hasTerminal

instance affineSite_hasFiniteLimits : HasFiniteLimits X.AffineEtale :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

instance affineSpec_preservesTerminal :
    PreservesLimit (Functor.empty.{0} X.AffineEtale) (Scheme.AffineEtale.Spec X) := by
  apply preservesLimit_of_preserves_limit_cone (affineSiteTerminalIsTerminal X)
  exact (isLimitMapConeEmptyConeEquiv _ _).symm (affineSiteTerminalImageIsTerminal X)

instance affineSpec_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (Scheme.AffineEtale.Spec X) :=
  inferInstanceAs (PreservesLimitsOfShape WalkingCospan
    (MorphismProperty.CostructuredArrow.toOver (@Etale) Scheme.Spec X))

instance affineSpec_preservesFiniteLimits :
    PreservesFiniteLimits (Scheme.AffineEtale.Spec X) := by
  have := preservesLimitsOfShape_pempty_of_preservesTerminal (Scheme.AffineEtale.Spec X)
  exact preservesFiniteLimits_of_preservesTerminal_and_pullbacks _

end AffineBase

variable {X Z : Scheme.{u}} (f : Z ⟶ X) (R : Type u) [CommRing R]

instance affineComma_hasColimits (V : Z.Etaleᵒᵖ) :
    HasColimitsOfShape (CostructuredArrow (affineSiteMap f).op V) (ModuleCat.{u} R) :=
  HasColimitsOfShape.of_essentiallySmall.{u, u} _ _

variable [IsAffine X]

instance affineSiteMap_preservesFiniteLimits :
    PreservesFiniteLimits (affineSiteMap f) := by
  dsimp only [affineSiteMap]
  infer_instance

instance affineSiteMap_flat : RepresentablyFlat (affineSiteMap f) :=
  flat_of_preservesFiniteLimits _

/-- The actual comma colimits computing affine-source inverse image are
exact filtered colimits in the original module universe. -/
instance affineComma_hasExactColimits (V : Z.Etaleᵒᵖ) :
    HasExactColimitsOfShape (CostructuredArrow (affineSiteMap f).op V) (ModuleCat.{u} R) := by
  let J := CostructuredArrow (affineSiteMap f).op V
  have : IsFiltered (SmallModel.{u} J) :=
    IsFiltered.of_equivalence (equivSmallModel.{u} J)
  exact HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} R)
    (equivSmallModel.{u} J).symm

/-- Evaluation of the actual left Kan extension is its comma colimit.
This is the universe-general version of Mathlib's small-category formula,
as in the earlier etale-restriction construction. -/
def affineLanEvaluationIso (V : Z.Etaleᵒᵖ) :
    (affineSiteMap f).op.lan ⋙ (evaluation Z.Etaleᵒᵖ (ModuleCat.{u} R)).obj V ≅
      (Functor.whiskeringLeft _ _ (ModuleCat.{u} R)).obj
        (CostructuredArrow.proj (affineSiteMap f).op V) ⋙ colim :=
  NatIso.ofComponents (fun G =>
    IsColimit.coconePointUniqueUpToIso
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit (affineSiteMap f).op G V)
      (colimit.isColimit _)) (fun {G₁ G₂} a => by
    apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit
      (affineSiteMap f).op G₁ V).hom_ext
    intro T
    have h₁ := fun (G : X.AffineEtaleᵒᵖ ⥤ ModuleCat.{u} R) =>
      IsColimit.comp_coconePointUniqueUpToIso_hom
        (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit (affineSiteMap f).op G V)
        (colimit.isColimit _) T
    have h₂ := congr_app ((affineSiteMap f).op.lanUnit.naturality a) T.left
    dsimp at h₁ h₂ ⊢
    simp only [Category.assoc] at h₁ ⊢
    simp only [Functor.lan, Functor.lanUnit] at h₂ ⊢
    rw [reassoc_of% h₁, NatTrans.naturality_assoc, ← reassoc_of% h₂, h₁,
      ι_colimMap, Functor.whiskerLeft_app]
    rfl)

instance affineLan_preservesFiniteLimits :
    PreservesFiniteLimits ((affineSiteMap f).op.lan :
      (X.AffineEtaleᵒᵖ ⥤ ModuleCat.{u} R) ⥤ Z.Etaleᵒᵖ ⥤ ModuleCat.{u} R) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u}
  intro J _ _
  apply preservesLimitsOfShape_of_evaluation _ J
  intro V
  exact preservesLimitsOfShape_of_natIso (affineLanEvaluationIso f R V).symm

instance affineInverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (affineInverseImage f R) := by
  dsimp only [affineInverseImage, Functor.sheafPullbackConstruction.sheafPullback]
  infer_instance

instance inverseImage_affine_preservesFiniteLimits :
    PreservesFiniteLimits (inverseImage f R) := by
  dsimp only [inverseImage]
  infer_instance

/-- The actual finite-limit comparison for inverse image over an affine base. -/
def inverseImageFiniteLimitIso {J : Type*} [SmallCategory J] [FinCategory J]
    (F : J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (inverseImage f R).obj (limit F) ≅ limit (F ⋙ inverseImage f R) :=
  preservesLimitIso (inverseImage f R) F

/-- The previously constructed inverse image, equipped with its proved
finite-limit and finite-colimit preservation over an affine base. -/
def inverseImageExactFunctorOfAffine :
    Sheaf X.smallEtaleTopology (ModuleCat.{u} R) ⥤ₑ
      Sheaf Z.smallEtaleTopology (ModuleCat.{u} R) :=
  ExactFunctor.of (inverseImage f R)

@[simp] theorem inverseImageExactFunctorOfAffine_obj :
    (inverseImageExactFunctorOfAffine f R).obj = inverseImage f R := rfl

end Langlands.Geometry.EtaleInverseImage
