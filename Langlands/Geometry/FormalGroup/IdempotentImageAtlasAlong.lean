import Langlands.Geometry.FormalGroup.CentralImageAtlasComparison
import Langlands.Geometry.FormalGroup.AtlasOrderBaseChangeAlong

/-! # Image atlases over supplied coefficient algebra structures -/

noncomputable section

universe u v w c

namespace Langlands.FormalGroup.ModuleLaw.IdempotentImageCover

open CategoryTheory BasicAtlas

attribute [local instance] coefficientAlgebra coefficientScalarTower

set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {e : ModuleLaw.Hom M M}
variable (I : IdempotentImageCover e τ) (S : CommAlgCat.{v} R)

/-- Regard the structural map as linear over a supplied scalar algebra structure. -/
def coefficientMap (O : Type u) [CommRing O] [Algebra O R] (S : CommAlgCat.{v} R)
    (β : Algebra O S) (h : coefficientAlgebra (O := O) S = β) : (letI := β; R →ₐ[O] S) :=
  letI := β
  ⟨algebraMap R S, fun a => congrArg (fun γ : Algebra O S => @algebraMap O S _ _ γ a) h⟩

/-- Extend a formal image retraction to a test with the supplied scalar ring action. -/
def baseChangeWithAlgebra (β : Algebra O S) (h : coefficientAlgebra (O := O) S = β) :
    (letI := β; IdempotentImageCover (e.map (coefficientMap O S β h)) τ) := by
  cases h
  exact I.baseChange S

/-- The extended generators are still the images of the original principal cover. -/
theorem baseChangeWithAlgebra_opens (β : Algebra O S) (h : coefficientAlgebra (O := O) S = β) :
    (letI := β; (I.baseChangeWithAlgebra S β h).atlas.opens) = I.atlas.baseOpens S := by
  cases h
  rfl

variable {D : Type w} [Ring D] [Algebra O D]
variable {C : Type c} [CommRing C] [Algebra C D] [Algebra C R]
variable {E : ModuleLaw.OrderAction (Dᵐᵒᵖ × D) M}
variable (I : IdempotentImageCover E.divisionProjector τ)
variable (hs : ∀ (b : I.atlas.opens) (a : C) (x : τ → Localization.Away b.val),
    ((I.divisionOrder E).chart b).fiberTangent (RingHom.id _) (algebraMap C D a) x =
      algebraMap C (Localization.Away b.val) a • x)
variable (α : Algebra O S) (β : Algebra C S)
variable (hα : coefficientAlgebra (O := O) S = α) (hβ : coefficientAlgebra (O := C) S = β)
variable (ht : letI := α; letI := β;
  ∀ (b : (I.baseChangeWithAlgebra S α hα).atlas.opens) (a : C) (x : τ → Localization.Away b.val),
    (((I.baseChangeWithAlgebra S α hα).divisionOrder (E.map (coefficientMap O S α hα))).chart b).fiberTangent
      (RingHom.id _) (algebraMap C D a) x = algebraMap C (Localization.Away b.val) a • x)

/-- The actual comparison of central image atlases for independently supplied
target scalar algebra structures. -/
def baseChangeWithAlgebraCentralIso :
    (letI := α; letI := β;
      BasicAtlas.OrderAction.Iso
        (((I.baseChangeWithAlgebra S α hα).divisionOrder
          (E.map (coefficientMap O S α hα))).centralAtlasOrder ht)
        ((((I.divisionOrder E).centralAtlasOrder hs).baseChange S).reAlgebra β hβ)
        (I.baseChangeWithAlgebra_opens S α hα)) := by
  cases hα
  cases hβ
  exact I.baseChangeCentralIso S hs ht

end Langlands.FormalGroup.ModuleLaw.IdempotentImageCover
