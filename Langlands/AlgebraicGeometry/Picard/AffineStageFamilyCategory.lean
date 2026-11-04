import Langlands.AlgebraicGeometry.Picard.AffineEnlargementSections
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Equivalence

/-! # Finite-stage categories of actual Picard families -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

/-- A finite subalgebra stage equipped with an actual line-bundle family. -/
structure AffineStageFamily where
  stage : AffineAlgebraStage R A
  family : PicardGroupoid ((relativeSpace f).obj (affineBase R stage.val))

namespace AffineStageFamily

variable {f}

/-- The actual family obtained by extension to the whole algebra. -/
def evaluation (L : AffineStageFamily (A := A) f) :
    PicardGroupoid ((relativeSpace f).obj (affineBase R A)) :=
  ((relative f).map (affineSubalgebraMap L.stage.val).op.toLoc).toFunctor.obj L.family

/-- The common finite stage of two families. -/
def commonStage (L M : AffineStageFamily (A := A) f) : AffineAlgebraStage R A :=
  ⟨L.stage.val ⊔ M.stage.val, L.stage.property.sup M.stage.property⟩

/-- Ordinary restriction of a family to a larger finite stage. -/
def atStage (L : AffineStageFamily (A := A) f) (D : AffineAlgebraStage R A)
    (h : L.stage.val ≤ D.val) :
    PicardGroupoid ((relativeSpace f).obj (affineBase R D.val)) :=
  ((relative f).map (affineAlgebraStageMap h).op.toLoc).toFunctor.obj L.family

/-- The ordinary pseudofunctor comparison between direct and iterated extension. -/
def evaluationIso (L : AffineStageFamily (A := A) f) (D : AffineAlgebraStage R A)
    (h : L.stage.val ≤ D.val) :
    L.evaluation ≅
      ((relative f).map (affineSubalgebraMap D.val).op.toLoc).toFunctor.obj
        (L.atStage D h) :=
  (Cat.Hom.toNatIso ((relative f).mapComp'
    (affineAlgebraStageMap h).op.toLoc (affineSubalgebraMap D.val).op.toLoc
    (affineSubalgebraMap L.stage.val).op.toLoc
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, affineAlgebraStageMap_restrict]))).app
      L.family

/-- The coherent Isom presheaf on the common finite stage. -/
def homPresheaf (L M : AffineStageFamily (A := A) f) :
    (Over (affineBase R (L.commonStage M).val))ᵒᵖ ⥤ Type (u + 1) :=
  affineEnlargementIsomPresheaf (L.commonStage M).val f
    (L.atStage (L.commonStage M) le_sup_left)
    (M.atStage (L.commonStage M) le_sup_right)

/-- The genuine diagram of Isom sections over common finite enlargements. -/
def homDiagram (L M : AffineStageFamily (A := A) f) :
    AffineAlgebraStageAbove (L.commonStage M).val ⥤ Type (u + 1) :=
  affineAlgebraStageAboveSections (L.commonStage M).val (L.homPresheaf M)

/-- Morphisms are the Type colimit of actual finite-stage Isom sections. -/
def Hom (L M : AffineStageFamily (A := A) f) : Type (u + 1) :=
  colimit (L.homDiagram M)

/-- The whole-base section comparison includes the ordinary pullback coherence. -/
def wholeHomEquiv (L M : AffineStageFamily (A := A) f) :
    (L.homPresheaf M).obj
        (op (Over.mk (affineSubalgebraMap (L.commonStage M).val))) ≃
      (L.evaluation ⟶ M.evaluation) :=
  Equiv.ulift.trans (Iso.homCongr
    (L.evaluationIso (L.commonStage M) le_sup_left).symm
    (M.evaluationIso (L.commonStage M) le_sup_right).symm)

/-- The canonical finite-stage section colimit maps bijectively to actual arrows. -/
def homEquiv [hf : IsProper f] [hflat : Flat f] [hfp : LocallyOfFinitePresentation f]
    (L M : AffineStageFamily (A := A) f) :
    L.Hom M ≃ (L.evaluation ⟶ M.evaluation) :=
  ((colimit.isColimit (L.homDiagram M)).coconePointUniqueUpToIso
    (affineEnlargementIsomSectionsIsColimit (L.commonStage M).val f
      (L.atStage (L.commonStage M) le_sup_left)
      (M.atStage (L.commonStage M) le_sup_right)
      (L.commonStage M).property hf hflat hfp)).toEquiv.trans (L.wholeHomEquiv M)

variable [IsProper f] [Flat f] [LocallyOfFinitePresentation f]

/-- A finite-stage representative is evaluated by its canonical restriction map. -/
theorem homEquiv_ι (L M : AffineStageFamily (A := A) f)
    (C : AffineAlgebraStageAbove (L.commonStage M).val)
    (φ : (L.homDiagram M).obj C) :
    L.homEquiv M (colimit.ι (L.homDiagram M) C φ) =
      L.wholeHomEquiv M
        ((L.homPresheaf M).map (affineAlgebraStageAboveRestriction C).op φ) := by
  apply congrArg (L.wholeHomEquiv M)
  exact ConcreteCategory.congr_hom
    (IsColimit.comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit (L.homDiagram M))
      (affineEnlargementIsomSectionsIsColimit (L.commonStage M).val f
        (L.atStage (L.commonStage M) le_sup_left)
        (M.atStage (L.commonStage M) le_sup_right)
        (L.commonStage M).property inferInstance inferInstance inferInstance) C) φ

/-- Category laws on genuine colimit morphisms transported through the proved comparison. -/
instance : Category (AffineStageFamily (A := A) f) where
  Hom L M := L.Hom M
  id L := (L.homEquiv L).symm (𝟙 L.evaluation)
  comp {L M N} φ ψ := (L.homEquiv N).symm (L.homEquiv M φ ≫ M.homEquiv N ψ)
  id_comp {L M} φ := by
    apply (L.homEquiv M).injective
    simp
  comp_id {L M} φ := by
    apply (L.homEquiv M).injective
    simp
  assoc {L M N P} φ ψ χ := by
    apply (L.homEquiv P).injective
    simp [Category.assoc]

/-- Actual extension of finite-stage families and their colimit morphisms. -/
def evaluationFunctor :
    AffineStageFamily (A := A) f ⥤
      PicardGroupoid ((relativeSpace f).obj (affineBase R A)) where
  obj := evaluation
  map {L M} := L.homEquiv M
  map_id L := (L.homEquiv L).apply_symm_apply _
  map_comp {L _ N} _ _ := (L.homEquiv N).apply_symm_apply _

/-- A specified actual section at a finite enlargement defines a colimit morphism. -/
def ofSection (L M : AffineStageFamily (A := A) f)
    (C : AffineAlgebraStageAbove (L.commonStage M).val)
    (φ : (L.homDiagram M).obj C) : L ⟶ M :=
  colimit.ι (L.homDiagram M) C φ

/-- Evaluation of a representative is its coherent ordinary restriction to `A`. -/
theorem evaluationFunctor_map_ofSection (L M : AffineStageFamily (A := A) f)
    (C : AffineAlgebraStageAbove (L.commonStage M).val)
    (φ : (L.homDiagram M).obj C) :
    evaluationFunctor.map (L.ofSection M C φ) =
      L.wholeHomEquiv M
        ((L.homPresheaf M).map (affineAlgebraStageAboveRestriction C).op φ) :=
  L.homEquiv_ι M C φ

/-- Every colimit morphism has an actual finite-stage representative. -/
theorem exists_section {L M : AffineStageFamily (A := A) f} (φ : L ⟶ M) :
    ∃ (C : AffineAlgebraStageAbove (L.commonStage M).val)
      (ψ : (L.homDiagram M).obj C), L.ofSection M C ψ = φ :=
  Types.jointly_surjective (L.homDiagram M) (colimit.isColimit _) φ

/-- Evaluation is fully faithful by the canonical section-colimit theorem. -/
def fullyFaithfulEvaluation :
    (evaluationFunctor (A := A) (f := f)).FullyFaithful where
  preimage {L M} := (L.homEquiv M).symm
  map_preimage {L M} := (L.homEquiv M).apply_symm_apply
  preimage_map {L M} := (L.homEquiv M).symm_apply_apply

instance : (evaluationFunctor (A := A) (f := f)).Full :=
  fullyFaithfulEvaluation.full

instance : (evaluationFunctor (A := A) (f := f)).Faithful :=
  fullyFaithfulEvaluation.faithful

/-- Every actual family descends to one of the finite-stage objects. -/
instance : (evaluationFunctor (A := A) (f := f)).EssSurj where
  mem_essImage M := by
    obtain ⟨B, hB, _, L, hL⟩ := exists_affineFamily_subalgebra f M.of ∅
    exact ⟨⟨⟨B, hB⟩, Core.mk L⟩, hL⟩

instance : (evaluationFunctor (A := A) (f := f)).IsEquivalence where

/-- Finite-stage actual families with colimit Isom morphisms recover the whole groupoid. -/
def equivalence :
    AffineStageFamily (A := A) f ≌
      PicardGroupoid ((relativeSpace f).obj (affineBase R A)) :=
  (evaluationFunctor (A := A) (f := f)).asEquivalence

/-- The finite-stage category is a groupoid because all evaluated arrows are invertible. -/
instance : Groupoid (AffineStageFamily (A := A) f) :=
  Groupoid.ofFullyFaithfulToGroupoid evaluationFunctor fullyFaithfulEvaluation

end AffineStageFamily

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
