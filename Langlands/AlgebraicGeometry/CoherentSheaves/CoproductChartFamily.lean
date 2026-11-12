import Langlands.AlgebraicGeometry.CoherentSheaves.Pullback
import Langlands.AlgebraicGeometry.Picard.CoproductChartLineBundle
import Langlands.AlgebraicGeometry.Modules.AffineRelativeFlatness
import Langlands.AlgebraicGeometry.Modules.FinitePresentationDescent
import Langlands.AlgebraicGeometry.Modules.FinitePresentationSections
import Langlands.AlgebraicGeometry.Modules.RelativeFlatnessDescent

/-! # Actual coherent families on the relative space of a coproduct chart -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.CoherentSheaves

namespace OpenCoverFamily

variable {Y : Scheme.{u}} (𝒰 : Y.OpenCover.{u})

/-- Local finite presentation can be checked on the members of an open cover. -/
lemma isFinitePresentation_of_openCover (N : Y.Modules)
    (h : ∀ i, ((Scheme.Modules.pullback (𝒰.f i)).obj N).IsFinitePresentation) :
    N.IsFinitePresentation := by
  apply Modules.isFinitePresentation_of_forall_exists_presentation
  intro y
  obtain ⟨i, x, rfl⟩ := 𝒰.exists_eq y
  have : (N.restrict (𝒰.f i)).IsFinitePresentation :=
    ObjectProperty.prop_of_iso (SheafOfModules.isFinitePresentation (𝒰.X i).ringCatSheaf)
      ((Scheme.Modules.restrictFunctorIsoPullback (𝒰.f i)).app N).symm (h i)
  obtain ⟨W, hxW, P, hP⟩ := Modules.exists_finitePresentation_restrict (N.restrict (𝒰.f i)) x
  let P' : (N.restrict (W.ι ≫ 𝒰.f i)).Presentation :=
    P.ofIsIso ((Scheme.Modules.restrictFunctorComp W.ι (𝒰.f i)).app N).inv
  obtain ⟨P'', hP''⟩ := Modules.exists_presentation_opensRange N (W.ι ≫ 𝒰.f i) P'
  refine ⟨(W.ι ≫ 𝒰.f i).opensRange, ⟨⟨x, hxW⟩, rfl⟩, P'', hP''⟩

/-- Relative flatness can be checked on the members of an open cover, with the
composite structure maps. -/
lemma isFlatOver_of_openCover {B : Scheme.{u}} (p : Y ⟶ B) (N : Y.Modules)
    (h : ∀ i, Modules.IsFlatOver (𝒰.f i ≫ p) ((Scheme.Modules.pullback (𝒰.f i)).obj N)) :
    Modules.IsFlatOver p N := by
  refine (Modules.isFlatOver_iff_openCover p N 𝒰.X 𝒰.f (fun y ↦ 𝒰.exists_eq y)).2
    (fun i ↦ ?_)
  exact (Modules.isFlatOver_iff_of_iso _
    ((Scheme.Modules.restrictFunctorIsoPullback (𝒰.f i)).app N).symm).mp (h i)

end OpenCoverFamily

namespace CoproductChartFamily

open Picard Picard.CoproductChartBundle AlgebraicSpace.CoproductChart
open Langlands.Scheme.Modules

variable {S X : Scheme.{u}} (f : X ⟶ S) {ι : Type u} (V : ι → Over S)
  (M : ∀ i, FamilyGroupoid f (V i))

/-- The actual module glued from the component families along the disjoint
relative cover. -/
def module : ((relativeSpace f).obj (sigmaOver V)).Modules :=
  OpenCoverModuleGluing.glued (relativeCover f V) (fun i ↦ (M i).of.obj)
    (DisjointCoverGluing.transition (relativeCover_isDisjoint f V) (fun i ↦ (M i).of.obj))

/-- The glued module pulls back to each prescribed component module. -/
def moduleIso (i : ι) :
    (Scheme.Modules.pullback ((relativeSpace f).map (sigmaOverι V i))).obj
        (module f V M) ≅ (M i).of.obj :=
  OpenCoverModuleGluing.pieceIso (relativeCover f V) (fun i ↦ (M i).of.obj)
    (DisjointCoverGluing.transition (relativeCover_isDisjoint f V) (fun i ↦ (M i).of.obj))
    (DisjointCoverGluing.cocycle (relativeCover_isDisjoint f V) (fun i ↦ (M i).of.obj)) i

/-- The glued module is a flat finitely presented family over the coproduct chart. -/
lemma isFamily_module :
    IsFamily ((relativeProjection f).app (sigmaOver V)) (module f V M) := by
  refine ⟨OpenCoverFamily.isFinitePresentation_of_openCover (relativeCover f V) _
    (fun i ↦ ?_), OpenCoverFamily.isFlatOver_of_openCover (relativeCover f V) _ _
    (fun i ↦ ?_)⟩
  · exact ObjectProperty.prop_of_iso
      (SheafOfModules.isFinitePresentation ((relativeSpace f).obj (V i)).ringCatSheaf)
      (moduleIso f V M i).symm (M i).of.property.1
  · have hw : (relativeCover f V).f i ≫ (relativeProjection f).app (sigmaOver V) =
        (relativeProjection f).app (V i) ≫ (sigmaOverι V i).left := by
      rw [relativeCover_f]
      exact (relativeProjection f).naturality (sigmaOverι V i)
    rw [hw]
    exact (Modules.isFlatOver_iff_of_iso _ (moduleIso f V M i).symm).mp
      (Modules.isFlatOver_comp_of_flat _ _ _ (M i).of.property.2)

/-- The actual family on the relative space of the coproduct chart. -/
def family : FamilyGroupoid f (sigmaOver V) :=
  ⟨⟨module f V M, isFamily_module f V M⟩⟩

/-- The glued family restricts to each component family. -/
def familyIso (i : ι) :
    (FamilyGroupoid.pullback f (sigmaOverι V i)).obj (family f V M) ≅ M i :=
  Core.isoMk (ObjectProperty.isoMk _ (moduleIso f V M i))

end CoproductChartFamily

end Langlands.AlgebraicGeometry.CoherentSheaves
