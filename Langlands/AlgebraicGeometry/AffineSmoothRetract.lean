import Langlands.GroupScheme.SplitKernelRetractGeometry
import Langlands.RingTheory.Grassmannian.ProperFinitePresentation

/-! # Smoothness of affine scheme retracts over an arbitrary base -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.AffineRetractGeometry

/-- Retraction data for schemes over the same base. The section and retraction
are scheme morphisms, with no group structure imposed. -/
structure SchemeRetract {S : Scheme.{u}} (X Y : Over S) where
  sectionMap : Y ⟶ X
  retraction : X ⟶ Y
  section_retraction : sectionMap ≫ retraction = 𝟙 Y

/-- A retract of a smooth affine algebra over any ring is smooth. -/
theorem smooth_algSpec_retract_anyRing {R : CommRingCat.{u}} {A B : CommAlgCat.{u} R}
    [Smooth ((algSpec R).obj (op A)).hom]
    (i : (algSpec R).obj (op B) ⟶ (algSpec R).obj (op A))
    (r : (algSpec R).obj (op A) ⟶ (algSpec R).obj (op B)) (h : i ≫ r = 𝟙 _) :
    Smooth ((algSpec R).obj (op B)).hom := by
  let : Algebra.Smooth R A := (DynamicSmooth.smooth_algSpec_iff A).1 inferInstance
  have hformal : Algebra.FormallySmooth R B :=
    DynamicSmooth.formallySmooth_of_algSpec_retract i r h
  have hcoord : (algSpec.fullyFaithful.preimage r).unop ≫
      (algSpec.fullyFaithful.preimage i).unop = 𝟙 B := by
    have h' := congrArg algSpec.fullyFaithful.preimage h
    rw [Functor.FullyFaithful.preimage_comp, Functor.FullyFaithful.preimage_id] at h'
    simpa using congrArg Quiver.Hom.unop h'
  have hfp : Algebra.FinitePresentation R B :=
    Algebra.FinitePresentation.of_retract
      (algSpec.fullyFaithful.preimage i).unop.hom
      (algSpec.fullyFaithful.preimage r).unop.hom
      (congrArg (fun f => f.hom) hcoord)
  exact (DynamicSmooth.smooth_algSpec_iff B).2 ⟨hformal, hfp⟩

/-- An affine scheme retract of a smooth affine scheme over any ring is smooth. -/
theorem smooth_of_retract_anyRing {R : CommRingCat.{u}} {X Y : Over (Spec R)}
    [IsAffine X.left] [IsAffine Y.left] [Smooth X.hom]
    (i : Y ⟶ X) (r : X ⟶ Y) (h : i ≫ r = 𝟙 Y) : Smooth Y.hom := by
  let hX : (algSpec R).essImage X := essImage_algSpec.mpr inferInstance
  let hY : (algSpec R).essImage Y := essImage_algSpec.mpr inferInstance
  let A : CommAlgCat R := hX.witness.unop
  let B : CommAlgCat R := hY.witness.unop
  let eX : (algSpec R).obj (op A) ≅ X := hX.getIso
  let eY : (algSpec R).obj (op B) ≅ Y := hY.getIso
  let : Smooth ((algSpec R).obj (op A)).hom :=
    smooth_of_over_iso eX inferInstance
  have h' : (eY.hom ≫ i ≫ eX.inv) ≫ (eX.hom ≫ r ≫ eY.inv) = 𝟙 _ := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc i r, h, Category.id_comp, eY.hom_inv_id]
  exact smooth_of_over_iso eY.symm
    (smooth_algSpec_retract_anyRing
      (eY.hom ≫ i ≫ eX.inv) (eX.hom ≫ r ≫ eY.inv) h')

/-- A retract of a smooth affine morphism, affine over the same arbitrary
base scheme, is smooth. -/
theorem smooth_of_retract_anyBase {S : Scheme.{u}} {X Y : Over S}
    [IsAffineHom X.hom] [IsAffineHom Y.hom] [Smooth X.hom]
    (i : Y ⟶ X) (r : X ⟶ Y) (h : i ≫ r = 𝟙 Y) : Smooth Y.hom := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @Smooth) S.affineOpenCover.openCover
  intro k
  let b := S.affineOpenCover.f k
  let F := Over.pullback b
  let : IsAffine (F.obj X).left := by
    change IsAffine (CategoryTheory.Limits.pullback X.hom b)
    infer_instance
  let : IsAffine (F.obj Y).left := by
    change IsAffine (CategoryTheory.Limits.pullback Y.hom b)
    infer_instance
  let : Smooth (F.obj X).hom := by
    change Smooth (CategoryTheory.Limits.pullback.snd X.hom b)
    infer_instance
  exact smooth_of_retract_anyRing (F.map i) (F.map r) (by
    rw [← F.map_comp, h, F.map_id])

/-- Smoothness descends along retraction data between affine schemes over
the same arbitrary base. -/
theorem SchemeRetract.smooth {S : Scheme.{u}} {X Y : Over S}
    [IsAffineHom X.hom] [IsAffineHom Y.hom] [Smooth X.hom]
    (e : SchemeRetract X Y) : Smooth Y.hom :=
  smooth_of_retract_anyBase e.sectionMap e.retraction e.section_retraction

end Langlands.GroupScheme.AffineRetractGeometry
