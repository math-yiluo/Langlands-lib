import Langlands.CategoryTheory.MonoidalActionMap
import Langlands.AlgebraicGeometry.PointTopology.SmoothResiduePointLifting
import Langlands.AlgebraicGeometry.PointTopology.RingPointBaseChange
import Langlands.GroupScheme.FiniteFieldTorsorPointProof
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-! # Actual points of torsors over complete rings with finite residue -/

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.MonoidalActionMap

namespace Langlands.GroupScheme.IntegralTorsorPoint

/-- Smoothness descends from the trivialization supplied by the torsor shear. -/
theorem smooth_of_isIso_leftSMul {S : Scheme.{u}} (H : GroupScheme S)
    [Smooth H.X.hom] (X : Over S) [ModObj H.X X] (hfl : Flat X.hom)
    (hs : Surjective X.hom) (hqc : QuasiCompact X.hom)
    (hiso : IsIso (ModObj.leftSMul H.X X)) : Smooth X.hom := by
  have h1 : (ModObj.leftSMul H.X X).left ≫ pullback.snd X.hom X.hom =
      pullback.snd H.X.hom X.hom :=
    congrArg CommaMorphism.left (ModObj.leftSMul_snd (M := H.X) (X := X))
  have : IsIso (ModObj.leftSMul H.X X).left :=
    inferInstanceAs (IsIso ((Over.forget S).map (ModObj.leftSMul H.X X)))
  have h2 : Smooth (pullback.snd X.hom X.hom) := by
    rw [← IsIso.inv_hom_id_assoc (ModObj.leftSMul H.X X).left
      (pullback.snd X.hom X.hom), h1]
    infer_instance
  exact MorphismProperty.of_pullback_snd_of_descendsAlong (P := @Smooth)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := X.hom) (g := X.hom)
    ⟨⟨hs, hfl⟩, hqc⟩ h2

variable (R : Type u) [CommRing R] (I : Ideal R) [I.IsMaximal]
variable [Finite (R ⧸ I)] [IsAdicComplete I R]
variable (H : GroupScheme (Spec (CommRingCat.of R)))
variable [Smooth H.X.hom] [IsAffineHom H.X.hom]
variable (X : Over (Spec (CommRingCat.of R))) [ModObj H.X X]

/-- A smooth affine group with connected finite special fibre has a point on
 every actual fpqc torsor over the complete base. -/
theorem nonempty_ringPoint
    (hconn : ConnectedSpace
      ((baseChange (Spec.algebraMap R (R ⧸ I))).obj H).X.left)
    (hfl : Flat X.hom) (hs : Surjective X.hom) (hqc : QuasiCompact X.hom)
    (hiso : IsIso (ModObj.leftSMul H.X X)) : Nonempty (RingPoint R X R) := by
  let : Field (R ⧸ I) := Ideal.Quotient.field I
  let : Flat X.hom := hfl
  let : Surjective X.hom := hs
  let : QuasiCompact X.hom := hqc
  let : IsIso (ModObj.leftSMul H.X X) := hiso
  let : Smooth X.hom := smooth_of_isIso_leftSMul H X hfl hs hqc hiso
  let b := Spec.algebraMap R (R ⧸ I)
  let H₀ := (baseChange b).obj H
  let X₀ := ringBaseChange R (R ⧸ I) X
  let : ModObj H₀.X X₀ := mappedModObj (Over.pullback b) H.X X
  have hfl₀ : Flat X₀.hom := inferInstanceAs (Flat (pullback.snd X.hom b))
  have hs₀ : Surjective X₀.hom := inferInstanceAs (Surjective (pullback.snd X.hom b))
  have hqc₀ : QuasiCompact X₀.hom := inferInstanceAs (QuasiCompact (pullback.snd X.hom b))
  have hiso₀ : IsIso (ModObj.leftSMul H₀.X X₀) :=
    isIso_mapped_leftSMul (Over.pullback b) H.X X
  have : Smooth H₀.X.hom := inferInstanceAs (Smooth (pullback.snd H.X.hom b))
  have : IsAffineHom H₀.X.hom := inferInstanceAs (IsAffineHom (pullback.snd H.X.hom b))
  obtain ⟨p₀⟩ := finiteFieldTorsorPointStatement (R ⧸ I) H₀ hconn X₀
    hfl₀ hs₀ hqc₀ hiso₀
  let p : RingPoint R X (R ⧸ I) :=
    (ringPointBaseChangeEquiv R (R ⧸ I) (R ⧸ I) X).symm p₀
  exact ⟨smoothResiduePointLift R X R I p⟩

/-- A chosen actual integral point of the given torsor. -/
def integralTorsorPoint
    (hconn : ConnectedSpace
      ((baseChange (Spec.algebraMap R (R ⧸ I))).obj H).X.left)
    (hfl : Flat X.hom) (hs : Surjective X.hom) (hqc : QuasiCompact X.hom)
    (hiso : IsIso (ModObj.leftSMul H.X X)) : RingPoint R X R :=
  Classical.choice (nonempty_ringPoint R I H X hconn hfl hs hqc hiso)

end Langlands.GroupScheme.IntegralTorsorPoint
