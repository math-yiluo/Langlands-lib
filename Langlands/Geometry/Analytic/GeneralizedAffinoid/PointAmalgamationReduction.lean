import Langlands.Geometry.Analytic.ValuedField.AmalgamationStatement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.PointAmalgamationStatement
import Langlands.Geometry.Analytic.Spectrum.ResidueField.Lift

/-! # Completed-residue reduction of compatible point amalgamation -/

noncomputable section

universe u v w

namespace Langlands.Analytic

namespace BanachSpectrum

variable {A : Type u} [NormedCommRing A]
  (K : Type v) [NormedField K] [IsUltrametricDist K] [NormedAlgebra K A]
  {B : Type w} [NormedCommRing B] [NormedAlgebra K B]

/-- The isometric map on completed residue fields when a point is identified
with the restriction of a target point. -/
def completedResidueComapOfEq (g : BoundedAlgHom K A B)
    (x : BanachSpectrum A) (y : BanachSpectrum B)
    (h : comap g.toBoundedRingHom y = x) :
    BoundedAlgHom K (CompletedResidueField K x) (CompletedResidueField K y) :=
  completedResidueLift K x ((completedResidueMap K y).comp g).toAlgHom
    (fun a => (norm_completedResidueMap K y (g a)).trans
      (congrArg (fun z : BanachSpectrum A => z a) h))

theorem isometry_completedResidueComapOfEq (g : BoundedAlgHom K A B)
    (x : BanachSpectrum A) (y : BanachSpectrum B)
    (h : comap g.toBoundedRingHom y = x) :
    Isometry (completedResidueComapOfEq K g x y h) :=
  isometry_completedResidueLift K _ _ _

@[simp]
theorem completedResidueComapOfEq_map (g : BoundedAlgHom K A B)
    (x : BanachSpectrum A) (y : BanachSpectrum B)
    (h : comap g.toBoundedRingHom y = x) (a : A) :
    completedResidueComapOfEq K g x y h (completedResidueMap K x a) =
      completedResidueMap K y (g a) :=
  completedResidueLift_map K _ _ _ a

end BanachSpectrum

namespace PresentedAffinoidAlgebra

open BanachSpectrum

/-- Isometric amalgamation of complete fields implies the common-field
realization of compatible points of actual presented affinoid algebras. -/
theorem pointAmalgamation_of_completeFieldAmalgamation
    (h : CompleteFieldAmalgamationStatement.{u}) : PointAmalgamationStatement.{u} := by
  intro K _ _ _ A B C i j x y hxy
  let z : BanachSpectrum A := comap i.toBoundedRingHom x
  let e : BoundedAlgHom K (CompletedResidueField K z) (CompletedResidueField K x) :=
    completedResidueComap K i x
  let d : BoundedAlgHom K (CompletedResidueField K z) (CompletedResidueField K y) :=
    completedResidueComapOfEq K j z y hxy.symm
  obtain ⟨L, hL, hLU, hLC, hLA, f, g, hfg, hf, hg⟩ :=
    h K (CompletedResidueField K z) (CompletedResidueField K x)
      (CompletedResidueField K y) e d
      (isometry_completedResidueComap K i x)
      (isometry_completedResidueComapOfEq K j z y hxy.symm)
  let := hL
  let := hLU
  let := hLC
  let := hLA
  refine ⟨L, hL, hLU, hLC, hLA,
    f.comp (completedResidueMap K x), g.comp (completedResidueMap K y), ?_, ?_, ?_⟩
  · apply BoundedAlgHom.ext
    intro a
    have heq := congrArg (fun q : BoundedAlgHom K (CompletedResidueField K z) L =>
      q (completedResidueMap K z a)) hfg
    change f (e (completedResidueMap K z a)) =
      g (d (completedResidueMap K z a)) at heq
    change f (completedResidueMap K x (i a)) = g (completedResidueMap K y (j a))
    simpa only [e, d, z, completedResidueComap_map, completedResidueComapOfEq_map] using heq
  · intro b
    change ‖f (completedResidueMap K x b)‖ = x b
    calc
      ‖f (completedResidueMap K x b)‖ = ‖completedResidueMap K x b‖ :=
        (AddMonoidHomClass.isometry_iff_norm f.toAlgHom).mp hf _
      _ = x b := norm_completedResidueMap K x b
  · intro c
    change ‖g (completedResidueMap K y c)‖ = y c
    calc
      ‖g (completedResidueMap K y c)‖ = ‖completedResidueMap K y c‖ :=
        (AddMonoidHomClass.isometry_iff_norm g.toAlgHom).mp hg _
      _ = y c := norm_completedResidueMap K y c

end PresentedAffinoidAlgebra

end Langlands.Analytic
