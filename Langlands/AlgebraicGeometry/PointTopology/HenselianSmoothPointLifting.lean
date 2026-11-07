import Langlands.CommutativeAlgebra.HenselianSections
import Langlands.AlgebraicGeometry.PointTopology.ProductRingPoints

/-! # Lifting smooth scheme points from the residue field to a Henselian local ring -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

section Schemes

variable {R K : Type u} [CommRing R] [HenselianLocalRing R] [Field K] [Algebra R K]

/-- A residue-field point above a prescribed integral target point lifts through a
smooth morphism, with its original reduction preserved. -/
theorem exists_smooth_lift_of_residue_point
    (hK : Function.Surjective (algebraMap R K)) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Smooth f] (p : Spec (CommRingCat.of R) ⟶ Y)
    (q : Spec (CommRingCat.of K) ⟶ X)
    (hq : q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ p) :
    ∃ a : Spec (CommRingCat.of R) ⟶ X, a ≫ f = p ∧
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ a = q := by
  let b : Spec (CommRingCat.of K) ⟶ pullback f p :=
    pullback.lift q (Spec.map (CommRingCat.ofHom (algebraMap R K))) hq
  obtain ⟨σ, hσ, hσb⟩ :=
    Langlands.CommutativeAlgebra.HenselianSections.exists_section_of_smooth_of_surjective
      hK (pullback.snd f p) b (pullback.lift_snd _ _ _)
  refine ⟨σ ≫ pullback.fst f p, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hσ, Category.id_comp]
  · rw [← Category.assoc, hσb]
    exact pullback.lift_fst _ _ _

end Schemes

section RelativePoints

variable {C R K : Type u} [CommRing C] [CommRing R] [HenselianLocalRing R]
  [Field K] [Algebra C R] [Algebra C K]
variable {X Y : Over (Spec (CommRingCat.of C))} (f : X ⟶ Y) [Smooth f.left]
variable (φ : R →ₐ[C] K) (hφ : Function.Surjective φ)

include hφ

/-- The relative point lift is over the original coefficient base and has exactly
the supplied residue point. -/
theorem exists_henselian_smooth_point_lift
    (p : RingPoint C Y R) (q : RingPoint C X K)
    (hq : q ≫ f = RingPoint.changeRing φ p) :
    ∃ a : RingPoint C X R, a ≫ f = p ∧ RingPoint.changeRing φ a = q := by
  let : Algebra R K := φ.toRingHom.toAlgebra
  obtain ⟨a, ha, haq⟩ := exists_smooth_lift_of_residue_point hφ f.left p.left q.left
    (congrArg (fun t => t.left) hq)
  let aR : RingPoint C X R := Over.homMk a (by
    change a ≫ X.hom = Spec.algebraMap C R
    rw [← Over.w f, ← Category.assoc, ha]
    exact Over.w p)
  refine ⟨aR, ?_, ?_⟩
  · exact RingPoint.ext C ha
  · exact RingPoint.ext C haq

/-- A chosen actual integral lift together with both exact compatibility
equations; no new point presentation is introduced. -/
def henselianSmoothPointLift
    (p : RingPoint C Y R) (q : RingPoint C X K)
    (hq : q ≫ f = RingPoint.changeRing φ p) :
    {a : RingPoint C X R // a ≫ f = p ∧ RingPoint.changeRing φ a = q} :=
  ⟨(exists_henselian_smooth_point_lift f φ hφ p q hq).choose,
    (exists_henselian_smooth_point_lift f φ hφ p q hq).choose_spec⟩

/-- Surjectivity on residue-field points implies surjectivity on integral points
for a smooth map over a Henselian local ring. -/
theorem surjective_integralPointMap_of_surjective_residuePointMap
    (hf : Function.Surjective (fun q : RingPoint C X K => q ≫ f)) :
    Function.Surjective (fun p : RingPoint C X R => p ≫ f) := by
  intro p
  obtain ⟨q, hq⟩ := hf (RingPoint.changeRing φ p)
  obtain ⟨a, ha, _⟩ := exists_henselian_smooth_point_lift f φ hφ p q hq
  exact ⟨a, ha⟩

end RelativePoints

end Langlands.AlgebraicGeometry.PointTopology
