import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceUniformLangWeilStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothMorphismCharts
import Langlands.AlgebraicGeometry.UniformLangWeilRationalSections

/-! # Actual algebraic-space fibre points from a uniform Lang–Weil estimate -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace UniformLangWeilFiniteFieldLifts

/-- The numerical Lang–Weil bound gives a point of the actual point-map fibre
when the field cardinality is larger than the square of the error constant. -/
theorem nonempty_fibre_of_bound
    {C κ : Type u} [CommRing C] [Field κ] [Algebra C κ]
    {X Y : AlgebraicSpace (Spec (CommRingCat.of C))} (f : X ⟶ Y)
    (x : RingPoints C Y κ) (d : ℕ) {c : ℝ} (hc : 0 ≤ c)
    (hlarge : c ^ 2 < (Nat.card κ : ℝ))
    (hbound :
      |(Nat.card {y : RingPoints C X κ // RingPoints.map f y = x} : ℝ) -
          (Nat.card κ : ℝ) ^ d| ≤
        c * (Nat.card κ : ℝ) ^ ((d : ℝ) - 1 / 2)) :
    Nonempty {y : RingPoints C X κ // RingPoints.map f y = x} := by
  have hpos : 0 < Nat.card {y : RingPoints C X κ // RingPoints.map f y = x} := by
    exact_mod_cast Langlands.AlgebraicGeometry.langWeil_count_pos d hc hlarge hbound
  exact (Nat.card_pos_iff.mp hpos).1

/-- Assuming the exact published algebraic-space estimate, choose one positive
constant and actual lifts over every sufficiently large finite field. The
smooth chart and all the estimate's geometric premises remain explicit. -/
def pointLifts
    (hLW : SpaceUniformLangWeilStatement.{u})
    (B Y : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (f : Y ⟶ B) (d : ℕ)
    (hBqs : IsQuasiSeparated B) (hBft : FiniteTypeOverRing (ULift.{u} ℤ) B)
    (chart : EtaleMorphismChart f) (hchart : IsSurjective chart.sourceMap)
    (hdim : SmoothOfRelativeDimension d chart.schemeMap.left)
    (hsep : IsSeparatedMorphism f) (hqc : IsQuasiCompactMorphism f)
    (hsurj : IsSurjectiveMorphism f) (hconn : HasGeometricallyConnectedFibres f) :
    Σ c : {c : ℝ // 0 < c},
      (κ : Type u) → [Field κ] → [Finite κ] → [Algebra (ULift.{u} ℤ) κ] →
        (x : RingPoints (ULift.{u} ℤ) B κ) →
        c.1 ^ 2 < (Nat.card κ : ℝ) →
        {y : RingPoints (ULift.{u} ℤ) Y κ // RingPoints.map f y = x} := by
  let estimate := hLW B Y f d hBqs hBft
    ⟨chart.source, chart.target, chart.sourceMap, chart.targetMap, chart.schemeMap,
      chart.sourceEtale, hchart, chart.targetEtale, hdim, chart.comm⟩
    hsep hqc hsurj hconn
  let c := estimate.choose
  have hc : 0 < c := estimate.choose_spec.1
  refine ⟨⟨c, hc⟩, fun κ _ _ _ x hlarge => ?_⟩
  exact Classical.choice (nonempty_fibre_of_bound f x d hc.le hlarge
    (estimate.choose_spec.2 κ x))

/-- The same constant makes the actual finite-field point map surjective. -/
theorem surjective_of_bound
    {C κ : Type u} [CommRing C] [Field κ] [Algebra C κ]
    {X Y : AlgebraicSpace (Spec (CommRingCat.of C))} (f : X ⟶ Y)
    (d : ℕ) {c : ℝ} (hc : 0 ≤ c) (hlarge : c ^ 2 < (Nat.card κ : ℝ))
    (hbound : ∀ x : RingPoints C Y κ,
      |(Nat.card {y : RingPoints C X κ // RingPoints.map f y = x} : ℝ) -
          (Nat.card κ : ℝ) ^ d| ≤
        c * (Nat.card κ : ℝ) ^ ((d : ℝ) - 1 / 2)) :
    Function.Surjective (RingPoints.map f : RingPoints C X κ → RingPoints C Y κ) := by
  intro x
  obtain ⟨⟨y, hy⟩⟩ := nonempty_fibre_of_bound f x d hc hlarge (hbound x)
  exact ⟨y, hy⟩

end UniformLangWeilFiniteFieldLifts

end Langlands.AlgebraicGeometry.AlgebraicSpace
