import Langlands.AlgebraicGeometry.AlgebraicSpace.UniformLangWeilFiniteFieldLifts
import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianSmoothPointLifting

/-! # Uniform integral lifts for smooth maps of algebraic spaces -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace UniformLangWeilHenselianLifts

/-- A numerical fibre estimate over a sufficiently large residue field gives
surjectivity on actual integral points, with the original coefficient base. -/
theorem surjective_of_bound
    {C R κ : Type u} [CommRing C] [CommRing R] [HenselianLocalRing R]
    [Field κ] [Algebra C R] [Algebra C κ]
    {X Y : AlgebraicSpace (Spec (CommRingCat.of C))} (f : X ⟶ Y)
    (hf : IsSmoothMorphism f) (φ : R →ₐ[C] κ) (hφ : Function.Surjective φ)
    (d : ℕ) {c : ℝ} (hc : 0 ≤ c) (hlarge : c ^ 2 < (Nat.card κ : ℝ))
    (hbound : ∀ x : RingPoints C Y κ,
      |(Nat.card {y : RingPoints C X κ // RingPoints.map f y = x} : ℝ) -
          (Nat.card κ : ℝ) ^ d| ≤
        c * (Nat.card κ : ℝ) ^ ((d : ℝ) - 1 / 2)) :
    Function.Surjective (RingPoints.map f : RingPoints C X R → RingPoints C Y R) :=
  HenselianSmoothPointLifting.surjective_of_residue f hf φ hφ
    (UniformLangWeilFiniteFieldLifts.surjective_of_bound f d hc hlarge hbound)

/-- Assuming the exact space estimate, choose one positive constant and lifts
over every Henselian local ring with a sufficiently large finite field quotient. -/
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
      (R : Type u) → [CommRing R] → [HenselianLocalRing R] → [Algebra (ULift.{u} ℤ) R] →
        (κ : Type u) → [Field κ] → [Finite κ] → [Algebra (ULift.{u} ℤ) κ] →
        (φ : R →ₐ[ULift.{u} ℤ] κ) → Function.Surjective φ →
        c.1 ^ 2 < (Nat.card κ : ℝ) →
        (p : RingPoints (ULift.{u} ℤ) B R) →
        {a : RingPoints (ULift.{u} ℤ) Y R // RingPoints.map f a = p} := by
  let : SmoothOfRelativeDimension d chart.schemeMap.left := hdim
  have hf : IsSmoothMorphism f :=
    ⟨chart.source, chart.target, chart.sourceMap, chart.targetMap, chart.schemeMap,
      chart.sourceEtale, hchart, chart.targetEtale,
      SmoothOfRelativeDimension.smooth d chart.schemeMap.left, chart.comm⟩
  let lifts := UniformLangWeilFiniteFieldLifts.pointLifts hLW B Y f d
    hBqs hBft chart hchart hdim hsep hqc hsurj hconn
  refine ⟨lifts.1, fun R _ _ _ κ _ _ _ φ hφ hlarge p => ?_⟩
  let q := lifts.2 κ (RingPoints.changeRing φ p) hlarge
  let a := HenselianSmoothPointLifting.pointLift f hf φ hφ p q.1 q.2
  exact ⟨a.1, a.2.1⟩

end UniformLangWeilHenselianLifts

end Langlands.AlgebraicGeometry.AlgebraicSpace
