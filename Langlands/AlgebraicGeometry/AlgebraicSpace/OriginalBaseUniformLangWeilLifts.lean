import Langlands.AlgebraicGeometry.AlgebraicSpace.BaseCompositionRingPoints
import Langlands.AlgebraicGeometry.AlgebraicSpace.BaseCompositionDiagonal
import Langlands.AlgebraicGeometry.AlgebraicSpace.BaseCompositionFibres
import Langlands.AlgebraicGeometry.AlgebraicSpace.UniformLangWeilHenselianLifts

/-! # Uniform fibre estimates with the original coefficient action -/

set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.OriginalBaseUniformLangWeilLifts

open BaseComposition

variable (C : Type u) [CommRing C] [Algebra (ULift.{u} ℤ) C]
  [LocallyOfFiniteType (Spec.algebraMap (ULift.{u} ℤ) C)]

/-- The exact space estimate over the integers gives a single fibre estimate for every
finite-field point with its original coefficient action. -/
theorem exists_bound (hLW : SpaceUniformLangWeilStatement.{u})
    (B Y : AlgebraicSpace (Spec (CommRingCat.of C))) (f : Y ⟶ B) (d : ℕ)
    (hBqs : IsQuasiSeparated B) (hBft : FiniteTypeOverRing C B)
    (chart : EtaleMorphismChart f) (hchart : IsSurjective chart.sourceMap)
    (hdim : SmoothOfRelativeDimension d chart.schemeMap.left)
    (hsep : IsSeparatedMorphism f) (hqc : IsQuasiCompactMorphism f)
    (hsurj : IsSurjectiveMorphism f) (hconn : HasGeometricallyConnectedFibres f) :
    ∃ c : ℝ, 0 < c ∧ ∀ (κ : Type u) [Field κ] [Finite κ] [Algebra C κ]
      (x : RingPoints C B κ),
      |(Nat.card {y : RingPoints C Y κ // RingPoints.map f y = x} : ℝ) -
          (Nat.card κ : ℝ) ^ d| ≤
        c * (Nat.card κ : ℝ) ^ ((d : ℝ) - 1 / 2) := by
  let g := Spec.algebraMap (ULift.{u} ℤ) C
  let c' := morphismChart g chart
  have hd' : SmoothOfRelativeDimension d c'.schemeMap.left :=
    morphismChart_smoothOfRelativeDimension g chart d hdim
  obtain ⟨c, hc, hb⟩ := hLW (space g B) (space g Y) (spaceMap g f) d
    (quasiSeparated_space g hBqs) (finiteTypeOverRing_space g hBft)
    ⟨c'.source, c'.target, c'.sourceMap, c'.targetMap, c'.schemeMap,
      c'.sourceEtale, morphismChart_sourceSurjective g chart hchart, c'.targetEtale,
      hd', c'.comm⟩
    (separated_spaceMap g hsep) (quasiCompact_spaceMap g hqc)
    (surjective_spaceMap g hsurj) (geometricallyConnectedFibres_spaceMap g hconn)
  refine ⟨c, hc, ?_⟩
  intro κ hκ hfin hCκ x
  let : Algebra (ULift.{u} ℤ) κ :=
    ((algebraMap C κ).comp (algebraMap (ULift.{u} ℤ) C)).toAlgebra
  let := IsScalarTower.of_algebraMap_eq (R := ULift.{u} ℤ) (S := C) (A := κ) (fun _ => rfl)
  have h := hb κ (ringPointLift (ULift.{u} ℤ) C κ B x)
  have he := card_ringPointFibre (ULift.{u} ℤ) C κ f x
  exact (congrArg (fun n : ℕ => |(n : ℝ) - (Nat.card κ : ℝ) ^ d| ≤
    c * (Nat.card κ : ℝ) ^ ((d : ℝ) - 1 / 2)) he).mpr h

/-- Under the exact integer-base estimate, one constant gives all original-coefficient
Henselian integral lifts for sufficiently large finite-field quotients. -/
theorem exists_uniform_surjectivity (hLW : SpaceUniformLangWeilStatement.{u})
    (B Y : AlgebraicSpace (Spec (CommRingCat.of C))) (f : Y ⟶ B) (d : ℕ)
    (hBqs : IsQuasiSeparated B) (hBft : FiniteTypeOverRing C B)
    (chart : EtaleMorphismChart f) (hchart : IsSurjective chart.sourceMap)
    (hdim : SmoothOfRelativeDimension d chart.schemeMap.left)
    (hsep : IsSeparatedMorphism f) (hqc : IsQuasiCompactMorphism f)
    (hsurj : IsSurjectiveMorphism f) (hconn : HasGeometricallyConnectedFibres f) :
    ∃ c : ℝ, 0 < c ∧ ∀ (R : Type u) [CommRing R] [HenselianLocalRing R] [Algebra C R]
      (κ : Type u) [Field κ] [Finite κ] [Algebra C κ]
      (φ : R →ₐ[C] κ), Function.Surjective φ → c ^ 2 < (Nat.card κ : ℝ) →
        Function.Surjective (RingPoints.map f : RingPoints C Y R → RingPoints C B R) := by
  obtain ⟨c, hc, hbound⟩ := exists_bound C hLW B Y f d hBqs hBft chart hchart hdim
    hsep hqc hsurj hconn
  let : SmoothOfRelativeDimension d chart.schemeMap.left := hdim
  have hf : IsSmoothMorphism f :=
    ⟨chart.source, chart.target, chart.sourceMap, chart.targetMap, chart.schemeMap,
      chart.sourceEtale, hchart, chart.targetEtale,
      SmoothOfRelativeDimension.smooth d chart.schemeMap.left, chart.comm⟩
  refine ⟨c, hc, ?_⟩
  intro R hR hHen hCR κ hκ hfin hCκ φ hφ hlarge
  exact UniformLangWeilHenselianLifts.surjective_of_bound f hf φ hφ d hc.le hlarge (hbound κ)

/-- Choose actual original-coefficient integral lifts with one common positive constant. -/
def pointLifts (hLW : SpaceUniformLangWeilStatement.{u})
    (B Y : AlgebraicSpace (Spec (CommRingCat.of C))) (f : Y ⟶ B) (d : ℕ)
    (hBqs : IsQuasiSeparated B) (hBft : FiniteTypeOverRing C B)
    (chart : EtaleMorphismChart f) (hchart : IsSurjective chart.sourceMap)
    (hdim : SmoothOfRelativeDimension d chart.schemeMap.left)
    (hsep : IsSeparatedMorphism f) (hqc : IsQuasiCompactMorphism f)
    (hsurj : IsSurjectiveMorphism f) (hconn : HasGeometricallyConnectedFibres f) :
    Σ c : {c : ℝ // 0 < c},
      (R : Type u) → [CommRing R] → [HenselianLocalRing R] → [Algebra C R] →
        (κ : Type u) → [Field κ] → [Finite κ] → [Algebra C κ] →
          (φ : R →ₐ[C] κ) → Function.Surjective φ → c.1 ^ 2 < (Nat.card κ : ℝ) →
            (p : RingPoints C B R) → {x : RingPoints C Y R // RingPoints.map f x = p} := by
  let h := exists_uniform_surjectivity C hLW B Y f d hBqs hBft chart hchart hdim
    hsep hqc hsurj hconn
  refine ⟨⟨Classical.choose h, (Classical.choose_spec h).1⟩, ?_⟩
  intro R hR hHen hCR κ hκ hfin hCκ φ hφ hlarge p
  let hp := (Classical.choose_spec h).2 R κ φ hφ hlarge p
  exact ⟨Classical.choose hp, Classical.choose_spec hp⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace.OriginalBaseUniformLangWeilLifts
