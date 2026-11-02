import Langlands.AlgebraicGeometry.Picard.SquareZeroUnitExactSequence
import Langlands.AlgebraicGeometry.Picard.UnitSheafPushforward
import Langlands.AlgebraicGeometry.Picard.StructureKernelModule
import Langlands.AlgebraicGeometry.Modules.AbelianSheafComparison
import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-! # Actual square-zero unit cohomology and its obstruction map -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000

namespace Langlands.AlgebraicGeometry.Picard.SquareZeroUnitCohomology

open SquareZeroUnitKernels NilpotentUnitReduction SquareZeroUnitExactSequence
open UnitSheafPushforward StructureKernelModule

/-- Actual abelian-sheaf cohomology of the structure-unit sheaf. -/
abbrev unitCohomology (Z : Scheme.{u}) (n : ℕ) :=
  Sheaf.H.{u} (unitsSheaf Z.presheaf Z.sheaf.property) n

variable {X Y : Scheme.{u}} (i : Y ⟶ X)

/-- The underlying additive group of the actual ideal-module cohomology. -/
abbrev idealCohomology (n : ℕ) :=
  (Modules.DerivedSections.cohomology X n).obj (kernelModule i)

/-- Compare actual additive-kernel sheaf cohomology with actual ideal-module cohomology. -/
def idealCohomologyAddEquiv (n : ℕ) :
    Sheaf.H.{u} (schemeAdditiveKernelSheaf i) n ≃+ idealCohomology i n :=
  Modules.AbelianSheafComparison.HAddEquiv X (kernelModule i) n

variable [IsClosedImmersion i] (hi : i.ker ^ 2 = ⊥)

/-- The cohomology map induced by the actual sectionwise map `a ↦ 1+a`. -/
def oneAddMap (n : ℕ) : idealCohomology i n →+ unitCohomology X n :=
  (Sheaf.H.map (schemeOneAdd i hi) n).comp
    (idealCohomologyAddEquiv i n).symm.toAddMonoidHom

/-- Actual unit reduction on cohomology, followed by the homeomorphic pushforward comparison. -/
def reductionMap (n : ℕ) : unitCohomology X n →+ unitCohomology Y n :=
  (nilpotentUnitsCohomologyPushforwardEquiv i ⟨2, hi⟩ n).toAddMonoidHom.comp
    (Sheaf.H.map (unitsReduction i) n)

/-- The actual unit-sequence boundary, expressed in actual ideal-module cohomology. -/
def boundaryMap (n : ℕ) : unitCohomology Y n →+ idealCohomology i (n + 1) :=
  (idealCohomologyAddEquiv i (n + 1)).toAddMonoidHom.comp
    ((Sheaf.H.δ (schemeUnitSequence_shortExact i hi) n (n + 1) rfl).comp
      (nilpotentUnitsCohomologyPushforwardEquiv i ⟨2, hi⟩ n).symm.toAddMonoidHom)

/-- Exactness at unit cohomology on the ambient scheme. -/
theorem oneAddMap_range_iff (n : ℕ) (x : unitCohomology X n) :
    (∃ a : idealCohomology i n, oneAddMap i hi n a = x) ↔
      reductionMap i hi n x = 0 := by
  let S := schemeUnitSequence i hi
  have hS := schemeUnitSequence_shortExact i hi
  constructor
  · rintro ⟨a, rfl⟩
    have hz := ConcreteCategory.congr_hom
      (Sheaf.H.longSequence_exact hS n (n + 1) rfl |>.zero 0)
      ((idealCohomologyAddEquiv i n).symm a)
    change Sheaf.H.map S.g n
      (Sheaf.H.map S.f n ((idealCohomologyAddEquiv i n).symm a)) = 0 at hz
    change (nilpotentUnitsCohomologyPushforwardEquiv i ⟨2, hi⟩ n)
      (Sheaf.H.map S.g n
        (Sheaf.H.map S.f n ((idealCohomologyAddEquiv i n).symm a))) = 0
    rw [hz, map_zero]
  · intro hx
    change (nilpotentUnitsCohomologyPushforwardEquiv i ⟨2, hi⟩ n)
      (Sheaf.H.map S.g n x) = 0 at hx
    have hx' : Sheaf.H.map S.g n x = 0 := by
      apply (nilpotentUnitsCohomologyPushforwardEquiv i ⟨2, hi⟩ n).injective
      simpa only [map_zero] using hx
    obtain ⟨a, ha⟩ := Sheaf.H.longSequence_exact₂ hS x hx'
    refine ⟨idealCohomologyAddEquiv i n a, ?_⟩
    change Sheaf.H.map S.f n
      ((idealCohomologyAddEquiv i n).symm (idealCohomologyAddEquiv i n a)) = x
    simpa only [AddEquiv.symm_apply_apply] using ha

/-- A unit-cohomology class lifts precisely when its actual boundary vanishes. -/
theorem reductionMap_range_iff (n : ℕ) (y : unitCohomology Y n) :
    (∃ x : unitCohomology X n, reductionMap i hi n x = y) ↔
      boundaryMap i hi n y = 0 := by
  let S := schemeUnitSequence i hi
  have hS := schemeUnitSequence_shortExact i hi
  constructor
  · rintro ⟨x, rfl⟩
    have hz := ConcreteCategory.congr_hom
      (Sheaf.H.longSequence_exact hS n (n + 1) rfl |>.zero 1) x
    change Sheaf.H.δ hS n (n + 1) rfl (Sheaf.H.map S.g n x) = 0 at hz
    change idealCohomologyAddEquiv i (n + 1)
      (Sheaf.H.δ hS n (n + 1) rfl
        ((nilpotentUnitsCohomologyPushforwardEquiv i ⟨2, hi⟩ n).symm
          ((nilpotentUnitsCohomologyPushforwardEquiv i ⟨2, hi⟩ n)
            (Sheaf.H.map S.g n x)))) = 0
    rw [AddEquiv.symm_apply_apply, hz, map_zero]
  · intro hy
    change idealCohomologyAddEquiv i (n + 1)
      (Sheaf.H.δ hS n (n + 1) rfl
        ((nilpotentUnitsCohomologyPushforwardEquiv i ⟨2, hi⟩ n).symm y)) = 0 at hy
    have hy' : Sheaf.H.δ hS n (n + 1) rfl
        ((nilpotentUnitsCohomologyPushforwardEquiv i ⟨2, hi⟩ n).symm y) = 0 := by
      apply (idealCohomologyAddEquiv i (n + 1)).injective
      simpa only [map_zero] using hy
    obtain ⟨x, hx⟩ := Sheaf.H.longSequence_exact₃ hS
      ((nilpotentUnitsCohomologyPushforwardEquiv i ⟨2, hi⟩ n).symm y) rfl hy'
    refine ⟨x, ?_⟩
    change (nilpotentUnitsCohomologyPushforwardEquiv i ⟨2, hi⟩ n)
      (Sheaf.H.map S.g n x) = y
    rw [hx, AddEquiv.apply_symm_apply]

/-- Exactness at actual ideal-module cohomology in the next degree. -/
theorem boundaryMap_range_iff (n : ℕ) (a : idealCohomology i (n + 1)) :
    (∃ y : unitCohomology Y n, boundaryMap i hi n y = a) ↔
      oneAddMap i hi (n + 1) a = 0 := by
  let S := schemeUnitSequence i hi
  have hS := schemeUnitSequence_shortExact i hi
  constructor
  · rintro ⟨y, rfl⟩
    have hz := ConcreteCategory.congr_hom
      (Sheaf.H.longSequence_exact hS n (n + 1) rfl |>.zero 2)
      ((nilpotentUnitsCohomologyPushforwardEquiv i ⟨2, hi⟩ n).symm y)
    change Sheaf.H.map S.f (n + 1)
      (Sheaf.H.δ hS n (n + 1) rfl
        ((nilpotentUnitsCohomologyPushforwardEquiv i ⟨2, hi⟩ n).symm y)) = 0 at hz
    change Sheaf.H.map S.f (n + 1)
      ((idealCohomologyAddEquiv i (n + 1)).symm
        (idealCohomologyAddEquiv i (n + 1)
          (Sheaf.H.δ hS n (n + 1) rfl
            ((nilpotentUnitsCohomologyPushforwardEquiv i ⟨2, hi⟩ n).symm y)))) = 0
    simpa only [AddEquiv.symm_apply_apply] using hz
  · intro ha
    change Sheaf.H.map S.f (n + 1) ((idealCohomologyAddEquiv i (n + 1)).symm a) = 0 at ha
    obtain ⟨y, hy⟩ := Sheaf.H.longSequence_exact₁ hS
      ((idealCohomologyAddEquiv i (n + 1)).symm a) ha rfl
    refine ⟨nilpotentUnitsCohomologyPushforwardEquiv i ⟨2, hi⟩ n y, ?_⟩
    change idealCohomologyAddEquiv i (n + 1)
      (Sheaf.H.δ hS n (n + 1) rfl
        ((nilpotentUnitsCohomologyPushforwardEquiv i ⟨2, hi⟩ n).symm
          (nilpotentUnitsCohomologyPushforwardEquiv i ⟨2, hi⟩ n y))) = a
    rw [AddEquiv.symm_apply_apply, hy, AddEquiv.apply_symm_apply]

/-- The actual degree-one lifting obstruction takes values in actual ideal-module H². -/
theorem h1_lift_iff (y : unitCohomology Y 1) :
    (∃ x : unitCohomology X 1, reductionMap i hi 1 x = y) ↔
      boundaryMap i hi 1 y = 0 :=
  reductionMap_range_iff i hi 1 y

end Langlands.AlgebraicGeometry.Picard.SquareZeroUnitCohomology
