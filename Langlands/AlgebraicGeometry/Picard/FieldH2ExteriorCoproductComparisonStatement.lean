import Langlands.AlgebraicGeometry.Picard.FieldH2PrimitiveInjectivityStatement
import Langlands.LinearAlgebra.ExteriorPowerTensorInjectivity

/-! # Degree-two exterior and Künneth comparison for abelian varieties -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- The degree-two exterior description and Künneth decomposition, with explicit
formulas for the three canonical cohomology pullbacks. This is an unproved
geometric comparison target. -/
def FieldH2ExteriorCoproductComparisonStatement : Prop :=
  ∀ (K : Type u) [Field K] (A : AbelianScheme (Spec (CommRingCat.of K))),
    let P : Over (Spec (CommRingCat.of K)) := A.X ⨯ A.X
    let p1 : P ⟶ A.X := Limits.prod.fst
    let p2 : P ⟶ A.X := Limits.prod.snd
    let m : P ⟶ A.X := p1 * p2
    let O := SheafOfModules.unit A.X.left.ringCatSheaf
    let H1 := (relativeCohomology A.X.hom 1).obj O
    let H2 := (relativeCohomology A.X.hom 2).obj O
    let HP2 := (relativeCohomology P.hom 2).obj
      (SheafOfModules.unit P.left.ringCatSheaf)
    let pull (f : P ⟶ A.X) :=
      (relativeCohomologyPullback f O 2 ≫
        (relativeCohomology P.hom 2).map
          (Langlands.Scheme.Modules.pullbackUnitIso f.left).hom).hom
    ∃ (e : H2 ≃ₗ[K] ⋀[K]^2 H1)
      (κ : HP2 ≃ₗ[K] H2 × (⨂[K]^2 H1) × H2),
      (∀ x, κ (pull p1 x) = (x, 0, 0)) ∧
      (∀ x, κ (pull p2 x) = (0, 0, x)) ∧
      (∀ x, κ (pull m x) =
        (x, exteriorPower.toTensorPower K H1 2 (e x), x))

/-- The explicit geometric comparison implies injectivity of the actual
reduced coproduct in degree two. -/
theorem fieldH2PrimitiveInjectivity_of_exteriorCoproductComparison
    (h : FieldH2ExteriorCoproductComparisonStatement.{u}) :
    FieldH2PrimitiveInjectivityStatement.{u} := by
  intro K _ A
  dsimp only
  obtain ⟨e, κ, hp1, hp2, hm⟩ := h K A
  intro x y hxy
  apply e.injective
  apply Langlands.LinearAlgebra.exteriorPowerToTensorPower_injective K _ 2
  have hκ := congrArg (fun z => (κ z).2.1) hxy
  simpa only [LinearMap.sub_apply, map_sub, hm, hp1, hp2, Prod.fst_sub,
    Prod.snd_sub, sub_zero] using hκ

end Langlands.AbelianScheme
