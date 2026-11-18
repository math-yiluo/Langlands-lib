import Langlands.GroupScheme.Torus.MultiplicativeTypeFpqcGeometry
import Langlands.GroupScheme.Torus.FppfRelativeTorusDescent
import Langlands.GroupScheme.Torus.MultiplicativeTypeFibralCriterionStatement
import Langlands.GroupScheme.Torus.MultiplicativeTypeFpqcExtensionStatement

/-! # Reduction of fpqc multiplicative-type descent to the fibral criterion -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.FpqcMultiplicativeType

/-- The unchanged fibral criterion implies the full fpqc-descent clause of
the fpqc-and-extension target. The fibral criterion remains an explicit premise. -/
theorem of_fpqcBaseChange_of_fibralCriterion
    (hcrit : MultiplicativeTypeFibralCriterionStatement.{u})
    {S T : Scheme.{u}} (H : GroupScheme S) [Flat H.X.hom]
    [LocallyOfFinitePresentation H.X.hom] [IsAffineHom H.X.hom]
    (b : T ⟶ S) [Flat b] [Surjective b] [QuasiCompact b]
    (hH : RelativeMultiplicativeType.IsMultiplicativeType ((baseChange b).obj H)) :
    RelativeMultiplicativeType.IsMultiplicativeType H := by
  have hcomm : IsCommMonObj ((baseChange b).obj H).X := by
    obtain ⟨𝒰, h𝒰⟩ := hH
    apply isCommMonObj_of_fppfCover 𝒰
    intro i
    obtain ⟨Λ, hΛ, -, ⟨e⟩⟩ := h𝒰 i
    let : AddCommGroup Λ := hΛ
    apply (isCommMonObj_iff_isMulCommutative _).2
    intro U
    refine ⟨⟨fun x y => ?_⟩⟩
    apply (isoPointsEquiv e U).injective
    rw [map_mul, map_mul, mul_comm]
  let : IsCommMonObj H.X := isCommMonObj_of_baseChange b H hcomm
  let H₁ := (baseChange b).obj H
  have : Flat H₁.X.hom := by
    change Flat (pullback.snd _ _)
    infer_instance
  have : LocallyOfFinitePresentation H₁.X.hom := by
    change LocallyOfFinitePresentation (pullback.snd _ _)
    infer_instance
  have : IsAffineHom H₁.X.hom := by
    change IsAffineHom (pullback.snd _ _)
    exact MorphismProperty.pullback_snd H.X.hom b (inferInstanceAs (IsAffineHom H.X.hom))
  obtain ⟨hfib, hord⟩ := ((hcrit T H₁).2).mp hH
  apply ((hcrit S H).2).mpr
  refine ⟨(forall_geometricFiber_isMultiplicativeType_iff b H).mp hfib, ?_⟩
  intro n hn
  change IsLocallyConstant (geometricTorsionOrder H (n : ℤ))
  exact (isLocallyConstant_geometricTorsionOrder_iff b H (n : ℤ)).mp (hord n hn)

end Langlands.GroupScheme.FpqcMultiplicativeType
