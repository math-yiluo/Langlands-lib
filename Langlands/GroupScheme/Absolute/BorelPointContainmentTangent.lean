import Langlands.GroupScheme.Absolute.BorelPointContainmentDensity
import Langlands.AlgebraicGeometry.TangentSmoothness
import Langlands.GroupScheme.Lie.PointTangent
import Langlands.GroupScheme.Lie.KernelTargetMaps
import Langlands.GroupScheme.ConjugacyBaseChange

/-! # Tangent surjectivity of the conjugation map of a dynamic centralizer -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace BorelPointContainment

open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.TangentSmoothness

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

/-- **Tangent criterion for the conjugation map.** Let `j : H ⟶ G` and let `z₀` be a rational
point of `H` with image `g₀ = j(z₀)`. If every Lie vector `W` of `G` has the form
`Ad(g₀⁻¹) X · dj(ξ) · X⁻¹` for Lie vectors `X` of `G` and `ξ` of `H`, then the conjugation map
`(x, h) ↦ x j(h) x⁻¹` is surjective on rational tangent vectors at `(1, z₀)`. -/
theorem isTangentSurjectiveAt_conjugation {G H : GroupScheme (Spec (CommRingCat.of k))}
    (j : H ⟶ G) (z₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)
    (h : ∀ W : lieKernel G k, ∃ (X : lieKernel G k) (ξ : lieKernel H k),
      lieKernelConjugation G (G.constantPoint (z₀ ≫ j.hom.hom)
          ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) k))))⁻¹ X *
        Lie.targetMap j k ξ * X⁻¹ = W) :
    IsTangentSurjectiveAt (G.X ⊗ H.X).hom G.X.hom (conjugation j).left
      (lift 1 z₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X ⊗ H.X).left := by
  rintro t ⟨ht₁, ht₂⟩
  let D := (algSpec (CommRingCat.of k)).obj
    (op (CommAlgCat.of (CommRingCat.of k) (DualNumber k)))
  let T : D ⟶ G.X := Over.homMk t ht₁
  let a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ D :=
    Over.homMk (dualNumberAugmentation k) dualNumberAugmentation_comp_dualNumberProjection
  let g₀ := z₀ ≫ j.hom.hom
  have hT : a ≫ T = g₀ := by
    apply Over.OverMorphism.ext
    refine ht₂.trans ?_
    change (lift 1 z₀ ≫ conjugation j).left = g₀.left
    rw [lift_conjugation, one_mul, inv_one, mul_one]
  let C := G.constantPoint g₀ D
  have hC : a ≫ C = g₀ := by
    rw [constantPoint_naturality, constantPoint_self]
  let w : D ⟶ G.X := C⁻¹ * T
  have hw : a ≫ w = 1 := by
    rw [MonObj.comp_mul, GrpObj.comp_inv, hC, hT, inv_mul_cancel]
  let W : lieKernel G k := (Lie.kernelTangentEquiv G).symm ⟨w.left, Over.w w, by
    have e := congrArg (fun f => f.left) hw
    exact e⟩
  have hW : W.val = w := Over.OverMorphism.ext rfl
  obtain ⟨X, ξ, hXξ⟩ := h W
  have hX : a ≫ X.val = 1 :=
    Over.OverMorphism.ext (Lie.kernelTangentEquiv G X).property.2
  have hξ : a ≫ ξ.val = 1 :=
    Over.OverMorphism.ext (Lie.kernelTangentEquiv H ξ).property.2
  let s : D ⟶ G.X ⊗ H.X := lift X.val (H.constantPoint z₀ D * ξ.val)
  have hs₁ : a ≫ s = lift 1 z₀ := by
    rw [comp_lift, MonObj.comp_mul, hX, hξ, constantPoint_naturality, constantPoint_self,
      mul_one]
  have hconst : Lie.constant G (G.constantPoint g₀
      ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) k)))) = C :=
    G.constantPoint_naturality g₀ _
  have hval := congrArg Subtype.val hXξ
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, lieKernelConjugation_val, map_inv,
    hW] at hval
  change (Lie.constant G (G.constantPoint g₀ _))⁻¹ * X.val *
    (Lie.constant G (G.constantPoint g₀ _))⁻¹⁻¹ * (Lie.targetMap j k ξ).val * X.val⁻¹ = w at hval
  rw [hconst] at hval
  have hs₂ : s ≫ conjugation j = T := by
    rw [lift_conjugation, MonObj.mul_comp, constantPoint_comp]
    change X.val * (C * (Lie.targetMap j k ξ).val) * X.val⁻¹ = T
    calc X.val * (C * (Lie.targetMap j k ξ).val) * X.val⁻¹
        = C * (C⁻¹ * X.val * C⁻¹⁻¹ * (Lie.targetMap j k ξ).val * X.val⁻¹) := by group
      _ = C * (C⁻¹ * T) := by rw [hval]
      _ = T := by group
  exact ⟨s.left, ⟨Over.w s, congrArg CommaMorphism.left hs₁⟩, congrArg CommaMorphism.left hs₂⟩

end BorelPointContainment

end Langlands.GroupScheme
