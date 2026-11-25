/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Line.LineProjFractionChartData
public import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
public import WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons
import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSectionAdjunction
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
import WeilConjectures.AlgebraicGeometry.BoundaryPullbackTensorUnit
import WeilConjectures.AlgebraicGeometry.Modules.PullbackSections

/-! # Pullback of generation opens and specified relative-Proj fraction maps

The square is only commutative. The primed algebra is identified degreewise with
its actual tensor pullback, compatibly with the coefficientwise Proj comparison.
The pulled-back homogeneous map is constructed from normalized composition and
power comparisons. All fraction equations are cross-multiplied on generator opens.

## References

* Stacks Project, Divisors on Spaces, Tag 0D2Z, opening assertion and (3)
* Constructions, Tags 01O9 and 01NK
-/

@[expose] public section

set_option linter.privateModule false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

attribute [local irreducible] tensorPullbackObj tensorPullbackMap

private theorem comp_four_congr {X : Scheme.{u}}
    {M₀ M₁ M₂ M₃ M₄ M₅ M₆ : X.Modules}
    (c₁ : M₀ ⟶ M₁) (c₅ : M₄ ⟶ M₅)
    {c₂ d₂ : M₁ ⟶ M₂} {c₃ d₃ : M₂ ⟶ M₃}
    {c₄ d₄ : M₃ ⟶ M₄} {c₆ d₆ : M₅ ⟶ M₆}
    (h₂ : c₂ = d₂) (h₃ : c₃ = d₃) (h₄ : c₄ = d₄) (h₆ : c₆ = d₆) :
    c₁ ≫ c₂ ≫ c₃ ≫ c₄ ≫ c₅ ≫ c₆ = c₁ ≫ d₂ ≫ d₃ ≫ d₄ ≫ c₅ ≫ d₆ := by
  subst d₂ d₃ d₄ d₆
  rfl

private theorem tensor_section_eq_unit {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : Y.Modules) (U : Y.Opens) (s : Γ(M, U)) :
    tensorPullbackSection g M U s =
      ((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app M).app U s := by
  exact (Classical.choose_spec (exists_tensorPullbackAdjunction g) M (op U) s).symm

attribute [local irreducible] tensorPullbackSection

private theorem pushforward_smul {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : X.Modules) (U : Y.Opens) (r : Γ(Y, U)) (s : Γ((pushforward g).obj M, U)) :
    (r • s : Γ((pushforward g).obj M, U)) = g.app U r • (show Γ(M, g ⁻¹ᵁ U) from s) := rfl

private theorem tensor_section_smul {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : Y.Modules) (U : Y.Opens) (r : Γ(Y, U)) (s : Γ(M, U)) :
    tensorPullbackSection g M U (r • s) =
      g.app U r • tensorPullbackSection g M U s := by
  rw [tensor_section_eq_unit, tensor_section_eq_unit]
  exact (Hom.app_smul
    ((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app M) r s).trans
      (pushforward_smul g _ U r _)

private theorem tensor_section_map {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : Y.Modules) {U V : Y.Opens} (h : V ≤ U) (s : Γ(M, U)) :
    tensorPullbackSection g M V (M.presheaf.map (homOfLE h).op s) =
      ((tensorPullback g).obj M).presheaf.map (homOfLE (g.preimage_mono h)).op
        (tensorPullbackSection g M U s) := by
  simp only [tensor_section_eq_unit]
  exact Hom.app_presheaf_map ((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app M)
    (homOfLE h) s

attribute [local irreducible] tensorPullbackSectionComp

private theorem pullback_frame_power {W W' : Scheme.{u}} (h : W' ⟶ W)
    (L : W.Modules) (U : W.Opens) (e : Γ(L, U)) (n : ℕ) :
    (boundaryPullbackPowIso h L n).hom.app (h ⁻¹ᵁ U)
        (tensorPullbackSection h (L.tensorPow n) U (lineProjFramePower L U e n)) =
      lineProjFramePower ((tensorPullback h).obj L) (h ⁻¹ᵁ U)
        (tensorPullbackSection h L U e) n := by
  induction n with
  | zero =>
    change (pullbackObjUnitIso h).hom.app (h ⁻¹ᵁ U)
      (((boundaryPullbackComparison h).hom.app (𝟙_ W.Modules)).app (h ⁻¹ᵁ U)
        (tensorPullbackSection h (𝟙_ W.Modules) U (unitSectionsEquiv U 1))) = _
    rw [tensor_section_eq_unit]
    have hu := (Classical.choose (exists_tensorPullbackAdjunction h)).unit_leftAdjointUniq_hom_app
      (pullbackPushforwardAdjunction h) (𝟙_ W.Modules)
    have hs := congrArg (fun z ↦ z.app U (unitSectionsEquiv U 1)) hu
    change ((boundaryPullbackComparison h).hom.app (𝟙_ W.Modules)).app (h ⁻¹ᵁ U)
      (((Classical.choose (exists_tensorPullbackAdjunction h)).unit.app
        (𝟙_ W.Modules)).app U (unitSectionsEquiv U 1)) = _ at hs
    rw [hs]
    change (pullbackObjUnitIso h).hom.app (h ⁻¹ᵁ U) (pullbackSection h (1 : Γ(W, U))) =
      (1 : Γ(W', h ⁻¹ᵁ U))
    simpa only [map_one] using
      pullbackObjUnitIso_hom_app_pullbackSection h (1 : Γ(W, U))
  | succ n ih =>
    change (Iso.refl ((tensorPullback h).obj L) ⊗ᵢ boundaryPullbackPowIso h L n).hom.app
      (h ⁻¹ᵁ U) ((boundaryPullbackTensorIso h L (L.tensorPow n)).hom.app (h ⁻¹ᵁ U)
        (tensorPullbackSection h (L ⊗ L.tensorPow n) U
          (tmulSection e (lineProjFramePower L U e n)))) =
      tmulSection (tensorPullbackSection h L U e)
        (lineProjFramePower ((tensorPullback h).obj L) (h ⁻¹ᵁ U)
          (tensorPullbackSection h L U e) n)
    rw [tensor_section_eq_unit, boundaryPullbackTensorIso_unit_tmul, tensorIso_hom]
    exact (tensorHom_app_tmulSection (𝟙 ((tensorPullback h).obj L))
      (boundaryPullbackPowIso h L n).hom _ _).trans (by
        simpa only [Hom.id_app, ConcreteCategory.id_apply, ← tensor_section_eq_unit] using
          congrArg (tmulSection (tensorPullbackSection h L U e)) ih)

attribute [local irreducible] boundaryPullbackPowIso

end AlgebraicGeometry.Scheme.Modules
