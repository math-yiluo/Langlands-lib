/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TwistTensor
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Transition

/-!
# The transition rule for the generators of the twisting sheaves

On the overlap `Uᵢ ∩ Uⱼ` of two standard opens of `ℙ(n; S)`, the free generators
`e_i^{(d)} = xᵢᵈ` of `𝒪(d)` (`AlgebraicGeometry.ProjectiveSpace.twistGenerator`) satisfy
`e_i^{(d)} = (xᵢ / xⱼ)ᵈ • e_j^{(d)}`, where `(xᵢ / xⱼ)ᵈ` is the transition unit
`AlgebraicGeometry.ProjectiveSpace.transitionUnit`. In particular `𝒪(d)` on `ℙ¹_S` is a twisted
structure sheaf in the sense of `AlgebraicGeometry.ProjectiveLine.TwistData`.

## Main results

- `AlgebraicGeometry.ProjectiveSpace.map_twistGenerator_eq_transitionUnit_smul`: the transition
  rule `e_i^{(d)} = u_{ij} • e_j^{(d)}` on `Uᵢ ∩ Uⱼ`.
- `AlgebraicGeometry.ProjectiveLine.twistData`: the twist data of `𝒪(d)` on `ℙ¹_S`.
-/

@[expose] public section

universe u

open CategoryTheory MvPolynomial HomogeneousLocalization

noncomputable section

namespace AlgebraicGeometry.ProjectiveSpace

open Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : Type u) (S : Scheme.{u})

/-- **The transition rule for the generators of `𝒪(d)`**: on the overlap `Uᵢ ∩ Uⱼ` of the
standard opens of `ℙ(n; S)`, the free generators `e_i^{(d)} = xᵢᵈ` and `e_j^{(d)} = xⱼᵈ` satisfy
`e_i^{(d)} = (xᵢ / xⱼ)ᵈ • e_j^{(d)}`, where `(xᵢ / xⱼ)ᵈ = transitionUnit n S d i j`. -/
theorem map_twistGenerator_eq_transitionUnit_smul (d : ℤ) (i j : n) :
    (twist n S d).presheaf.map (homOfLE inf_le_left).op (twistGenerator n S d i) =
      (transitionUnit n S d i j).1 •
        (twist n S d).presheaf.map (homOfLE inf_le_right).op (twistGenerator n S d j) := by
  have hXi := X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) i
  have hXj := X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) (σ := n) j
  let V := Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X i) ⊓
    Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X j)
  have hVi : V ≤ _ := inf_le_left
  have hVj : V ≤ _ := inf_le_right
  have h1 := Proj.map_awayToSection_smul_twistPowSection_one hXi hXj
    (by simpa using hXi) hVi hVj
  obtain ⟨u₀, hu₀⟩ := ((Proj.isFreeGenerator_twistPowSection 1 hXj).map hVj).exists_unit_smul_eq
    ((Proj.isFreeGenerator_twistPowSection 1 hXi).map hVi)
  have hc : u₀.1 = _ := ((Proj.isFreeGenerator_twistPowSection 1 hXj).map
    hVj).smul_left_injective (hu₀.symm.trans h1.symm)
  have hW : standardOpen n S i ⊓ standardOpen n S j ≤ toProjInt n S ⁻¹ᵁ V :=
    fun x hx ↦ ⟨hx.1, hx.2⟩
  have H := pullbackSection_smul_map_eq (toProjInt n S) hVi hVj
    (Proj.zpow_smul_map_twistPowSection hXi hXj hVi hVj u₀ hu₀.symm d) hW
  refine H.symm.trans (congrArg (· • _) ?_)
  let φ := ((toProjInt n S).appLE V _ hW).hom
  have key : (Proj (homogeneousSubmodule n (ULift.{u} ℤ))).presheaf.map (homOfLE hVj).op ≫
      (toProjInt n S).appLE V _ hW = (toProjInt n S).appLE (Proj.basicOpen _ (X j))
        (standardOpen n S i ⊓ standardOpen n S j) inf_le_right := by
    rw [Scheme.Hom.map_appLE]
  have hu : Units.map φ.toMonoidHom u₀ = ratioUnit n S i j := by
    refine Units.ext ?_
    rw [Units.coe_map, hc]
    exact ConcreteCategory.congr_hom key _
  rw [transitionUnit, ← hu, ← map_zpow]
  rfl

end AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.ProjectiveLine

open ProjectiveSpace

variable (S : Scheme.{u})

/-- **The twisting sheaf `𝒪(d)` on `ℙ¹_S` as a twisted structure sheaf**: the generators are
`g₀ = x₀ᵈ` over `U₀` and `g₁ = x₁ᵈ` over `U₁` (`ProjectiveSpace.twistGenerator`), which satisfy
the glueing relation `g₀ = t^{-d} g₁ = (x₀ / x₁)ᵈ g₁` over `U₀ ∩ U₁`
(`ProjectiveSpace.map_twistGenerator_eq_transitionUnit_smul`). -/
def twistData (d : ℤ) : TwistData S d (twist (ULift.{u} (Fin 2)) S d) where
  g₀ := twistGenerator (ULift.{u} (Fin 2)) S d ⟨0⟩
  g₁ := twistGenerator (ULift.{u} (Fin 2)) S d ⟨1⟩
  bijective_smul_g₀ := isFreeGenerator_twistGenerator (ULift.{u} (Fin 2)) S d ⟨0⟩
  bijective_smul_g₁ := isFreeGenerator_twistGenerator (ULift.{u} (Fin 2)) S d ⟨1⟩
  map_g₀ := map_twistGenerator_eq_transitionUnit_smul (ULift.{u} (Fin 2)) S d ⟨0⟩ ⟨1⟩

end AlgebraicGeometry.ProjectiveLine
