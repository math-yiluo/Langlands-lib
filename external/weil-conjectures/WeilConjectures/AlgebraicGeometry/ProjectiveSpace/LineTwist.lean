/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineDifferentials
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TwistGenerator

/-!
# The twisting sheaves on the projective line are twisted structure sheaves

Let `S` be a scheme and `ℙ¹_S = ProjectiveLine S`, covered by the standard opens
`U₀ = D₊(x₀)` and `U₁ = D₊(x₁)`. A twisted structure sheaf `𝒪(d)` on `ℙ¹_S` is a module with
generators `g₀` on `U₀` and `g₁` on `U₁` glued by `g₀ = t^{-d} g₁` on `U₀ ∩ U₁`, `t = x₁ / x₀`
(`AlgebraicGeometry.ProjectiveLine.TwistData`). We show that the twisting sheaf
`AlgebraicGeometry.ProjectiveSpace.twist` is one, with generators `x₀ᵈ` and `x₁ᵈ`
(`AlgebraicGeometry.ProjectiveLine.twistData`), and that a twisted structure sheaf is unique up
to unique isomorphism compatible with the generators.

## Main statements

- `AlgebraicGeometry.ProjectiveLine.TwistData.existsUnique_iso`: uniqueness up to unique
  isomorphism compatible with the generators.
- `AlgebraicGeometry.ProjectiveLine.nonempty_twistData`: `𝒪(d)` exists, is invertible and is
  unique.
-/

@[expose] public section

universe u

open CategoryTheory MvPolynomial HomogeneousLocalization

noncomputable section

namespace AlgebraicGeometry.ProjectiveLine

open ProjectiveSpace Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The index type `{0, 1}` of the homogeneous coordinates of `ℙ¹`. -/
local notation "T₂" => ULift (Fin 2)

/-- The index `0`. -/
local notation "j₀" => (⟨0⟩ : ULift (Fin 2))

/-- The index `1`. -/
local notation "j₁" => (⟨1⟩ : ULift (Fin 2))

variable (S : Scheme.{u})

namespace TwistData

variable {S} {d : ℤ} {𝓛 𝓛' : (ProjectiveLine S).Modules}

/-- The generators of a twisted structure sheaf, indexed by `Fin 2`. -/
def gen (D : TwistData S d 𝓛) : (i : Fin 2) → Γ(𝓛, standardOpen T₂ S ⟨i⟩)
  | 0 => D.g₀
  | 1 => D.g₁

lemma isFreeGenerator_gen (D : TwistData S d 𝓛) : ∀ i : Fin 2, IsFreeGenerator (D.gen i)
  | 0 => D.bijective_smul_g₀
  | 1 => D.bijective_smul_g₁

variable (S) in
lemma iSup_standardOpen_up : ⨆ i : Fin 2, standardOpen T₂ S ⟨i⟩ = ⊤ :=
  (Equiv.ulift.symm.iSup_comp (g := fun i ↦ standardOpen T₂ S i)).trans
    (iSup_standardOpen T₂ S)

/-- The glueing relation `g₀ = u₀₁ g₁` restricted to an open `W ⊆ U₀ ∩ U₁`. -/
lemma map_g₀_eq (D : TwistData S d 𝓛) {W : (ProjectiveLine S).Opens}
    (h₀ : W ≤ standardOpen T₂ S j₀) (h₁ : W ≤ standardOpen T₂ S j₁) :
    𝓛.presheaf.map (homOfLE h₀).op D.g₀ =
      (ProjectiveLine S).presheaf.map (homOfLE (le_inf h₀ h₁)).op
          (transitionUnit T₂ S d j₀ j₁).1 •
        𝓛.presheaf.map (homOfLE h₁).op D.g₁ := by
  rw [← presheaf_map_homOfLE_map_homOfLE inf_le_left (le_inf h₀ h₁), D.map_g₀, map_smul,
    presheaf_map_homOfLE_map_homOfLE]

/-- On an open `W ⊆ Uᵢ ∩ Uⱼ`, the relations between the generators `gᵢ`, `gⱼ` of two twisted
structure sheaves of the same degree are the same. -/
lemma smul_gen_eq (D : TwistData S d 𝓛) (D' : TwistData S d 𝓛') :
    ∀ (i j : Fin 2) (W : (ProjectiveLine S).Opens) (hi : W ≤ standardOpen T₂ S ⟨i⟩)
      (hj : W ≤ standardOpen T₂ S ⟨j⟩) (a b : Γ(ProjectiveLine S, W)),
      a • 𝓛.presheaf.map (homOfLE hi).op (D.gen i) =
        b • 𝓛.presheaf.map (homOfLE hj).op (D.gen j) →
      a • 𝓛'.presheaf.map (homOfLE hi).op (D'.gen i) =
        b • 𝓛'.presheaf.map (homOfLE hj).op (D'.gen j)
  | 0, 0, _, hi, _, a, b, h => by
    obtain rfl : a = b := ((D.isFreeGenerator_gen 0).map hi).smul_left_injective h
    rfl
  | 0, 1, _, hi, hj, a, b, h => by
    change a • 𝓛.presheaf.map (homOfLE hi).op D.g₀ = b • 𝓛.presheaf.map (homOfLE hj).op D.g₁
      at h
    change a • 𝓛'.presheaf.map (homOfLE hi).op D'.g₀ = b • 𝓛'.presheaf.map (homOfLE hj).op D'.g₁
    rw [D.map_g₀_eq hi hj, smul_smul] at h
    rw [D'.map_g₀_eq hi hj, smul_smul, ((D.isFreeGenerator_gen 1).map hj).smul_left_injective h]
  | 1, 0, _, hi, hj, a, b, h => by
    change a • 𝓛.presheaf.map (homOfLE hi).op D.g₁ = b • 𝓛.presheaf.map (homOfLE hj).op D.g₀
      at h
    change a • 𝓛'.presheaf.map (homOfLE hi).op D'.g₁ = b • 𝓛'.presheaf.map (homOfLE hj).op D'.g₀
    rw [D.map_g₀_eq hj hi, smul_smul] at h
    rw [D'.map_g₀_eq hj hi, smul_smul, ((D.isFreeGenerator_gen 1).map hi).smul_left_injective h]
  | 1, 1, _, hi, _, a, b, h => by
    obtain rfl : a = b := ((D.isFreeGenerator_gen 1).map hi).smul_left_injective h
    rfl

/-- The morphism of twisted structure sheaves of the same degree sending generators to
generators. -/
def hom (D : TwistData S d 𝓛) (D' : TwistData S d 𝓛') : 𝓛 ⟶ 𝓛' :=
  glueHom (iSup_standardOpen_up S) D.isFreeGenerator_gen (smul_gen_eq D D')

lemma hom_app_gen (D : TwistData S d 𝓛) (D' : TwistData S d 𝓛') (i : Fin 2) :
    (D.hom D').app _ (D.gen i) = D'.gen i :=
  glueHom_app_self _ _ _ i

lemma hom_ext' (D : TwistData S d 𝓛) {φ ψ : 𝓛 ⟶ 𝓛'} (h₀ : φ.app _ D.g₀ = ψ.app _ D.g₀)
    (h₁ : φ.app _ D.g₁ = ψ.app _ D.g₁) : φ = ψ :=
  hom_ext_of_isFreeGenerator (iSup_standardOpen_up S) D.isFreeGenerator_gen fun
    | 0 => h₀
    | 1 => h₁

/-- **Uniqueness of twisted structure sheaves.** Two twisted structure sheaves of the same
degree `d` on `ℙ¹_S` are isomorphic by a unique isomorphism sending the generators `g₀`, `g₁`
of the first to those of the second. -/
theorem existsUnique_iso (D : TwistData S d 𝓛) (D' : TwistData S d 𝓛') :
    ∃! φ : 𝓛 ≅ 𝓛', φ.hom.app _ D.g₀ = D'.g₀ ∧ φ.hom.app _ D.g₁ = D'.g₁ := by
  refine ⟨⟨D.hom D', D'.hom D, D.hom_ext' ?_ ?_, D'.hom_ext' ?_ ?_⟩,
    ⟨D.hom_app_gen D' 0, D.hom_app_gen D' 1⟩, fun φ hφ ↦ Iso.ext (D.hom_ext' ?_ ?_)⟩
  · rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
    erw [D.hom_app_gen D' 0, D'.hom_app_gen D 0]
    rfl
  · rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
    erw [D.hom_app_gen D' 1, D'.hom_app_gen D 1]
    rfl
  · rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
    erw [D'.hom_app_gen D 0, D.hom_app_gen D' 0]
    rfl
  · rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
    erw [D'.hom_app_gen D 1, D.hom_app_gen D' 1]
    rfl
  · exact hφ.1.trans (D.hom_app_gen D' 0).symm
  · exact hφ.2.trans (D.hom_app_gen D' 1).symm

end TwistData

/-- **The twists `𝒪(d)` exist.** For every `d ∈ ℤ`, a twisted structure sheaf `𝒪(d)` on `ℙ¹_S`
in the sense of `AlgebraicGeometry.ProjectiveLine.TwistData` (generators `g₀` on `U₀`, `g₁` on
`U₁`, glued by `g₀ = t^{-d} g₁`) exists, namely the twisting sheaf
`AlgebraicGeometry.ProjectiveSpace.twist` (`AlgebraicGeometry.ProjectiveLine.twistData`); it is
an invertible module; and it is unique up to unique isomorphism compatible with the generators
(`AlgebraicGeometry.ProjectiveLine.TwistData.existsUnique_iso`). -/
theorem nonempty_twistData (d : ℤ) :
    Nonempty (TwistData S d (twist T₂ S d)) ∧ (twist T₂ S d).IsInvertible ∧
      ∀ {𝓛 𝓛' : (ProjectiveLine S).Modules} (D : TwistData S d 𝓛) (D' : TwistData S d 𝓛'),
        ∃! φ : 𝓛 ≅ 𝓛', φ.hom.app _ D.g₀ = D'.g₀ ∧ φ.hom.app _ D.g₁ = D'.g₁ :=
  ⟨⟨twistData S d⟩, inferInstance, fun D D' ↦ D.existsUnique_iso D'⟩

end AlgebraicGeometry.ProjectiveLine
