/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts

/-!
# The transition units of the twisting sheaves on projective space

On the overlap `Uᵢ ∩ Uⱼ` of two standard opens `Uᵢ = D₊(xᵢ)` of `ℙ(n; S)`, the quotient
`xᵢ / xⱼ` of homogeneous coordinates is a unit. The twisting sheaf `𝒪(d)` is obtained by gluing
free rank-one modules on the `Uᵢ` along the units `(xᵢ / xⱼ)^d`, and these satisfy the cocycle
rule on triple overlaps.

The quotients are pulled back from the integral model `Proj ℤ[Tᵢ]`, where `xᵢ / xⱼ` is the
degree-zero fraction `Tᵢ / Tⱼ` of `ℤ[Tᵢ]_{Tⱼ}`, a section over `D₊(Tⱼ)`.

## Main definitions

- `AlgebraicGeometry.ProjectiveSpace.ratio`: the section `xᵢ / xⱼ` over `Uᵢ ∩ Uⱼ`.
- `AlgebraicGeometry.ProjectiveSpace.ratioUnit`: the unit `xᵢ / xⱼ` over `Uᵢ ∩ Uⱼ`.
- `AlgebraicGeometry.ProjectiveSpace.transitionUnit`: the transition unit `(xᵢ / xⱼ)^d` of the
  twisting sheaf `𝒪(d)`.
- `AlgebraicGeometry.ProjectiveLine.TwistData`: a twisted structure sheaf `𝒪(d)` on `ℙ¹_S`,
  i.e. a module with generators on the two standard opens glued by `g₀ = t^{-d} g₁`.

## Main results

- `AlgebraicGeometry.ProjectiveSpace.transitionUnit_mul_transitionUnit`: the cocycle rule
  `u_{ij} u_{jk} = u_{ik}` on `Uᵢ ∩ Uⱼ ∩ U_k`.
-/

@[expose] public section

universe u

open CategoryTheory MvPolynomial HomogeneousLocalization

noncomputable section

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : Type u) (S : Scheme.{u})

/-- The degree-zero fraction `Tᵢ / Tⱼ` of the localization `ℤ[T]_{Tⱼ}`. -/
def awayRatio (i j : n) : Away (homogeneousSubmodule n (ULift.{u} ℤ)) (X j) :=
  Away.mk _ (X_mem_homogeneousSubmodule_one _ j) 1 (X i)
    (by simpa using X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) i)

/-- The quotient `xᵢ / xⱼ` of homogeneous coordinates, a function on the overlap `Uᵢ ∩ Uⱼ` of
the standard opens of `ℙ(n; S)`: the pullback of the section `Tᵢ / Tⱼ` of the integral model
over `D₊(Tⱼ)`. -/
def ratio (i j : n) : Γ(ℙ(n; S), standardOpen n S i ⊓ standardOpen n S j) :=
  (toProjInt n S).appLE (Proj.basicOpen _ (X j)) _ inf_le_right
    (Proj.awayToSection _ (X j) (awayRatio n i j))

variable {n S}

/-- The restriction of `xᵢ / xⱼ` to an open contained in the preimage of `D₊(x)`, for a
multiple `x = Tⱼ g` of `Tⱼ`, computed in the degree-zero part of `ℤ[T]ₓ`. -/
lemma map_ratio {i j : n} {e : ℕ} {g : MvPolynomial n (ULift.{u} ℤ)}
    (hg : g ∈ homogeneousSubmodule n (ULift.{u} ℤ) e) {x : MvPolynomial n (ULift.{u} ℤ)}
    (hx : x = X j * g) {W : ℙ(n; S).Opens}
    (hW : W ≤ toProjInt n S ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) x)
    (hW' : W ≤ standardOpen n S i ⊓ standardOpen n S j) :
    ℙ(n; S).presheaf.map (homOfLE hW').op (ratio n S i j) =
      (Proj.awayToSection _ x ≫ (toProjInt n S).appLE _ W hW)
        (awayMap _ hg hx (awayRatio n i j)) := by
  have key : Proj.awayToSection _ (X j) ≫ (toProjInt n S).appLE _ _ inf_le_right ≫
      ℙ(n; S).presheaf.map (homOfLE hW').op =
      CommRingCat.ofHom (awayMap _ hg hx) ≫ Proj.awayToSection _ x ≫
        (toProjInt n S).appLE _ W hW := by
    rw [Scheme.Hom.appLE_map, Proj.awayMap_awayToSection_assoc, Scheme.Hom.map_appLE]
  have := ConcreteCategory.congr_hom key (awayRatio n i j)
  simp only [CategoryTheory.comp_apply] at this ⊢
  exact this

lemma val_awayMap_awayRatio {i j : n} {e : ℕ} {g : MvPolynomial n (ULift.{u} ℤ)}
    (hg : g ∈ homogeneousSubmodule n (ULift.{u} ℤ) e) {x : MvPolynomial n (ULift.{u} ℤ)}
    (hx : x = X j * g) :
    (awayMap _ hg hx (awayRatio n i j)).val =
      Localization.mk (X i * g) ⟨x, Submonoid.mem_powers x⟩ := by
  rw [awayRatio, awayMap_mk, Away.val_mk]
  simp

/-- Two sections over `W`, pulled back from the degree-zero part of `ℤ[T]ₓ` for some `x` with
`W ⊆ D₊(x)`, agree if the fractions agree. -/
lemma appLE_awayToSection_congr {x : MvPolynomial n (ULift.{u} ℤ)} {W : ℙ(n; S).Opens}
    (hW : W ≤ toProjInt n S ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) x)
    {a b : Away (homogeneousSubmodule n (ULift.{u} ℤ)) x} (h : a.val = b.val) :
    (Proj.awayToSection _ x ≫ (toProjInt n S).appLE _ W hW) a =
      (Proj.awayToSection _ x ≫ (toProjInt n S).appLE _ W hW) b := by
  rw [val_injective _ h]

lemma standardOpen_inf_le (i j : n) :
    standardOpen n S i ⊓ standardOpen n S j ≤ toProjInt n S ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X i * X j) := by
  rw [Proj.basicOpen_mul]
  exact le_rfl

lemma standardOpen_inf_inf_le (i j k : n) :
    standardOpen n S i ⊓ standardOpen n S j ⊓ standardOpen n S k ≤ toProjInt n S ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X i * X j * X k) := by
  rw [Proj.basicOpen_mul, Proj.basicOpen_mul]
  exact le_rfl

/-- `(xᵢ / xⱼ) (xⱼ / xᵢ) = 1` on `Uᵢ ∩ Uⱼ`. -/
lemma ratio_mul_map_ratio (i j : n) :
    ratio n S i j * ℙ(n; S).presheaf.map (homOfLE (inf_comm _ _).le).op (ratio n S j i) = 1 := by
  rw [← (show ℙ(n; S).presheaf.map (homOfLE le_rfl).op (ratio n S i j) = ratio n S i j from
      by simp),
    map_ratio (X_mem_homogeneousSubmodule_one _ i) (x := X i * X j) (by ring)
      (standardOpen_inf_le i j),
    map_ratio (X_mem_homogeneousSubmodule_one _ j) (x := X i * X j) rfl
      (standardOpen_inf_le i j), ← map_mul,
    ← map_one (Proj.awayToSection _ (X i * X j) ≫
      (toProjInt n S).appLE _ _ (standardOpen_inf_le i j)).hom]
  refine appLE_awayToSection_congr _ ?_
  rw [val_mul, val_awayMap_awayRatio, val_awayMap_awayRatio, val_one, Localization.mk_mul,
    ← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp; ring⟩

variable (n S) in
/-- **The unit `xᵢ / xⱼ`** on the overlap `Uᵢ ∩ Uⱼ` of two standard opens of `ℙ(n; S)`, with
inverse `xⱼ / xᵢ`. -/
def ratioUnit (i j : n) : Γ(ℙ(n; S), standardOpen n S i ⊓ standardOpen n S j)ˣ where
  val := ratio n S i j
  inv := ℙ(n; S).presheaf.map (homOfLE (inf_comm _ _).le).op (ratio n S j i)
  val_inv := ratio_mul_map_ratio i j
  inv_val := by rw [mul_comm]; exact ratio_mul_map_ratio i j

/-- The cocycle rule `(xᵢ / xⱼ) (xⱼ / x_k) = xᵢ / x_k` for the ratios, on `Uᵢ ∩ Uⱼ ∩ U_k`. -/
lemma map_ratio_mul_map_ratio (i j k : n) :
    ℙ(n; S).presheaf.map (homOfLE (inf_le_left :
        standardOpen n S i ⊓ standardOpen n S j ⊓ standardOpen n S k ≤ _)).op
        (ratio n S i j) *
      ℙ(n; S).presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        standardOpen n S i ⊓ standardOpen n S j ⊓ standardOpen n S k ≤
          standardOpen n S j ⊓ standardOpen n S k)).op (ratio n S j k) =
      ℙ(n; S).presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        standardOpen n S i ⊓ standardOpen n S j ⊓ standardOpen n S k ≤
          standardOpen n S i ⊓ standardOpen n S k)).op (ratio n S i k) := by
  have hi := X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) i
  have hj := X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) j
  have hk := X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) k
  rw [map_ratio (SetLike.mul_mem_graded hi hk) (x := X i * X j * X k) (by ring)
      (standardOpen_inf_inf_le i j k),
    map_ratio (SetLike.mul_mem_graded hi hj) (x := X i * X j * X k) (by ring)
      (standardOpen_inf_inf_le i j k),
    map_ratio (SetLike.mul_mem_graded hi hj) (x := X i * X j * X k) (by ring)
      (standardOpen_inf_inf_le i j k), ← map_mul]
  refine appLE_awayToSection_congr _ ?_
  rw [val_mul, val_awayMap_awayRatio, val_awayMap_awayRatio, val_awayMap_awayRatio,
    Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp; ring⟩

variable (n S) in
/-- **The transition units of the twisting sheaf `𝒪(d)`**: `u_{ij} = (xᵢ / xⱼ)^d` on
`Uᵢ ∩ Uⱼ`. The twisting sheaf `𝒪(d)` is glued from free rank-one modules on the `Uᵢ` with
bases `eᵢ^{(d)}` along `eᵢ^{(d)} = u_{ij} eⱼ^{(d)}`. -/
def transitionUnit (d : ℤ) (i j : n) : Γ(ℙ(n; S), standardOpen n S i ⊓ standardOpen n S j)ˣ :=
  ratioUnit n S i j ^ d

/-- **The cocycle rule for the transition units of the twists**: on the triple overlap
`Uᵢ ∩ Uⱼ ∩ U_k` of standard opens of `ℙ(n; S)`, `u_{ij} u_{jk} = u_{ik}` for the units
`u_{ij} = (xᵢ / xⱼ)^d`. Indeed `(xᵢ / xⱼ) (xⱼ / x_k) = xᵢ / x_k`, and the power map is
multiplicative on units. -/
theorem transitionUnit_mul_transitionUnit (d : ℤ) (i j k : n) :
    Units.map (ℙ(n; S).presheaf.map (homOfLE (inf_le_left :
        standardOpen n S i ⊓ standardOpen n S j ⊓ standardOpen n S k ≤ _)).op).hom.toMonoidHom
        (transitionUnit n S d i j) *
      Units.map (ℙ(n; S).presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right)
        inf_le_right : standardOpen n S i ⊓ standardOpen n S j ⊓ standardOpen n S k ≤
          standardOpen n S j ⊓ standardOpen n S k)).op).hom.toMonoidHom
        (transitionUnit n S d j k) =
      Units.map (ℙ(n; S).presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left)
        inf_le_right : standardOpen n S i ⊓ standardOpen n S j ⊓ standardOpen n S k ≤
          standardOpen n S i ⊓ standardOpen n S k)).op).hom.toMonoidHom
        (transitionUnit n S d i k) := by
  simp only [transitionUnit, map_zpow, ← mul_zpow]
  congr 1
  exact Units.ext (map_ratio_mul_map_ratio i j k)

end AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.ProjectiveLine

open ProjectiveSpace

variable (S : Scheme.{u})

/-- **A twisted structure sheaf `𝒪(d)` on `ℙ¹_S`**, relative to the standard affine cover
`U₀ = D₊(x₀)`, `U₁ = D₊(x₁)`: an `𝒪_{ℙ¹_S}`-module `𝓛` together with sections `g₀` over `U₀`
and `g₁` over `U₁` which trivialize it over `U₀` and over `U₁` (every section over an open
`V ⊆ Uᵢ` is uniquely `a • gᵢ`), and satisfy the glueing relation `g₀ = t^{-d} g₁` over
`U₀ ∩ U₁`, where `t = x₁ / x₀`; that is, `g₀ = (x₀ / x₁)^d g₁ = u₀₁ g₁` for the transition unit
`u₀₁` of `transitionUnit`. -/
structure TwistData (d : ℤ) (𝓛 : (ProjectiveLine S).Modules) where
  /-- The generator over `U₀ = D₊(x₀)`. -/
  g₀ : Γ(𝓛, standardOpen _ S ⟨0⟩)
  /-- The generator over `U₁ = D₊(x₁)`. -/
  g₁ : Γ(𝓛, standardOpen _ S ⟨1⟩)
  /-- `g₀` trivializes `𝓛` over `U₀`. -/
  bijective_smul_g₀ (V : (ProjectiveLine S).Opens) (hV : V ≤ standardOpen _ S ⟨0⟩) :
    Function.Bijective fun a : Γ(ProjectiveLine S, V) ↦ a • 𝓛.presheaf.map (homOfLE hV).op g₀
  /-- `g₁` trivializes `𝓛` over `U₁`. -/
  bijective_smul_g₁ (V : (ProjectiveLine S).Opens) (hV : V ≤ standardOpen _ S ⟨1⟩) :
    Function.Bijective fun a : Γ(ProjectiveLine S, V) ↦ a • 𝓛.presheaf.map (homOfLE hV).op g₁
  /-- The glueing relation `g₀ = t^{-d} g₁` over `U₀ ∩ U₁`, with `t = x₁ / x₀`. -/
  map_g₀ : 𝓛.presheaf.map (homOfLE inf_le_left).op g₀ =
    (transitionUnit (ULift.{u} (Fin 2)) S d ⟨0⟩ ⟨1⟩).1 •
      𝓛.presheaf.map (homOfLE inf_le_right).op g₁

end AlgebraicGeometry.ProjectiveLine
