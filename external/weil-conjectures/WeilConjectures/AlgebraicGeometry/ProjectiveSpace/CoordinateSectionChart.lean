/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateSection
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TwistTensor
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.TensorObj

/-!
# The coordinate sections and `𝒪 ≅ 𝒪(0)` on the standard charts

On the standard open `Uⱼ = D₊(xⱼ)` of `ℙ(n; S)`, with local generators `e_j^{(m)}` of `𝒪(m)`
(`ProjectiveSpace.twistGenerator`), the coordinate section `xᵢ` of `𝒪(1)` restricts to
`(xᵢ / xⱼ) • e_j^{(1)}`, and the isomorphism `𝒪 ≅ 𝒪(0)` sends `1` to `e_j^{(0)}`.

## Main results

- `AlgebraicGeometry.ProjectiveSpace.coordinateSection_app_standardOpen`:
  `xᵢ|_{Uⱼ} = (xᵢ / xⱼ) • e_j^{(1)}`.
- `AlgebraicGeometry.ProjectiveSpace.unitIsoTwistZero_hom_app_standardOpen`:
  `𝒪 ≅ 𝒪(0)` sends `1` to `e_j^{(0)}` on `Uⱼ`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory HomogeneousLocalization

noncomputable section

namespace AlgebraicGeometry

namespace Proj

open ProjectiveSpectrum.Twist

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] {𝒜 : ℕ → σ}
  [GradedRing 𝒜] {f g : A}

/-- On `D₊(g)`, the global section `f` of `𝒪(1)` is `(f / g) • g¹` for `f`, `g` of degree `1`,
where `g¹ = twistPowSection 1 hg` is the local generator. -/
lemma map_unitToTwist_eq_smul_twistPowSection_one (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)
    (hf' : f ∈ 𝒜 (1 • 1)) :
    (twist 𝒜 (0 + ((1 : ℕ) : ℤ))).presheaf.map (homOfLE le_top : Proj.basicOpen 𝒜 g ⟶ ⊤).op
        (Scheme.Modules.Hom.app (unitToTwist hf) ⊤ (1 : Γ(Proj 𝒜, ⊤))) =
      Proj.awayToSection 𝒜 g (Away.mk 𝒜 hg 1 f hf') • twistPowSection 1 hg := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  have h1 := val_unitToTwist_app_top hf ⟨x.1, trivial⟩
  have h3 := ProjectiveSpectrum.Proj.awayToSection_apply 𝒜 g (Away.mk 𝒜 hg 1 f hf') x
  rw [coe_twist_smul_apply, twist_presheaf_map_apply, val_twistPowSection_apply]
  refine (h1 : _).trans (Eq.trans ?_ (congrArg (· * _) h3.symm))
  simp only [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk',
    RingHom.id_apply]
  rw [← IsLocalization.mk'_mul, IsLocalization.mk'_eq_iff_eq]
  simp [mul_comm]

/-- On `D₊(g)`, the morphism `𝒪 ⟶ 𝒪(0)` sends `1` to the local generator `g⁰` of `𝒪(0)`. -/
lemma map_unitToTwistZero_one_eq_twistPowSection_zero (hg : g ∈ 𝒜 1) :
    (twist 𝒜 0).presheaf.map (homOfLE le_top : Proj.basicOpen 𝒜 g ⟶ ⊤).op
        (Scheme.Modules.Hom.app (unitToTwistZero (𝒜 := 𝒜)) ⊤ (1 : Γ(Proj 𝒜, ⊤))) =
      twistPowSection 0 hg := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  rw [twist_presheaf_map_apply, val_twistPowSection_zero]
  change ((degreePart.zeroEquiv (1 : HomogeneousLocalization.AtPrime 𝒜
    x.1.asHomogeneousIdeal.toIdeal) : degreePart 𝒜 x.1.asHomogeneousIdeal.toIdeal.primeCompl 0) :
    Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) = 1
  rw [degreePart.coe_zeroEquiv_apply, HomogeneousLocalization.val_one]

end Proj

namespace ProjectiveSpace

open Scheme.Modules MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : Type u) (S : Scheme.{u})

/-- The value of the coordinate section `xᵢ` of `𝒪(1)` on `1` is the global section
`twistOneSection n S i`. -/
lemma coordinateSection_app_top_one (i : n) :
    (coordinateSection n S i).app ⊤ (1 : Γ(ℙ(n; S), ⊤)) = twistOneSection n S i :=
  (pullbackSection_app_one (toProjInt n S)
    (Proj.unitToTwist (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) i))).symm

/-- **The coordinate section `xᵢ` on the chart `Uⱼ`**: on the standard open `Uⱼ = D₊(xⱼ)` the
coordinate section `xᵢ` of `𝒪(1)` (applied to `1`) is `(xᵢ / xⱼ) • e_j^{(1)}`, where
`xᵢ / xⱼ = coordRatio n S j i` and `e_j^{(1)} = twistGenerator n S 1 j` is the local generator. -/
theorem coordinateSection_app_standardOpen (i j : n) :
    (coordinateSection n S i).app (standardOpen n S j) (1 : Γ(ℙ(n; S), standardOpen n S j)) =
      coordRatio n S j i • twistGenerator n S 1 j := by
  have hnat := Hom.app_presheaf_map (coordinateSection n S i)
    (homOfLE (le_top : standardOpen n S j ≤ ⊤)) (1 : Γ(ℙ(n; S), ⊤))
  have h1 : (ℙ(n; S)).presheaf.map (homOfLE (le_top : standardOpen n S j ≤ ⊤)).op
      (1 : Γ(ℙ(n; S), ⊤)) = 1 :=
    map_one ((ℙ(n; S)).presheaf.map (homOfLE (le_top : standardOpen n S j ≤ ⊤)).op).hom
  erw [h1] at hnat
  rw [hnat, coordinateSection_app_top_one, twistOneSection]
  have H := Proj.map_unitToTwist_eq_smul_twistPowSection_one
    (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) i)
    (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) j)
    (by simpa using X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) i)
  have H₁ := congrArg (pullbackSection (toProjInt n S)) H
  rw [pullbackSection_map, pullbackSection_smul] at H₁
  exact H₁

/-- **`𝒪 ≅ 𝒪(0)` on the charts**: on the standard open `Uⱼ`, the isomorphism
`unitIsoTwistZero: 𝒪 ≅ 𝒪(0)` sends `1` to the local generator `e_j^{(0)}` of `𝒪(0)`. -/
theorem unitIsoTwistZero_hom_app_standardOpen (j : n) :
    Hom.app (unitIsoTwistZero n S).hom (standardOpen n S j)
      (1 : Γ(ℙ(n; S), standardOpen n S j)) =
      twistGenerator n S 0 j := by
  have hnat := Hom.app_presheaf_map (unitIsoTwistZero n S).hom
    (homOfLE (le_top : standardOpen n S j ≤ ⊤)) (1 : Γ(ℙ(n; S), ⊤))
  have h1 : (ℙ(n; S)).presheaf.map (homOfLE (le_top : standardOpen n S j ≤ ⊤)).op
      (1 : Γ(ℙ(n; S), ⊤)) = 1 :=
    map_one ((ℙ(n; S)).presheaf.map (homOfLE (le_top : standardOpen n S j ≤ ⊤)).op).hom
  erw [h1] at hnat
  have htop : Hom.app (unitIsoTwistZero n S).hom ⊤ (1 : Γ(ℙ(n; S), ⊤)) =
      pullbackSection (toProjInt n S)
        (Hom.app (Proj.unitToTwistZero (𝒜 := homogeneousSubmodule n (ULift.{u} ℤ))) ⊤
          (1 : Γ(Proj (homogeneousSubmodule n (ULift.{u} ℤ)), ⊤))) :=
    (pullbackSection_app_one (toProjInt n S) Proj.unitToTwistZero).symm
  rw [hnat, htop]
  have H := Proj.map_unitToTwistZero_one_eq_twistPowSection_zero
    (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) j)
  have H₁ := congrArg (pullbackSection (toProjInt n S)) H
  rw [pullbackSection_map] at H₁
  exact H₁

end ProjectiveSpace

end AlgebraicGeometry
