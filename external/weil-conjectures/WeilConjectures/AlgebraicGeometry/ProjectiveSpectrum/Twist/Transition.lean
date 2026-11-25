/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.TensorObj

/-!
# Transition functions of the powers `fᵐ` of the twisting sheaves

For homogeneous elements `f` and `g` of degree `1` of a graded ring `𝒜`, the sections `fᵐ` and
`gᵐ` of `𝒪(m)` over `D₊(f)` and `D₊(g)` are related by `fᵐ = (f / g)ᵐ • gᵐ` on
`D₊(f) ∩ D₊(g)`.
-/

@[expose] public section

noncomputable section
universe u

open CategoryTheory HomogeneousLocalization

namespace AlgebraicGeometry.Proj

open ProjectiveSpectrum.Twist Scheme.Modules

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜] {f g : A}

/-- **The transition rule** `f = (f / g) • g` for the sections `f¹` and `g¹` of `𝒪(1)`, on an
open `W ⊆ D₊(f) ∩ D₊(g)`, where `f / g` is the degree-zero fraction of `A_g`. -/
lemma map_awayToSection_smul_twistPowSection_one (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)
    (hf' : f ∈ 𝒜 (1 • 1)) {W : (Proj 𝒜).Opens} (hWf : W ≤ Proj.basicOpen 𝒜 f)
    (hWg : W ≤ Proj.basicOpen 𝒜 g) :
    (Proj 𝒜).presheaf.map (homOfLE hWg).op (Proj.awayToSection 𝒜 g (Away.mk 𝒜 hg 1 f hf')) •
        (twist 𝒜 1).presheaf.map (homOfLE hWg).op (twistPowSection 1 hg) =
      (twist 𝒜 1).presheaf.map (homOfLE hWf).op (twistPowSection 1 hf) := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  have h3 := ProjectiveSpectrum.Proj.awayToSection_apply 𝒜 g (Away.mk 𝒜 hg 1 f hf')
    ⟨x.1, hWg x.2⟩
  rw [coe_twist_smul_apply, twist_presheaf_map_apply, twist_presheaf_map_apply,
    val_twistPowSection_apply, val_twistPowSection_apply]
  refine (congrArg (· * _) h3).trans ?_
  simp only [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk',
    RingHom.id_apply]
  rw [← IsLocalization.mk'_mul, IsLocalization.mk'_eq_iff_eq]
  simp [mul_comm]

/-- `g⁰ = f⁰` on an open `W ⊆ D₊(f) ∩ D₊(g)`. -/
lemma map_twistPowSection_zero (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) {W : (Proj 𝒜).Opens}
    (hWf : W ≤ Proj.basicOpen 𝒜 f) (hWg : W ≤ Proj.basicOpen 𝒜 g) :
    (twist 𝒜 0).presheaf.map (homOfLE hWg).op (twistPowSection 0 hg) =
      (twist 𝒜 0).presheaf.map (homOfLE hWf).op (twistPowSection 0 hf) := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  rw [twist_presheaf_map_apply, twist_presheaf_map_apply, val_twistPowSection_zero,
    val_twistPowSection_zero]

/-- **The transition rule for the powers** `fᵐ = uᵐ • gᵐ`: if `u` is a unit on an open
`W ⊆ D₊(f) ∩ D₊(g)` with `f = u • g` as sections of `𝒪(1)` on `W` (e.g. `u = f / g`), then
`fᵐ = uᵐ • gᵐ` as sections of `𝒪(m)` on `W`, for every `m : ℤ`. -/
lemma zpow_smul_map_twistPowSection (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) {W : (Proj 𝒜).Opens}
    (hWf : W ≤ Proj.basicOpen 𝒜 f) (hWg : W ≤ Proj.basicOpen 𝒜 g) (u : Γ(Proj 𝒜, W)ˣ)
    (hu : u.1 • (twist 𝒜 1).presheaf.map (homOfLE hWg).op (twistPowSection 1 hg) =
      (twist 𝒜 1).presheaf.map (homOfLE hWf).op (twistPowSection 1 hf)) (m : ℤ) :
    (u ^ m).1 • (twist 𝒜 m).presheaf.map (homOfLE hWg).op (twistPowSection m hg) =
      (twist 𝒜 m).presheaf.map (homOfLE hWf).op (twistPowSection m hf) := by
  have h0 := map_twistPowSection_zero hf hg hWf hWg
  have hneg : (u⁻¹).1 • (twist 𝒜 (-1)).presheaf.map (homOfLE hWg).op
      (twistPowSection (-1) hg) =
      (twist 𝒜 (-1)).presheaf.map (homOfLE hWf).op (twistPowSection (-1) hf) := by
    obtain ⟨d, hd⟩ := ((isFreeGenerator_twistPowSection (-1) hg).map hWg).exists_smul_eq
      ((twist 𝒜 (-1)).presheaf.map (homOfLE hWf).op (twistPowSection (-1) hf))
    have h := twistPowSection_map_eq_mul_smul hf hg hWf hWg hu hd
    have hud : u.1 * d = 1 := ((isFreeGenerator_twistPowSection (1 + -1) hg).map
      hWg).smul_left_injective (h.trans (h0.symm.trans (one_smul _ _).symm))
    obtain rfl : d = (u⁻¹).1 := (Units.inv_eq_of_mul_eq_one_right hud).symm
    exact hd
  induction m using Int.induction_on with
  | zero => rw [zpow_zero, Units.val_one, one_smul, h0]
  | succ m ih =>
    rw [zpow_add_one, Units.val_mul]
    exact twistPowSection_map_eq_mul_smul hf hg hWf hWg ih hu
  | pred m ih =>
    rw [sub_eq_add_neg, zpow_add, zpow_neg_one, Units.val_mul]
    exact twistPowSection_map_eq_mul_smul hf hg hWf hWg ih hneg

end AlgebraicGeometry.Proj
