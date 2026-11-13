import Langlands.GroupScheme.SimplyConnected.LocalOuterTypeAHermitianModelStatement
import Langlands.GroupScheme.Examples.HermitianRootCocharacterNontrivial
import Langlands.GroupScheme.Rational.NontrivialCocharacterRank

/-!
# Local anisotropic simply connected type A is inner, given the Hermitian model

This module proves `LocalAnisotropicTypeAInnerStatement` from
`LocalOuterTypeAHermitianModelStatement`: an outer form would be isomorphic to a
Hermitian model, whose actual diagonal cocharacter is nontrivial, contradicting
anisotropy.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A nonarchimedean local field is infinite: a nonzero element of valuation
less than one cannot have finite multiplicative order. -/
theorem IsNonarchimedeanLocalField.infinite (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] : Infinite K := by
  by_contra hfin
  have : Finite K := not_infinite_iff_finite.mp hfin
  obtain ⟨γ, hγ0, hγ1⟩ := ValuativeRel.IsNontrivial.exists_lt_one (R := K)
  obtain ⟨r, rfl⟩ := ValuativeRel.valuation_surjective γ
  have hr : r ≠ 0 := by
    rintro rfl
    simp at hγ0
  let u : Kˣ := Units.mk0 r hr
  have hu : u ^ Nat.card Kˣ = 1 := pow_card_eq_one'
  have hpow : r ^ Nat.card Kˣ = 1 := by
    have h := congrArg Units.val hu
    rwa [Units.val_pow_eq_pow_val, Units.val_one, Units.val_mk0] at h
  have hcard : Nat.card Kˣ ≠ 0 := Nat.card_pos.ne'
  have hlt : ValuativeRel.valuation K r ^ Nat.card Kˣ < 1 :=
    pow_lt_one₀ hγ0.le hγ1 hcard
  rw [← map_pow, hpow, map_one] at hlt
  exact lt_irrefl _ hlt

/-- The local outer-A Hermitian model statement implies that every affine
anisotropic simply connected absolutely almost-simple group of type `A_n` over a
nonarchimedean local field has trivial actual star action. -/
theorem localAnisotropicTypeAInner_of_hermitianModel
    (h : LocalOuterTypeAHermitianModelStatement.{u}) :
    LocalAnisotropicTypeAInnerStatement.{u} := by
  intro K _ _ _ _ G _ _ d n hsc has hanis htype
  have : Infinite K := IsNonarchimedeanLocalField.infinite K
  by_contra hstar
  push Not at hstar
  obtain ⟨L, _, _, _, _, H, w, hw, ⟨e⟩⟩ := h K G d n hsc has htype hstar
  apply HermitianRoot.SchemeModel.cocharacter_ne_zero K L H w hw
  have hz := hanis.cocharacter_eq_zero (HermitianRoot.SchemeModel.cocharacter K L H w hw ≫ e.inv)
  rw [← Category.comp_id (HermitianRoot.SchemeModel.cocharacter K L H w hw),
    ← e.inv_hom_id, ← Category.assoc, hz, Limits.zero_comp]

end Langlands.GroupScheme
