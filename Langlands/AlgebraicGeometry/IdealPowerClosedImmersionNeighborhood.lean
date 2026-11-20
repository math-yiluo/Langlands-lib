import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Filtration

/-! # Open neighborhoods detected by all powers of an ideal sheaf -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AlgebraicGeometry

private theorem exists_away_map_eq_bot_of_le_powers {B : Type u}
    [CommRing B] [IsNoetherianRing B] (p : PrimeSpectrum B) (I J : Ideal B)
    (hI : I ≤ p.asIdeal) (hJ : ∀ n : ℕ, J ≤ I ^ n) :
    ∃ d ∉ p.asIdeal, J ≤ RingHom.ker (algebraMap B (Localization.Away d)) := by
  have hp (n : ℕ) : (J : Submodule B B) ≤ I ^ n • (⊤ : Submodule B B) := by
    simpa only [smul_eq_mul, ← Ideal.one_eq_top, mul_one] using hJ n
  obtain ⟨k, hk⟩ := I.exists_pow_inf_eq_pow_smul (J : Submodule B B)
  have hle : (J : Submodule B B) ≤ I • (J : Submodule B B) := by
    have he := hk (k + 1) k.le_succ
    rw [inf_eq_right.mpr (hp (k + 1)), inf_eq_right.mpr (hp k),
      show k + 1 - k = 1 by omega, pow_one] at he
    exact he.le
  obtain ⟨r, hr, hfix⟩ := Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul
    I (J : Submodule B B) J.fg_of_isNoetherianRing hle
  let d := 1 - r
  refine ⟨d, ?_, fun x hx => ?_⟩
  · intro hd
    have hz := p.asIdeal.add_mem hd (hI hr)
    rw [show d + r = 1 by simp [d]] at hz
    exact p.isPrime.ne_top (p.asIdeal.eq_top_of_isUnit_mem hz isUnit_one)
  · change algebraMap B (Localization.Away d) x = 0
    apply (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away d) d).mul_right_injective
    change algebraMap B (Localization.Away d) d * algebraMap B (Localization.Away d) x =
      algebraMap B (Localization.Away d) d * 0
    have hdx : d * x = 0 := by
      have hrx : r * x = x := hfix x hx
      change (1 - r) * x = 0
      rw [sub_mul, one_mul, hrx, sub_self]
    rw [← map_mul, hdx, map_zero, mul_zero]

/-- If the defining ideal of a closed subscheme lies in every positive
power of an ideal sheaf, it contains an open neighbourhood of the support
of that ideal sheaf on a locally noetherian scheme. -/
def IdealPowerClosedImmersionNeighborhoodStatement : Prop :=
  ∀ {X Z : Scheme.{u}} [IsLocallyNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i]
    (I : X.IdealSheafData), (∀ n : ℕ, i.ker ≤ I ^ (n + 1)) →
      ∀ x ∈ I.support, ∃ W : X.Opens, x ∈ W ∧ ∃ z : W.toScheme ⟶ Z, z ≫ i = W.ι

set_option maxHeartbeats 1000000 in
/-- Localize the ideal-sheaf inclusion on an affine chart at a function that
annihilates the defining ideal and is nonzero at the given point. -/
theorem exists_open_factor_of_idealPowers : IdealPowerClosedImmersionNeighborhoodStatement.{u} := by
  intro X Z _ i _ I h x hx
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  let P : X.affineOpens := ⟨U, hU⟩
  let B := Γ(X, U)
  have : IsNoetherianRing B := IsLocallyNoetherian.component_noetherian P
  let p : PrimeSpectrum B := hU.primeIdealOf ⟨x, hxU⟩
  have hpx : hU.fromSpec p = x := hU.fromSpec_primeIdealOf _
  have hp : I.ideal P ≤ p.asIdeal := by
    have hz : x ∈ X.zeroLocus (U := U) (I.ideal P) :=
      (Scheme.IdealSheafData.mem_support_iff_of_mem (U := P) hxU).mp hx
    have hpre : p ∈ hU.fromSpec ⁻¹' X.zeroLocus (U := U) (I.ideal P : Set B) := by
      change hU.fromSpec p ∈ X.zeroLocus (I.ideal P : Set B)
      rw [hpx]
      exact hz
    rw [hU.fromSpec_preimage_zeroLocus] at hpre
    exact (PrimeSpectrum.mem_zeroLocus _ _).mp hpre
  have hpow (n : ℕ) : i.ker.ideal P ≤ (I.ideal P) ^ n := by
    cases n with
    | zero => simp
    | succ n => exact h n P
  obtain ⟨d, hd, hk⟩ := exists_away_map_eq_bot_of_le_powers p (I.ideal P) (i.ker.ideal P) hp hpow
  let W := X.affineBasicOpen (U := P) d
  let r : B →+* Γ(X, W.1) := (X.presheaf.map (homOfLE (X.basicOpen_le d)).op).hom
  let : Algebra B Γ(X, W.1) := r.toAlgebra
  have : IsLocalization.Away d Γ(X, W.1) := hU.isLocalization_basicOpen d
  let φ : Localization.Away d →+* Γ(X, W.1) :=
    IsLocalization.Away.lift d (show IsUnit (r d) from IsLocalization.Away.algebraMap_isUnit d)
  have hW : i.ker.ideal W = ⊥ := by
    rw [← i.ker.map_ideal_basicOpen P d, ← le_bot_iff, Ideal.map_le_iff_le_comap]
    intro a ha
    change r a = 0
    have ha' : φ (algebraMap B (Localization.Away d) a) = r a :=
      IsLocalization.Away.lift_eq d (show IsUnit (r d) from
        IsLocalization.Away.algebraMap_isUnit (S := Γ(X, W.1)) d) a
    exact ha'.symm.trans ((congrArg φ (hk ha)).trans (map_zero φ))
  have hcomp : i.ker.comap W.1.ι = ⊥ := by
    have : IsAffine W.1.toScheme := W.2
    apply Scheme.IdealSheafData.ext_of_isAffine
    rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
    have haff : IsAffineOpen (W.1.ι ''ᵁ (⊤ : W.1.toScheme.Opens)) := by
      rw [W.1.ι_image_top]
      exact W.2
    have he : (⟨W.1.ι ''ᵁ (⊤ : W.1.toScheme.Opens), haff⟩ : X.affineOpens) = W :=
      Subtype.ext W.1.ι_image_top
    have hz (V : X.affineOpens) (hEq : V = W) : i.ker.ideal V = ⊥ := by
      subst V
      exact hW
    rw [hz _ he]
    change RingHom.ker (W.1.ι.appIso (⊤ : W.1.toScheme.Opens)).inv.hom = ⊥
    exact RingHom.ker_coe_equiv (W.1.ι.appIso (⊤ : W.1.toScheme.Opens)).symm.commRingCatIsoToRingEquiv
  have hle : i.ker ≤ W.1.ι.ker :=
    (Scheme.IdealSheafData.le_map_iff_comap_le.mpr hcomp.le).trans_eq
      (Scheme.IdealSheafData.map_bot W.1.ι)
  have hxW : x ∈ W.1 := by
    have hpre : p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen d := by
      rw [hU.fromSpec_preimage_basicOpen]
      exact hd
    change hU.fromSpec p ∈ X.basicOpen d at hpre
    rw [hpx] at hpre
    exact hpre
  exact ⟨W.1, hxW, IsClosedImmersion.lift i W.1.ι hle, IsClosedImmersion.lift_fac _ _ _⟩

end Langlands.AlgebraicGeometry
