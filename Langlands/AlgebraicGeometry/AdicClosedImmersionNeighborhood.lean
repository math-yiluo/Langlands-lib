import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Filtration

/-! # Open neighborhoods detected by adic thickenings of a closed subscheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing Opposite

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

/-- A closed subscheme containing the preimage of every maximal-ideal power
thickening contains an open neighbourhood of each point of the closed fibre. -/
def AdicClosedImmersionNeighborhoodStatement : Prop :=
  ∀ {R : CommRingCat.{u}} [IsLocalRing R] [IsNoetherianRing R] {X Z : Scheme.{u}}
    (a : X ⟶ Spec R) [LocallyOfFiniteType a] (c : Z ⟶ X) [IsClosedImmersion c]
    (x : X), a x = closedPoint R →
    (∀ n : ℕ, ∃ v : pullback a (Spec.algebraMap R (R ⧸ maximalIdeal R ^ n)) ⟶ Z,
      v ≫ c = pullback.fst a (Spec.algebraMap R (R ⧸ maximalIdeal R ^ n))) →
      ∃ W : X.Opens, x ∈ W ∧ ∃ z : W.toScheme ⟶ Z, z ≫ c = W.ι

set_option maxHeartbeats 1200000 in
/-- Artin–Rees and the determinant trick give the open factorization. -/
theorem exists_open_factor_of_adicThickenings : AdicClosedImmersionNeighborhoodStatement.{u} := by
  intro R _ _ X Z a _ c _ x hx h
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  let B := Γ(X, U)
  let u₀ : Spec B ⟶ X := hU.fromSpec
  have : IsOpenImmersion u₀ := inferInstanceAs (IsOpenImmersion hU.fromSpec)
  obtain ⟨p, hp⟩ : x ∈ Set.range u₀ :=
    (Set.ext_iff.mp (IsAffineOpen.range_fromSpec hU) x).mpr hxU
  let ρ := Spec.preimage (u₀ ≫ a)
  have hρ : Spec.map ρ = u₀ ≫ a := Spec.map_preimage _
  have hp' : PrimeSpectrum.comap ρ.hom p = closedPoint R := by
    change (Spec.map ρ) p = closedPoint R
    rw [hρ, Scheme.Hom.comp_apply, hp, hx]
  have hI : (maximalIdeal R).map ρ.hom ≤ p.asIdeal := by
    apply Ideal.map_le_iff_le_comap.mpr
    exact (congrArg PrimeSpectrum.asIdeal hp').symm.le
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian a
  have : IsNoetherianRing B := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let Z₀ := pullback c u₀
  let z₀ : Z₀ ⟶ Spec B := pullback.snd c u₀
  have : IsClosedImmersion z₀ := MorphismProperty.pullback_snd c u₀ inferInstance
  have : IsAffine Z₀ := isAffine_of_isAffineHom z₀
  let q : B ⟶ Γ(Z₀, ⊤) := (Scheme.ΓSpecIso B).inv ≫ z₀.appTop
  have hq : Z₀.isoSpec.hom ≫ Spec.map q = z₀ := by
    rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality z₀]
    simp only [Category.assoc, Scheme.isoSpec, asIso_hom, toSpecΓ_SpecMap_ΓSpecIso_inv,
      Category.comp_id]
  have hsurj : Function.Surjective q.hom := (z₀.app_surjective ⊤ (isAffineOpen_top _)).comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso B).inv).2
  have hk (n : ℕ) : RingHom.ker q.hom ≤ ((maximalIdeal R).map ρ.hom) ^ n := by
    let J := maximalIdeal R ^ n
    let J' := J.map ρ.hom
    let d := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J'))
    let b := Spec.algebraMap R (R ⧸ J)
    let b' := Spec.map (CommRingCat.ofHom (Ideal.quotientMap J' ρ.hom Ideal.le_comap_map))
    have hw : (d ≫ u₀) ≫ a = b' ≫ b := by
      rw [Category.assoc, ← hρ]
      change d ≫ Spec.map ρ = b' ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
      dsimp only [d, b']
      rw [← Spec.map_comp, ← Spec.map_comp]
      exact congrArg (fun f : R ⟶ CommRingCat.of (B ⧸ J') => Spec.map f)
        (by ext1; exact (Ideal.quotientMap_comp_mk Ideal.le_comap_map).symm)
    obtain ⟨v, hv⟩ := h n
    let l := pullback.lift (d ≫ u₀) b' hw
    have hl : (l ≫ v) ≫ c = d ≫ u₀ := by
      rw [Category.assoc, hv]
      exact pullback.lift_fst _ _ _
    let z := pullback.lift (l ≫ v) d hl
    let r := Spec.preimage (z ≫ Z₀.isoSpec.hom)
    have hr : q ≫ r = CommRingCat.ofHom (Ideal.Quotient.mk J') := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, Category.assoc, hq]
      exact pullback.lift_snd _ _ _
    have hlJ : RingHom.ker q.hom ≤ J' := by
      rw [← Ideal.mk_ker (I := J')]
      intro y hy
      change q.hom y = 0 at hy
      change (Ideal.Quotient.mk J') y = 0
      rw [← show (q ≫ r).hom y = (Ideal.Quotient.mk J') y from
        congrArg (fun k : B ⟶ CommRingCat.of (B ⧸ J') => k.hom y) hr]
      change r.hom (q.hom y) = 0
      rw [hy, map_zero]
    rw [← Ideal.map_pow]
    exact hlJ
  obtain ⟨d, hd, hker⟩ := exists_away_map_eq_bot_of_le_powers p _ _ hI hk
  let l := Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away d)))
  let r := CommRingCat.ofHom (q.hom.liftOfSurjective hsurj ⟨_, hker⟩)
  let v := Spec.map r ≫ Z₀.isoSpec.inv ≫ pullback.fst c u₀
  have hqr : q ≫ r = CommRingCat.ofHom (algebraMap B (Localization.Away d)) := by
    ext1
    exact RingHom.liftOfSurjective_comp q.hom hsurj _
  have hv : v ≫ c = l ≫ u₀ := by
    have he : Spec.map q = Z₀.isoSpec.inv ≫ z₀ := by
      rw [Iso.eq_inv_comp]
      exact hq
    simp only [v, Category.assoc, pullback.condition (f := c) (g := u₀)]
    change Spec.map r ≫ Z₀.isoSpec.inv ≫ z₀ ≫ u₀ = _
    rw [← Category.assoc Z₀.isoSpec.inv z₀ u₀, ← he, ← Spec.map_comp_assoc, hqr]
  have : IsOpenImmersion l := inferInstanceAs (IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away d)))))
  let w := l ≫ u₀
  have hW : x ∈ w.opensRange := by
    apply Scheme.Hom.mem_opensRange.mpr
    have hlp : p ∈ l.opensRange := by
      rw [Scheme.Hom.opensRange_localizationAway]
      exact hd
    obtain ⟨p', hp'⟩ := Scheme.Hom.mem_opensRange.mp hlp
    refine ⟨p', ?_⟩
    change u₀ (l p') = x
    exact (congrArg (fun t : Spec B => u₀ t) hp').trans hp
  refine ⟨w.opensRange, hW, w.isoOpensRange.inv ≫ v, ?_⟩
  rw [Category.assoc, hv]
  exact w.isoOpensRange_inv_comp

end Langlands.AlgebraicGeometry
