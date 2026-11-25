/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.AlgebraicGeometry.QuasiCoherentIdealZeroSetAffine
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.IdealPowerProductZeroAffineCover
import Mathlib.RingTheory.Finiteness.Ideal
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed

/-! # An ideal power kills a coherent module exactly when its support lies in the zero set

Source: Stacks Project, Cohomology of Schemes, Lemma 30.10.2 (Tag 01Y9),
using Algebra, Lemma 10.62.4 (Tag 00L6)
(blueprint: lem-weil-pbc-coherent-support-power-ideal-kills).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- On a Noetherian scheme, a coherent module is annihilated by some nonnegative power of
an ideal exactly when its nonzero-stalk locus lies in the locus where the stalk ideal is
proper. The latter condition is failure of surjectivity of the stalk inclusion, as in
`quasi_coherent_ideal_zero_set_affine`. The shared `idealSheafPower` has the structure sheaf
with identity inclusion at exponent zero, so its product with `F` is canonically `F`.

Source: Stacks Project, Cohomology of Schemes, Lemma 30.10.2 (Tag 01Y9), with Algebra,
Lemma 10.62.4 (Tag 00L6) (blueprint: lem-weil-pbc-coherent-support-power-ideal-kills).

Proof:
1. Choose a finite affine cover with Noetherian section rings, using pqf-def-locnoeth
   and quasi-compactness (def-weil-pbc-noetherian-ring, def-pc-scheme,
   def-weil-affine-spectrum).
2. Coherence gives finite presentation locally and hence quasi-coherence and finite type.
   By lem-weil-pbc-quasi-coherent-finite-type-affine the sections on each affine in the
   cover form a finite module (pqf-def-coherent, def-weil-finitely-generated-module).
3. By lem-weil-pbc-ideal-times-quasi-coherent-affine-sections, the sections of each ideal
   power times F are the corresponding ideal power times its affine section module.
   At exponent zero this is F itself (def-weil-pbc-coherent-formal-module).
4. Vanishing is equivalent to vanishing of these modules on every member of the cover:
   use lem-weil-pbc-module-restriction-open-immersion-colimits and the counit and
   zero preservation of lem-weil-pbc-affine-tilde-gamma-adjunction, then the sheaf
   property (situation-conventions).
5. On each affine, support is V(Ann M), by lem-weil-pbc-finite-type-module-support-closed
   and lem-weil-pbc-finite-module-support-annihilator. The ideal zero set is V(I), by
   lem-weil-pbc-quasi-coherent-ideal-zero-set-affine. Thus the global containment is
   equivalent to these containments on the cover.
6. Algebra 00L6: I^n M = 0 iff I^n is contained in Ann M. Such containment implies
   V(Ann M) is contained in V(I). Conversely the zero-locus containment gives
   I contained in the radical of Ann M (lem-weil-pbc-zero-locus-eq-iff-radical-eq).
   Noetherianity makes I finitely generated, so lem-weil-pbc-fg-ideal-radical-power
   gives a power contained in Ann M; all higher powers also kill M.
7. A global killing power therefore implies the support containment. Conversely take
   the maximum of the finitely many affine killing exponents and apply step 4.
   For an empty cover (the empty scheme) take exponent zero. -/
theorem coherent_support_power_ideal_kills (X : Scheme.{u}) [IsNoetherian X]
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (K : X.IdealSheafData) :
    (∃ t : ℕ, IsZero (idealModuleProduct (idealSheafPower K.toModulesι t).2 F)) ↔
      {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ⊆
        {x : X | ¬ Function.Surjective
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map K.toModulesι).hom} := by
  classical
  obtain ⟨hq, ht⟩ :=
    (Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp hF
  have : F.IsQuasicoherent := hq
  have : F.IsFiniteType := ht
  obtain ⟨S, hfin, hcover⟩ :=
    isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp
      ⟨isCompact_univ (X := X), isOpen_univ⟩
  have hS : ∀ x : X, ∃ U ∈ S, x ∈ U.1 := by
    intro x
    have hx : x ∈ ⋃ U ∈ S, (U.1 : Set X) := by rw [← hcover]; trivial
    obtain ⟨U, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hU, hx⟩ := Set.mem_iUnion.mp hx
    exact ⟨U, hU, hx⟩
  have hsupp := (Modules.finite_type_module_support_closed X F).2.2.1
  have hzero := (quasi_coherent_ideal_zero_set_affine X K).2.2.1
  have hloc :
      ({x : X | ¬ Subsingleton (F.presheaf.stalk x)} ⊆
        {x : X | ¬ Function.Surjective
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map K.toModulesι).hom}) ↔
      ∀ U ∈ S, K.ideal U ≤ (Module.annihilator Γ(X, U.1) Γ(F, U.1)).radical := by
    constructor
    · intro h U _
      apply (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _).mp
      intro p hp
      have hx : U.2.fromSpec p ∈
          {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ∩ (U.1 : Set X) := by
        rw [hsupp U]
        exact ⟨p, hp, rfl⟩
      have hy : U.2.fromSpec p ∈
          {x : X | ¬ Function.Surjective
            ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map K.toModulesι).hom} ∩
              (U.1 : Set X) := ⟨h hx.1, hx.2⟩
      rw [hzero U] at hy
      obtain ⟨q, hq, heq⟩ := hy
      have he : q = p := U.2.fromSpec.isOpenEmbedding.injective heq
      exact he ▸ hq
    · intro h x hx
      obtain ⟨U, hU, hxU⟩ := hS x
      have hx' : x ∈ U.2.fromSpec '' PrimeSpectrum.zeroLocus
          (Module.annihilator Γ(X, U.1) Γ(F, U.1) : Set Γ(X, U.1)) := by
        rw [← hsupp U]
        exact ⟨hx, hxU⟩
      obtain ⟨p, hp, rfl⟩ := hx'
      have hp' := (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _).mpr (h U hU) hp
      have hy : U.2.fromSpec p ∈
          {x : X | ¬ Function.Surjective
            ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map K.toModulesι).hom} ∩
              (U.1 : Set X) := by
        rw [hzero U]
        exact ⟨p, hp', rfl⟩
      exact hy.1
  rw [hloc]
  constructor
  · rintro ⟨t, ht⟩ U hU a ha
    have hkill := (idealPowerProduct_isZero_iff_affine_cover X F K S hS t).mp ht U hU
    exact ⟨t, hkill (Ideal.pow_mem_pow ha t)⟩
  · intro h
    have hex : ∀ U : S, ∃ n : ℕ,
        K.ideal U.1 ^ n ≤ Module.annihilator Γ(X, U.1.1) Γ(F, U.1.1) := by
      intro U
      have : IsNoetherianRing Γ(X, U.1.1) :=
        IsLocallyNoetherian.component_noetherian U.1
      exact Ideal.exists_pow_le_of_le_radical_of_fg (h U.1 U.2)
        (Ideal.fg_of_isNoetherianRing _)
    choose n hn using hex
    let T := hfin.toFinset
    let t := T.sup fun U ↦ if hU : U ∈ S then n ⟨U, hU⟩ else 0
    refine ⟨t, (idealPowerProduct_isZero_iff_affine_cover X F K S hS t).mpr ?_⟩
    intro U hU
    have hnt : n ⟨U, hU⟩ ≤ t := by
      have hm : U ∈ T := hfin.mem_toFinset.mpr hU
      simpa only [dite_eq_left hU] using Finset.le_sup
        (f := fun U ↦ if hU : U ∈ S then n ⟨U, hU⟩ else 0) hm
    exact (Ideal.pow_le_pow_right hnt).trans (hn ⟨U, hU⟩)

end AlgebraicGeometry.Scheme
