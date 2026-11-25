/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.CoefficientHigherDirectImageZero
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.GeometricPointModuleConstant
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.TorsionConstantPrimeDevissage
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Coefficients

/-!
# Prime cyclic detection of a geometric-point coefficient

Source: Stacks Project, Tag 0F08, coefficient reduction in the proof, with
underlying-abelian comparison from Tag 03FD and qcqs colimits from Tag 0739.
(blueprint: lem-sbc-prime-cyclic-detection)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

private theorem prime_cyclic_vanishing_in_integer_coefficients
    {X Y : Scheme.{u}} (h : Y ⟶ X) [QuasiCompact h] [QuasiSeparated h]
    (q : ℤ) (r : ℕ)
    (hz : IsZero (higherDirectImage (ULift.{u + 1} (ZMod r)) h q
      (constantModSheaf (ULift.{u + 1} (ZMod r)) Y r))) :
    IsZero (higherDirectImage (ULift.{u + 1} ℤ) h q
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).obj
        (ModuleCat.of.{u + 1} (ULift.{u + 1} ℤ) (ULift.{u + 1} (ZMod r))))) := by
  let P := ULift.{u + 1} (ZMod r)
  let φ : ULift.{u + 1} ℤ →+* P :=
    (Int.castRingHom P).comp ULift.ringEquiv.toRingHom
  have : (ModuleCat.restrictScalars.{u + 1} φ).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1} φ).isLeftAdjoint
  have hr : (r : P) = 0 := by
    apply ULift.ext
    exact ZMod.natCast_self r
  have hi : (Ideal.span {(r : P)} : Ideal P) = ⊥ := by simp [hr]
  let l : ModuleCat.of.{u + 1} P (P ⧸ (Ideal.span {(r : P)} : Ideal P)) ≅
      ModuleCat.of.{u + 1} P P :=
    (Submodule.quotEquivOfEqBot _ hi).toModuleIso
  let c := constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P)
  let HP := DerivedCategory.Plus.singleFunctor _ 0 ⋙
    (lowerStar (ModuleCat.{u + 1} P) h).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor _ q
  have hp : IsZero (higherDirectImage P h q (c.obj (ModuleCat.of.{u + 1} P P))) :=
    (HP.mapIso (c.mapIso l)).isZero_iff.mp hz
  have hz' := (isZero_higherDirectImage_restrictScalars_iff φ h q
    (c.obj (ModuleCat.of.{u + 1} P P))).mpr hp
  let k : (ModuleCat.restrictScalars.{u + 1} φ).obj (ModuleCat.of.{u + 1} P P) ≅
      ModuleCat.of.{u + 1} (ULift.{u + 1} ℤ) P :=
    (show (ModuleCat.restrictScalars.{u + 1} φ).obj (ModuleCat.of.{u + 1} P P) ≃ₗ[
      ULift.{u + 1} ℤ] P from
      { __ := AddEquiv.refl P
        map_smul' := by
          intro z x
          change (z.down : P) • x = z.down • x
          exact Int.cast_smul_eq_zsmul P _ _ }).toModuleIso
  let ci : (Sheaf.restrictScalars Y.smallEtaleTopology φ).obj
      (c.obj (ModuleCat.of.{u + 1} P P)) ≅
      (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).obj
        (ModuleCat.of.{u + 1} (ULift.{u + 1} ℤ) P) :=
    (constantCommuteCompose Y.smallEtaleTopology
    (ModuleCat.restrictScalars.{u + 1} φ)).app (ModuleCat.of.{u + 1} P P) ≪≫
      (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).mapIso k
  let HZ := DerivedCategory.Plus.singleFunctor _ 0 ⋙
    (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor _ q
  exact (HZ.mapIso ci).isZero_iff.mp hz'

/-- Nonvanishing with a geometric-point coefficient detects a prime cyclic abelian
coefficient, with a prime that is not a unit in the original coefficient ring.

Source: Stacks Project, Tag 0F08, proof's cyclic-coefficient reduction; Tag 03FD
for forgetting coefficients; Tag 0739 for qcqs cohomology and filtered colimits.
(blueprint: lem-sbc-prime-cyclic-detection)

Proof:
1. The geometric-point module-constancy theorem supplies a module M and an isomorphism
between e-star F and the constant M-sheaf on Y. The already-proved
baseChangeTargetFunctorIso transports the nonvanishing to its higher direct image.
2. Restrict M along ULift Z -> Lambda. The constant sheaf comparison and
isZero_higherDirectImage_restrictScalars_iff preserve nonvanishing. The equation n = 0
in Lambda kills every element of this integer module.
3. Suppose there is no prime as in the conclusion. Apply
isZero_higherDirectImage_constant_of_prime_vanishing. For a prime dividing n with
noninjective multiplication on M, scalar cancellation shows that prime is not a unit
in Lambda. The assumed absence of a witness forces its prime-field image to vanish.
4. In P = ULift(ZMod r), r = 0, so its ideal is bottom. The quotient module is P,
by Submodule.quotEquivOfEqBot. Restricting its scalar action to the integers gives
the ordinary integer-module P, by Int.cast_smul_eq_zsmul. The higher-direct-image
coefficient comparison and constantCommuteCompose turn its vanishing into the
prime-cyclic vanishing required in step 3. The resulting vanishing for M contradicts
step 2. This also covers negative q, where images of degree-zero sheaves vanish. -/
theorem exists_prime_cyclic_higherDirectImage
    (Λ : Type (u + 1)) [CommRing Λ] {K : Type u} [Field K] [IsAlgClosed K]
    {X Y : Scheme.{u}} (e : Y ⟶ Spec (.of K)) (h : Y ⟶ X)
    [QuasiCompact h] [QuasiSeparated h] (n : ℕ) (hn : n ≠ 0)
    (hΛ : (n : Λ) = 0) (q : ℤ)
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : ¬ IsZero ((baseChangeTargetFunctor Λ e h q).obj F)) :
    ∃ r : ℕ, r.Prime ∧ r ∣ n ∧ ¬ IsUnit (r : Λ) ∧
      ¬ IsZero (higherDirectImage (ULift.{u + 1} (ZMod r)) h q
        (constantModSheaf (ULift.{u + 1} (ZMod r)) Y r)) := by
  classical
  obtain ⟨M, ⟨i⟩⟩ := exists_constant_module_upperStar_geometricPoint Λ e F
  let HΛ := DerivedCategory.Plus.singleFunctor _ 0 ⋙
    (lowerStar (ModuleCat.{u + 1} Λ) h).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor _ q
  let cΛ := constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  have hconst : ¬ IsZero (higherDirectImage Λ h q (cΛ.obj M)) := by
    intro hz
    apply hF
    exact IsZero.of_iso hz ((baseChangeTargetFunctorIso Λ e h q).app F ≪≫ HΛ.mapIso i)
  let φ : ULift.{u + 1} ℤ →+* Λ :=
    (Int.castRingHom Λ).comp ULift.ringEquiv.toRingHom
  have : (ModuleCat.restrictScalars.{u + 1} φ).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1} φ).isLeftAdjoint
  let MZ := (ModuleCat.restrictScalars.{u + 1} φ).obj M
  let HZ := DerivedCategory.Plus.singleFunctor _ 0 ⋙
    (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor _ q
  let cZ := constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
  have hZ : ¬ IsZero (higherDirectImage (ULift.{u + 1} ℤ) h q (cZ.obj MZ)) := by
    intro hz
    apply hconst
    apply (isZero_higherDirectImage_restrictScalars_iff φ h q (cΛ.obj M)).mp
    let ci : (Sheaf.restrictScalars Y.smallEtaleTopology φ).obj (cΛ.obj M) ≅ cZ.obj MZ :=
      (constantCommuteCompose Y.smallEtaleTopology
        (ModuleCat.restrictScalars.{u + 1} φ)).app M
    exact IsZero.of_iso hz (HZ.mapIso ci)
  have hM : ∀ x : MZ, n • x = 0 := by
    intro x
    change n • (show M from x) = 0
    rw [← Nat.cast_smul_eq_nsmul Λ, hΛ, zero_smul]
  by_contra hnone
  apply hZ
  apply isZero_higherDirectImage_constant_of_prime_vanishing h q MZ n hn hM
  intro r hr hrn hnotinj
  have hunit : ¬ IsUnit (r : Λ) := by
    intro hu
    apply hnotinj
    intro x y hxy
    change r • (show M from x) = r • (show M from y) at hxy
    rw [← Nat.cast_smul_eq_nsmul Λ, ← Nat.cast_smul_eq_nsmul Λ] at hxy
    exact hu.smul_left_cancel.mp hxy
  have hz : IsZero (higherDirectImage (ULift.{u + 1} (ZMod r)) h q
      (constantModSheaf (ULift.{u + 1} (ZMod r)) Y r)) := by
    by_contra hnonzero
    exact hnone ⟨r, hr, hrn, hunit, hnonzero⟩
  exact prime_cyclic_vanishing_in_integer_coefficients h q r hz

end AlgebraicGeometry.Etale
