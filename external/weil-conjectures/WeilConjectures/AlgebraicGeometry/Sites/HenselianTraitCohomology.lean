/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.GaloisModule
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.FieldTheory.HenselianDVRGaloisCohomology

/-!
# Étale cohomology of the generic point of a strictly henselian trait

Let `B` be a henselian discrete valuation ring with separably closed residue field, `K` its
fraction field and `ℓ` a prime invertible in the residue field. We compute the étale cohomology
of `Spec K` with coefficients in the constant sheaf `ℤ/ℓ`:
`H⁰(Spec K, ℤ/ℓ) ≃ ℤ/ℓ`, `H¹(Spec K, ℤ/ℓ) ≃ ℤ/ℓ` and `Hᵠ(Spec K, ℤ/ℓ) = 0` for `q ≥ 2`.

By `AlgebraicGeometry.Scheme.sheafHConstantSheafAddEquivGaloisH` this is the Galois cohomology
of the trivial module `ℤ/ℓ` of the absolute Galois group `G` of `K`. This group has a continuous
character `χ: G → ℤ_ℓ` with `χ τ = 1` whose kernel has finite quotients of order prime to `ℓ`
(`IsDiscreteValuationRing.exists_isEllAdicQuotient`), so `Hᵠ(G, ℤ/ℓ) = 0` for `q ≥ 2` and
`H¹(G, ℤ/ℓ) = (ℤ/ℓ)^{ker χ} / (τ - 1) = ℤ/ℓ` (`DiscreteModule.IsEllAdicQuotient.HOneAddEquiv`).

## Main statements

- `IsDiscreteValuationRing.subsingleton_sheafH_constantZMod_spec_of_isFractionRing`: the
  vanishing in degrees `q ≥ 2`.
- `IsDiscreteValuationRing.nonempty_addEquiv_sheafH_one_constantZMod_spec_of_isFractionRing`:
  `H¹(Spec K, ℤ/ℓ) ≃ ℤ/ℓ`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

/-- The trivial discrete module `ℤ/ℓ` is `ℓ`-primary. -/
lemma DiscreteModule.isPrimary_trivial_zmod {G : Type u} [Group G] [TopologicalSpace G]
    (ℓ : ℕ) :
    IsPrimary ℓ (trivial.{u + 1} G (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)))) := by
  refine fun x ↦ ⟨1, ULift.ext ((ULift.smul_down x _).trans ?_)⟩
  rw [pow_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  rfl

namespace IsDiscreteValuationRing

variable {B K : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [HenselianLocalRing B] [IsSepClosed (ResidueField B)] [Field K] [Algebra B K]
  [IsFractionRing B K] {ℓ : ℕ} [Fact ℓ.Prime]

variable (K) in
/-- **Vanishing of the higher cohomology of the generic point of a strictly henselian trait.**
If `K` is the fraction field of a henselian discrete valuation ring `B` with separably closed
residue field, in which the prime `ℓ` is invertible, then `Hᵠ(Spec K, ℤ/ℓ) = 0` for `q ≥ 2`. -/
theorem subsingleton_sheafH_constantZMod_spec_of_isFractionRing
    (hℓ : (ℓ : ResidueField B) ≠ 0) (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H ((Spec (.of K)).constantZMod ℓ) q) := by
  have := subsingleton_H_galois_of_natCast_ne_zero.{u + 1} B (F := K) (Ω := SeparableClosure K) hℓ _
    (DiscreteModule.isPrimary_trivial_zmod ℓ) hq
  exact (Scheme.sheafHConstantSheafAddEquivGaloisH K (SeparableClosure K) _ q).toEquiv.subsingleton

variable (K) in
/-- **The first cohomology of the generic point of a strictly henselian trait.**
If `K` is the fraction field of a henselian discrete valuation ring `B` with separably closed
residue field, in which the prime `ℓ` is invertible, then `H¹(Spec K, ℤ/ℓ) ≃ ℤ/ℓ`. -/
theorem nonempty_addEquiv_sheafH_one_constantZMod_spec_of_isFractionRing
    (hℓ : (ℓ : ResidueField B) ≠ 0) :
    Nonempty (Sheaf.H ((Spec (.of K)).constantZMod ℓ) 1 ≃+ ZMod ℓ) := by
  obtain ⟨χ, τ, h⟩ := exists_isEllAdicQuotient B K (SeparableClosure K) hℓ
  set M := DiscreteModule.trivial.{u + 1} Gal(SeparableClosure K/K)
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)))
  have hfix : DiscreteModule.fixedAddSubgroup.{u + 1} M χ.toMonoidHom.ker = ⊤ :=
    eq_top_iff.2 fun _ _ _ _ ↦ rfl
  have hτ : (DiscreteModule.tauSubOne.{u + 1} χ τ M).range = ⊥ := by
    rw [AddMonoidHom.range_eq_bot_iff]
    ext x
    rw [DiscreteModule.coe_tauSubOne_apply]
    exact sub_self _
  exact ⟨(Scheme.sheafHConstantSheafAddEquivGaloisH K (SeparableClosure K) _ 1).trans <|
    (DiscreteModule.IsEllAdicQuotient.HOneAddEquiv.{u + 1} h (X := M)
      (DiscreteModule.isPrimary_trivial_zmod ℓ)).trans <|
    (QuotientAddGroup.quotientAddEquivOfEq hτ).trans <| QuotientAddGroup.quotientBot.trans <|
    (AddEquiv.addSubgroupCongr hfix).trans <| AddSubgroup.topEquiv.trans AddEquiv.ulift⟩

end IsDiscreteValuationRing
