/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.FieldTheory.KummerFreeSubgroup
public import WeilConjectures.Mathlib.FieldTheory.KrullTopology
public import WeilConjectures.RepresentationTheory.DiscreteModule.Procyclic
public import WeilConjectures.RingTheory.HenselianDVRExtension

/-!
# Galois cohomology of the fraction field of a strictly henselian DVR

Let `R` be a henselian discrete valuation ring with separably closed residue field `k`,
`F` its fraction field, `Ω` a separable closure of `F` and `G = Gal(Ω/F)`. Let `ℓ` be a prime
invertible in `k`. Then `Hᵠ(G, M) = 0` for `q > 1` and every `ℓ`-primary discrete `G`-module
`M`, and `H⁰(G, M)`, `H¹(G, M)` are finite for finite `M` (blueprint `lem-exc-dvr-galois`).

Choose a uniformizer `π` of `R` and compatible `ℓ ^ m`-th roots `π_m ∈ Ω` of `π`. As `F`
contains the `ℓ ^ m`-th roots of unity (Hensel's lemma), the Kummer character
`χ : G → ℤ_ℓ`, `σ (π_m) = ζ_m ^ χ(σ) π_m`, is a continuous homomorphism
(`KummerSystem.char`). It is nontrivial modulo `ℓ`, as `π` is not an `ℓ`-th power, so after
rescaling it takes the value `1` on some `τ ∈ G`. Its kernel `K` has all finite quotients of
order prime to `ℓ`: if `E / F` is finite Galois and `ℓ ^ b` is the `ℓ`-part of `[E : F]`,
then `E` contains an `ℓ ^ b`-th root of `π`, as `E / F` is totally ramified and units of the
integral closure are `ℓ ^ b`-th powers
(`IsDiscreteValuationRing.exists_pow_eq_algebraMap_of_dvd_finrank`); hence `π_b ∈ E` and the
image of `K` in `Gal(E/F)` lies in `Gal(E/F(π_b))`, of order prime to `ℓ`. The cohomology is then
computed by `DiscreteModule.IsEllAdicQuotient`: it is given by the two-term complex
`[Mᴷ --τ-1--> Mᴷ]` (blueprint `lem-exc-procyclic-two-term`).

## Main statements

- `IsDiscreteValuationRing.exists_isEllAdicQuotient`: the `ℓ`-adic procyclic quotient of `G`.
- `IsDiscreteValuationRing.subsingleton_H_galois`: the vanishing above degree one.
- `IsDiscreteValuationRing.finite_H_zero_galois`, `IsDiscreteValuationRing.finite_H_one_galois`:
  the finiteness.
-/

@[expose] public section

universe w u

open IsLocalRing Module IntermediateField Polynomial

namespace IsDiscreteValuationRing

variable {R F Ω : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [IsSepClosed (ResidueField R)] [Field F] [Algebra R F]
  [IsFractionRing R F] [Field Ω] [Algebra F Ω] [IsSepClosed Ω] [Algebra.IsSeparable F Ω]
  {ℓ : ℕ} [hℓ' : Fact ℓ.Prime]

omit [HenselianLocalRing R] [IsSepClosed (ResidueField R)] [IsDomain R]
  [IsDiscreteValuationRing R] [IsFractionRing R F] hℓ' in
/-- `ℓ` is invertible in `F` if it is invertible in the residue field of `R`. -/
lemma natCast_ne_zero_of_residue [IsLocalRing R]
    (hℓ : (ℓ : ResidueField R) ≠ 0) : (ℓ : F) ≠ 0 := by
  have : IsUnit (ℓ : R) := by
    by_contra h
    apply hℓ
    rw [← map_natCast (residue R), residue_eq_zero_iff]
    exact (mem_maximalIdeal _).2 h
  rw [← map_natCast (algebraMap R F)]
  intro h0
  exact not_isUnit_zero (h0 ▸ this.map (algebraMap R F))

omit [Fact ℓ.Prime] [IsDomain R] [IsDiscreteValuationRing R] in
/-- `F` contains the primitive `ℓ ^ m`-th roots of unity. -/
lemma exists_isPrimitiveRoot_pow (hℓ : (ℓ : ResidueField R) ≠ 0) (m : ℕ) :
    ∃ ζ : F, IsPrimitiveRoot ζ (ℓ ^ m) := by
  have : ((ℓ ^ m : ℕ) : ResidueField R) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hℓ
  obtain ⟨ζ, hζ⟩ := HenselianLocalRing.exists_isPrimitiveRoot this
  exact ⟨algebraMap R F ζ, hζ.map_of_injective (IsFractionRing.injective R F)⟩

omit [HenselianLocalRing R] [IsSepClosed (ResidueField R)] in
/-- A uniformizer is not an `ℓ`-th power in the fraction field. -/
lemma not_exists_pow_eq_algebraMap {π : R} (hπ : Irreducible π) :
    ¬ ∃ y : F, y ^ ℓ = algebraMap R F π := by
  rintro ⟨y, hy⟩
  have hℓ0 : ℓ ≠ 0 := hℓ'.out.ne_zero
  have hyint : IsIntegral R y :=
    ⟨X ^ ℓ - C π, monic_X_pow_sub_C π hℓ0, by simp [hy]⟩
  obtain ⟨z, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hyint
  rw [← map_pow] at hy
  have hz := IsFractionRing.injective R F hy
  obtain ⟨k, hk⟩ : ∃ k, ℓ = k + 2 := ⟨ℓ - 2, by have := hℓ'.out.two_le; omega⟩
  rw [hk, pow_succ] at hz
  have hzu : IsUnit z := by
    rcases hπ.isUnit_or_isUnit hz.symm with h | h
    · exact (isUnit_pow_iff (Nat.succ_ne_zero k)).1 h
    · exact h
  exact hπ.not_isUnit (hz ▸ (hzu.pow _).mul hzu)

/-- Multiplication by `c` on `ℤ_ℓ`, as a continuous endomorphism of `Multiplicative ℤ_[ℓ]`. -/
noncomputable def _root_.PadicInt.mulLeftContinuousMonoidHom (c : ℤ_[ℓ]) :
    Multiplicative ℤ_[ℓ] →ₜ* Multiplicative ℤ_[ℓ] where
  toFun x := .ofAdd (c * x.toAdd)
  map_one' := by simp
  map_mul' x y := by simp [mul_add]
  continuous_toFun := continuous_ofAdd.comp ((continuous_const.mul continuous_id).comp
    continuous_toAdd)

@[simp]
lemma _root_.PadicInt.toAdd_mulLeftContinuousMonoidHom_apply (c : ℤ_[ℓ])
    (x : Multiplicative ℤ_[ℓ]) :
    (PadicInt.mulLeftContinuousMonoidHom c x).toAdd = c * x.toAdd :=
  rfl

variable (R F Ω) in
/-- **The tame `ℓ`-adic quotient.** The absolute Galois group `G = Gal(Ω/F)` has a continuous
character `χ : G → ℤ_ℓ` with `χ τ = 1` for some `τ`, whose kernel has all its finite quotients of
order prime to `ℓ`. It is a rescaled Kummer character of a uniformizer. -/
theorem exists_isEllAdicQuotient (hℓ : (ℓ : ResidueField R) ≠ 0) :
    ∃ (χ : Gal(Ω/F) →ₜ* Multiplicative ℤ_[ℓ]) (τ : Gal(Ω/F)),
      DiscreteModule.IsEllAdicQuotient ℓ χ τ := by
  classical
  have : IsSepClosure F Ω := ⟨‹_›, ‹_›⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπF : algebraMap R F π ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective R F)]
    exact hπ.ne_zero
  obtain ⟨S, hS0⟩ := KummerSystem.exists_α_zero_eq (L := Ω) (natCast_ne_zero_of_residue hℓ)
    (exists_isPrimitiveRoot_pow hℓ) hπF
  -- an element moving `π ^ (1 / ℓ)`
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ : Gal(Ω/F), σ (S.α 1) ≠ S.α 1 := by
    by_contra! H
    obtain ⟨y, hy⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (S.α 1)).mpr H
    refine not_exists_pow_eq_algebraMap (F := F) (ℓ := ℓ) hπ ⟨y, (algebraMap F Ω).injective ?_⟩
    rw [map_pow, hy, ← hS0]
    exact S.α_succ_pow 0
  set a : ℤ_[ℓ] := (S.char σ₀).toAdd
  have ha1 : PadicInt.toZModPow 1 a ≠ 0 := by
    rw [S.toZModPow_char]
    intro h0
    apply hσ₀
    have := (S.charZMod_eq_iff (σ := σ₀) (m := 1) (c := 0)).1 h0
    simpa using this
  have ha : IsUnit a := by
    by_contra h
    apply ha1
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, pow_one,
      ← PadicInt.maximalIdeal_eq_span_p]
    exact (mem_maximalIdeal _).2 h
  set χ := (PadicInt.mulLeftContinuousMonoidHom (ha.unit⁻¹ : ℤ_[ℓ]ˣ)).comp S.char
  have hker (σ : Gal(Ω/F)) : χ σ = 1 ↔ S.char σ = 1 := by
    rw [← toAdd_eq_zero, ← toAdd_eq_zero (x := S.char σ)]
    change (PadicInt.mulLeftContinuousMonoidHom _ (S.char σ)).toAdd = 0 ↔ _
    rw [PadicInt.toAdd_mulLeftContinuousMonoidHom_apply, Units.mul_right_eq_zero]
  refine ⟨χ, σ₀, ⟨?_, fun U hU ↦ ?_⟩⟩
  · apply Multiplicative.toAdd.injective
    change (PadicInt.mulLeftContinuousMonoidHom _ (S.char σ₀)).toAdd = 1
    rw [PadicInt.toAdd_mulLeftContinuousMonoidHom_apply, IsUnit.val_inv_mul]
  -- the `ℓ`-freeness of `ker χ`
  have hGal : IsGalois F Ω := inferInstance
  obtain ⟨E, hEfin, hEnorm, hEU⟩ := (krullTopology_mem_nhds_one_iff_of_normal F Ω U).1
    (hU.mem_nhds U.one_mem)
  have hEsep : Algebra.IsSeparable F E := Algebra.isSeparable_tower_bot_of_isSeparable F E Ω
  have hEgal : IsGalois F E := ⟨⟩
  set N := E.fixingSubgroup
  set K := χ.toMonoidHom.ker
  set n := finrank F E
  have hn0 : n ≠ 0 := Module.finrank_pos.ne'
  set b := n.factorization ℓ
  let : Algebra R E := ((algebraMap F E).comp (algebraMap R F)).toAlgebra
  have : IsScalarTower R F E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨γ, hγ⟩ := exists_pow_eq_algebraMap_of_dvd_finrank R F E (N := ℓ ^ b)
    (by rw [Nat.cast_pow]; exact pow_ne_zero _ hℓ) (Nat.ordProj_dvd n ℓ) hπ
  -- `π ^ (1 / ℓ ^ b)` lies in `E`
  have hαE : S.α b ∈ E := by
    have hγΩ : (γ : Ω) ^ ℓ ^ b = S.α 0 := by
      rw [← IntermediateField.coe_pow, hγ, hS0]
      rfl
    have hα0 : S.α b ≠ 0 := S.α_ne_zero b
    obtain ⟨i, -, hi⟩ := (S.isPrimitiveRoot_ζ b).eq_pow_of_pow_eq_one
      (ξ := (γ : Ω) / S.α b) (by rw [div_pow, hγΩ, S.α_pow, div_self S.α_zero_ne_zero])
    have hζE : S.ζ b ∈ E := by
      obtain ⟨y, hy⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (S.ζ b)).mpr
        fun σ ↦ S.map_ζ σ b
      rw [← hy]
      exact E.algebraMap_mem y
    have hζ0 : S.ζ b ^ i ≠ 0 := pow_ne_zero _ ((S.isPrimitiveRoot_ζ b).ne_zero
      (pow_ne_zero _ hℓ'.out.ne_zero))
    have : S.α b = (γ : Ω) / S.ζ b ^ i := by
      have hγ0 : (γ : Ω) ≠ 0 := by
        rintro h
        rw [h, zero_pow (pow_ne_zero _ hℓ'.out.ne_zero)] at hγΩ
        exact S.α_zero_ne_zero hγΩ.symm
      rw [hi, div_div_cancel₀ hγ0]
    rw [this]
    exact E.div_mem γ.2 (pow_mem hζE i)
  set M := (S.charZMod b).ker
  have hKM : K ≤ M := by
    intro σ hσ
    rw [MonoidHom.mem_ker] at hσ ⊢
    have h1 : S.char σ = 1 := (hker σ).1 hσ
    apply Multiplicative.toAdd.injective
    rw [← S.toZModPow_char, h1, toAdd_one, map_zero, toAdd_one]
  have hNM : N ≤ M := by
    intro σ hσ
    rw [MonoidHom.mem_ker, ← toAdd_eq_zero, S.charZMod_eq_iff]
    simp only [ZMod.val_zero, pow_zero, one_mul]
    exact (_root_.mem_fixingSubgroup_iff _).1 hσ _ hαE
  have hMindex : M.index = ℓ ^ b := by
    rw [Subgroup.index_ker]
    have hu : IsUnit (S.charZMod b σ₀).toAdd := by
      rw [← S.toZModPow_char]
      exact ha.map _
    have : (S.charZMod b).range = ⊤ := by
      rw [eq_top_iff]
      rintro x -
      refine ⟨σ₀ ^ (x.toAdd * (hu.unit⁻¹ : (ZMod (ℓ ^ b))ˣ)).val, ?_⟩
      apply Multiplicative.toAdd.injective
      rw [map_pow, toAdd_pow, nsmul_eq_mul, ZMod.natCast_zmod_val, mul_assoc,
        IsUnit.val_inv_mul, mul_one]
    rw [this, Subgroup.card_top]
    exact (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod _)
  have hNker : (AlgEquiv.restrictNormalHom (K₁ := Ω) E).ker = N := E.restrictNormalHom_ker
  have hNindex : N.index = n := by
    rw [← hNker, Subgroup.index_ker,
      MonoidHom.range_eq_top_of_surjective _ (AlgEquiv.restrictNormalHom_surjective Ω),
      Subgroup.card_top, IsGalois.card_aut_eq_finrank]
  intro hdvd
  have h1 : ℓ ∣ N.relIndex K := hdvd.trans (Subgroup.relIndex_dvd_of_le_left K hEU)
  have : N.Normal := by
    rw [← hNker]
    exact MonoidHom.normal_ker _
  rw [← Subgroup.relIndex_sup_right] at h1
  have h2 : N.relIndex (K ⊔ N) ∣ N.relIndex M :=
    ⟨_, (Subgroup.relIndex_mul_relIndex N (K ⊔ N) M le_sup_right (sup_le hKM hNM)).symm⟩
  have h3 : N.relIndex M * ℓ ^ b = n := by
    rw [← hMindex, ← hNindex]
    exact Subgroup.relIndex_mul_index hNM
  obtain ⟨c, hc⟩ := h1.trans h2
  have h4 : ℓ ^ (b + 1) ∣ n := ⟨c, by rw [← h3, hc]; ring⟩
  exact Nat.pow_succ_factorization_not_dvd hn0 hℓ'.out h4

omit [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [IsSepClosed (ResidueField R)] in
/-- A prime `ℓ` different from the characteristic `p` of a field is invertible in it. -/
lemma natCast_ne_zero_of_ne [IsLocalRing R] {p : ℕ} [CharP (ResidueField R) p] (hp : p.Prime)
    (hℓp : ℓ ≠ p) : (ℓ : ResidueField R) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff (ResidueField R) p]
  intro h
  exact hℓp ((Nat.prime_dvd_prime_iff_eq hp hℓ'.out).1 h).symm

variable (R) in
/-- The vanishing of `Hᵠ(Gal(Ω/F), M)` for `q > 1` and `ℓ`-primary `M`, for a prime `ℓ`
invertible in the residue field. See `IsDiscreteValuationRing.subsingleton_H_galois`. -/
theorem subsingleton_H_galois_of_natCast_ne_zero (hℓ : (ℓ : ResidueField R) ≠ 0)
    (M : DiscreteModule.{w} Gal(Ω/F)) (hM : DiscreteModule.IsPrimary ℓ M) {q : ℕ} (hq : 1 < q) :
    Subsingleton (DiscreteModule.H Gal(Ω/F) M q) := by
  have : IsSepClosure F Ω := ⟨‹_›, ‹_›⟩
  obtain ⟨χ, τ, h⟩ := exists_isEllAdicQuotient R F Ω hℓ
  exact h.subsingleton_H M hM hq

omit [IsSepClosed (ResidueField R)] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [IsFractionRing R F] [IsSepClosed Ω] [Algebra.IsSeparable F Ω]
  [Fact ℓ.Prime] in
/-- `H⁰(Gal(Ω/F), M)` is finite for finite `M`. -/
theorem finite_H_zero_galois (M : DiscreteModule.{w} Gal(Ω/F)) [Finite M.obj.V] :
    Finite (DiscreteModule.H Gal(Ω/F) M 0) :=
  Finite.of_injective (fun x ↦ (DiscreteModule.H_zero_addEquiv M x).1)
    (Subtype.val_injective.comp (DiscreteModule.H_zero_addEquiv M).injective)

variable (R) in
/-- `H¹(Gal(Ω/F), M)` is finite for finite `ℓ`-primary `M`, for a prime `ℓ` invertible in the
residue field: it is a quotient of `Mᴷ` (`DiscreteModule.IsEllAdicQuotient.HOneAddEquiv`). -/
theorem finite_H_one_galois_of_natCast_ne_zero (hℓ : (ℓ : ResidueField R) ≠ 0)
    (M : DiscreteModule.{w} Gal(Ω/F)) (hM : DiscreteModule.IsPrimary ℓ M) [Finite M.obj.V] :
    Finite (DiscreteModule.H Gal(Ω/F) M 1) := by
  have : IsSepClosure F Ω := ⟨‹_›, ‹_›⟩
  obtain ⟨χ, τ, h⟩ := exists_isEllAdicQuotient R F Ω hℓ
  have : Finite (DiscreteModule.fixedAddSubgroup M χ.toMonoidHom.ker) := Subtype.finite
  exact Finite.of_equiv _ (h.HOneAddEquiv hM).symm.toEquiv


variable (R) in
/-- Blueprint `lem-exc-dvr-galois`: The prime-to-characteristic local Galois calculation.

Let `R` be a discrete valuation ring which is strictly henselian, with separably closed
residue field of characteristic `p > 0`; put `F = Frac(R)`, `G = Gal(Ω/F)` for a separable
closure `Ω` of `F`, and fix a prime `ℓ ≠ p`. Then `Hᵠ(G, M) = 0` for `q > 1` and every discrete
`G`-module `M` killed by a power of `ℓ` (more generally `ℓ`-primary); if `M` is finite, then
`H⁰(G, M)` and `H¹(G, M)` are finite (`IsDiscreteValuationRing.finite_H_zero_galois`,
`IsDiscreteValuationRing.finite_H_one_galois`).

Discrete modules over a finite ring `A` killed by a power of `ℓ` are in particular `ℓ`-primary
discrete `G`-modules, and the cohomology is computed with `ℤ`-coefficients (see
`DiscreteModule`). The excellence assumption of the blueprint is not needed: integral closures
in finite separable extensions of `F` are finite over `R`; and the residue field only needs to
be separably closed. -/
theorem subsingleton_H_galois {p : ℕ} [CharP (ResidueField R) p] (hp : p.Prime) (hℓp : ℓ ≠ p)
    (M : DiscreteModule.{w} Gal(Ω/F)) (hM : DiscreteModule.IsPrimary ℓ M) {q : ℕ} (hq : 1 < q) :
    Subsingleton (DiscreteModule.H Gal(Ω/F) M q) :=
  subsingleton_H_galois_of_natCast_ne_zero R (natCast_ne_zero_of_ne hp hℓp) M hM hq

variable (R) in
/-- Blueprint `lem-exc-dvr-galois`: The prime-to-characteristic local Galois calculation,
finiteness of `H¹` (see `IsDiscreteValuationRing.subsingleton_H_galois`). -/
theorem finite_H_one_galois {p : ℕ} [CharP (ResidueField R) p] (hp : p.Prime) (hℓp : ℓ ≠ p)
    (M : DiscreteModule.{w} Gal(Ω/F)) (hM : DiscreteModule.IsPrimary ℓ M) [Finite M.obj.V] :
    Finite (DiscreteModule.H Gal(Ω/F) M 1) :=
  finite_H_one_galois_of_natCast_ne_zero R (natCast_ne_zero_of_ne hp hℓp) M hM


end IsDiscreteValuationRing
