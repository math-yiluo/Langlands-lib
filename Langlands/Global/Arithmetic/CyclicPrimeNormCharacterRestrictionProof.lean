import Langlands.Global.Arithmetic.CyclicPrimeNormCharacterRestrictionStatement
import Langlands.Global.Arithmetic.CyclicNormKernelCharacterProof
import Langlands.Global.AdelicFunctoriality.IdeleClassNormTowerProof
import Langlands.Global.AdelicFunctoriality.IdeleClassNormTransport
import Langlands.Global.AdelicFunctoriality.IdeleNormLift

/-! # Norm-trivial characters at the bottom prime step of a cyclic tower

For a tower `F ⊂ K ⊂ E` of cyclic Galois extensions of number fields, every Hecke
character of `K` trivial on norms from `E` is a power of the pullback along the
norm `C_K → C_F` of a norm-kernel character of `E/F`. Hence it is invariant under
`Gal(K/F)`. When `[K : F]` is prime and the character is nontrivial with trivial
`[K : F]`-th power, its restriction along the inclusion `C_F → C_K` has kernel
exactly the norm image of `C_K` in `C_F`.
-/

noncomputable section

universe uF uK uE

set_option autoImplicit false

namespace Langlands.Global.HeckeCharacter

open Langlands.Global.AdelicFunctoriality

/-- A Hecke character with value `1` at every idele class is the trivial character. -/
private theorem eq_one_of_forall_apply {F : Type uF} [Field F] [NumberField F]
    (χ : HeckeCharacter F) (h : ∀ x, χ x = 1) : χ = 1 :=
  ContinuousMonoidHom.ext h

/-- The pullback of `η` along the norm, evaluated on the image of the inclusion, is the
degree-th power of `η`. -/
private theorem comp_norm_comp_inclusion_apply {F : Type uF} {K : Type uK}
    [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
    (η : HeckeCharacter F) (x : IdeleClasses F) :
    η (ideleClassNorm (K := F) (L := K) (ideleClassInclusion (K := F) (L := K) x)) =
      η x ^ Module.finrank F K := by
  rw [ideleClassNormInclusionPower F K x, map_pow]

/-- Every Hecke character of `K` trivial on norms from `E` is invariant under `Gal(K/F)`;
if it is nontrivial with `χ ^ [K : F] = 1` and `[K : F]` is prime, its restriction to
`C_F` has kernel exactly the norm image from `C_K`. -/
theorem cyclicPrimeNormCharacterRestriction :
    CyclicPrimeNormCharacterRestrictionStatement.{uF, uK, uE} := by
  intro F K E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hprime χ hχ
  -- The three norm-kernel characters.
  obtain ⟨⟨η, hη⟩, hηall⟩ := cyclicNormKernelCharacter.{uF, uE} F E
  obtain ⟨hηord, -⟩ := hηall η hη
  obtain ⟨⟨θ, hθ⟩, hθall⟩ := cyclicNormKernelCharacter.{uK, uE} K E
  obtain ⟨hθord, hθpow⟩ := hθall θ hθ
  obtain ⟨⟨ρ, hρ⟩, hρall⟩ := cyclicNormKernelCharacter.{uF, uK} F K
  obtain ⟨-, hρpow⟩ := hρall ρ hρ
  clear hηall hθall hρall
  -- Degrees: `n = [E : F] = p * m`, with `p = [K : F]` and `m = [E : K]`.
  have hnpm : Module.finrank F E = Module.finrank F K * Module.finrank K E :=
    (Module.finrank_mul_finrank F K E).symm
  set p := Module.finrank F K with hp_def
  set m := Module.finrank K E with hm_def
  set n := Module.finrank F E with hn_def
  have hp_pos : 0 < p := hprime.pos
  have hm_pos : 0 < m := Module.finrank_pos
  -- The pullback of `η` along the norm from `K` to `F`.
  let ψ : HeckeCharacter K := η.comp (ideleClassNorm (K := F) (L := K))
  have hψ_apply (y : IdeleClasses K) : ψ y = η (ideleClassNorm (K := F) (L := K) y) := rfl
  have hψtriv : ψ.IsTrivialOnNorm E := by
    intro y
    rw [hψ_apply, ← ideleClassNormTower F K E y]
    exact hη.isTrivialOnNorm y
  -- If `ψ ^ d = 1` then `η ^ (p * d) = 1`, hence `m ∣ d`.
  have hdvd_of_pow (d : ℕ) (hd : ψ ^ d = 1) : m ∣ d := by
    have hηpow : η ^ (p * d) = 1 := by
      apply eq_one_of_forall_apply
      intro x
      have h := congrArg
        (fun φ : HeckeCharacter K => φ (ideleClassInclusion (K := F) (L := K) x)) hd
      simp only [ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.one_toFun] at h
      rw [hψ_apply, comp_norm_comp_inclusion_apply] at h
      rw [ContinuousMonoidHom.pow_apply, pow_mul, h]
    have h := orderOf_dvd_of_pow_eq_one hηpow
    rw [hηord, hnpm] at h
    exact Nat.dvd_of_mul_dvd_mul_left hp_pos h
  have hψord : orderOf ψ = m :=
    Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one (hψtriv.pow_finrank_eq_one E))
      (hdvd_of_pow _ (pow_orderOf_eq_one ψ))
  -- `ψ` generates the cyclic group of characters trivial on norms from `E`.
  have hzpowers : Subgroup.zpowers ψ = Subgroup.zpowers θ := by
    obtain ⟨k, -, hk⟩ := (hθpow ψ).mp hψtriv
    have hle : Subgroup.zpowers ψ ≤ Subgroup.zpowers θ := by
      rw [Subgroup.zpowers_le, hk]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers θ) k
    have : Finite (Subgroup.zpowers θ) := by
      apply Nat.finite_of_card_ne_zero
      rw [Nat.card_zpowers, hθord]
      exact hm_pos.ne'
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [Nat.card_zpowers, Nat.card_zpowers, hθord, hψord]
  have hψfin : IsOfFinOrder ψ := orderOf_pos_iff.mp (hψord ▸ hm_pos)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ψ ^ k = χ := by
    obtain ⟨i, -, hi⟩ := (hθpow χ).mp hχ
    have hmem : χ ∈ Subgroup.zpowers ψ := by
      rw [hzpowers, hi]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers θ) i
    exact Submonoid.mem_powers_iff _ _ |>.mp (hψfin.mem_powers_iff_mem_zpowers.mpr hmem)
  have hχ_apply (y : IdeleClasses K) :
      χ y = η (ideleClassNorm (K := F) (L := K) y) ^ k := by
    rw [← hk, ContinuousMonoidHom.pow_apply]
    rfl
  refine ⟨?_, ?_⟩
  · -- Invariance: the norm is unchanged by an automorphism of `K` over `F`.
    intro τ
    apply ContinuousMonoidHom.ext
    intro y
    rw [comap_apply, hχ_apply, hχ_apply,
      ideleClassNorm_equiv (RingEquiv.refl F) τ.toRingEquiv (fun a => τ.commutes a) y,
      ideleClassEquiv_refl]
    rfl
  · intro hχp hχne
    let χF : HeckeCharacter F := χ.comp (ideleClassInclusion (K := F) (L := K))
    have hχF_apply (x : IdeleClasses F) : χF x = (η x ^ p) ^ k := by
      change χ (ideleClassInclusion (K := F) (L := K) x) = _
      rw [hχ_apply, comp_norm_comp_inclusion_apply]
    -- The restriction is trivial on norms from `K`.
    have hχFtriv : χF.IsTrivialOnNorm K := by
      intro y
      rw [hχF_apply, ← pow_mul, mul_comm, pow_mul, ← hχ_apply]
      have h := congrArg (fun φ : HeckeCharacter K => φ y) hχp
      simpa only [ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.one_toFun] using h
    -- The restriction is nontrivial.
    have hχFne : χF ≠ 1 := by
      intro h1
      apply hχne
      have hηpow : η ^ (p * k) = 1 := by
        apply eq_one_of_forall_apply
        intro x
        have h := congrArg (fun φ : HeckeCharacter F => φ x) h1
        simp only [ContinuousMonoidHom.one_toFun] at h
        rw [hχF_apply] at h
        rw [ContinuousMonoidHom.pow_apply, pow_mul, h]
      have h := orderOf_dvd_of_pow_eq_one hηpow
      rw [hηord, hnpm] at h
      have hmk : m ∣ k := Nat.dvd_of_mul_dvd_mul_left hp_pos h
      rw [← hk]
      exact orderOf_dvd_iff_pow_eq_one.mp (hψord ▸ hmk)
    obtain ⟨i, hip, hi⟩ := (hρpow χF).mp hχFtriv
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact hχFne (by rw [hi, pow_zero])
    have hcop : Nat.gcd i p = 1 := (Nat.coprime_of_lt_prime hi0 hip hprime).symm
    have hρp : ρ ^ p = 1 := hρ.isTrivialOnNorm.pow_finrank_eq_one K
    intro x
    constructor
    · intro hx
      apply (hρ x).mp
      have h1 : ρ x ^ i = 1 := by
        rw [← ContinuousMonoidHom.pow_apply, ← hi]
        exact hx
      have h2 : ρ x ^ p = 1 := by
        rw [← ContinuousMonoidHom.pow_apply, hρp]
        rfl
      have h := pow_gcd_eq_one.mpr ⟨h1, h2⟩
      rwa [hcop, pow_one] at h
    · rintro ⟨y, rfl⟩
      exact hχFtriv y

end Langlands.Global.HeckeCharacter
