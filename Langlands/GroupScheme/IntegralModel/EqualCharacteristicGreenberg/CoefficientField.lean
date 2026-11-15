import Langlands.GroupScheme.IntegralModel.CongruenceTower
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Smooth.Field

/-! # Coefficient fields of the congruence quotients of an equal-characteristic local ring -/

noncomputable section

universe u

namespace Langlands.GroupScheme.IntegralModel

open IsLocalRing

section Residue

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- The actual residue homomorphism of a positive congruence quotient. -/
def congruenceResidue (n : ℕ+) : congruenceRing R n →+* ResidueField R :=
  Ideal.Quotient.factor (Ideal.pow_le_self n.ne_zero)

@[simp] theorem congruenceResidue_quotient (n : ℕ+) (r : R) :
    congruenceResidue R n (congruenceQuotient R n r) = residue R r := rfl

theorem congruenceResidue_surjective (n : ℕ+) :
    Function.Surjective (congruenceResidue R n) := by
  intro x
  obtain ⟨r, rfl⟩ := residue_surjective x
  exact ⟨congruenceQuotient R n r, rfl⟩

theorem mem_ker_congruenceResidue {n : ℕ+} {x : congruenceRing R n}
    (hx : congruenceResidue R n x = 0) :
    x ∈ (maximalIdeal R).map (congruenceQuotient R n) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hr : residue R r = 0 := hx
  exact Ideal.mem_map_of_mem _ ((residue_eq_zero_iff r).mp hr)

/-- The kernel of the residue homomorphism of a congruence quotient is nilpotent. -/
theorem isNilpotent_ker_congruenceResidue (n : ℕ+) :
    IsNilpotent (RingHom.ker (congruenceResidue R n)) := by
  refine ⟨(n : ℕ), ?_⟩
  have h1 : RingHom.ker (congruenceResidue R n) ^ (n : ℕ)
      ≤ ((maximalIdeal R).map (congruenceQuotient R n)) ^ (n : ℕ) :=
    Ideal.pow_right_mono (fun x hx => mem_ker_congruenceResidue R (RingHom.mem_ker.mp hx)) _
  have h2 : ((maximalIdeal R).map (congruenceQuotient R n)) ^ (n : ℕ) = ⊥ := by
    rw [← Ideal.map_pow]
    exact Ideal.map_quotient_self _
  exact le_bot_iff.mp (h2 ▸ h1)

end Residue

section CharZero

/-- Every field of characteristic zero is formally smooth over the integers: it is
separable algebraic over a purely transcendental extension of the rationals. -/
theorem formallySmooth_int_of_charZero (K : Type u) [Field K] [CharZero K] [Algebra ℤ K] :
    Algebra.FormallySmooth ℤ K := by
  obtain rfl : ‹Algebra ℤ K› = Ring.toIntAlgebra K := Subsingleton.elim _ _
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℚ K
  have : Algebra.IsAlgebraic (IntermediateField.adjoin ℚ (Set.range ((↑) : s → K))) K :=
    hs.isAlgebraic_field
  have : Algebra.FormallySmooth ℚ K :=
    Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1
  have : Algebra.FormallySmooth ℤ ℚ :=
    Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors ℤ)
  exact Algebra.FormallySmooth.comp ℤ ℚ K

end CharZero

section Coefficient

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- In residue characteristic zero, formal smoothness of the residue field over the
integers lifts the identity of the residue field through the nilpotent residue kernel. -/
theorem exists_coefficientField_of_charZero [CharZero (ResidueField R)] (n : ℕ+) :
    ∃ σ : ResidueField R →+* congruenceRing R n,
      (congruenceResidue R n).comp σ = RingHom.id _ := by
  have := formallySmooth_int_of_charZero (ResidueField R)
  let g : congruenceRing R n →ₐ[ℤ] ResidueField R :=
    { toRingHom := congruenceResidue R n
      commutes' := fun z => by
        change congruenceResidue R n (algebraMap ℤ _ z) = algebraMap ℤ _ z
        rw [eq_intCast (algebraMap ℤ (congruenceRing R n)) z,
          eq_intCast (algebraMap ℤ (ResidueField R)) z, map_intCast] }
  have hg : Function.Surjective g := fun x => congruenceResidue_surjective R n x
  have hg' : IsNilpotent (RingHom.ker (g : congruenceRing R n →+* ResidueField R)) :=
    isNilpotent_ker_congruenceResidue R n
  let σ := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id ℤ (ResidueField R)) g hg hg'
  refine ⟨σ.toRingHom, RingHom.ext fun x => ?_⟩
  exact Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id ℤ (ResidueField R)) g hg hg' x

/-- In equal positive characteristic `p` with perfect residue field, the composite of the
inverse Frobenius power on the residue field with the `p ^ n`-th power of arbitrary
lifts is a ring section of the residue map. -/
theorem exists_coefficientField_of_charP (p : ℕ) [Fact p.Prime] [CharP R p]
    [CharP (ResidueField R) p] [PerfectRing (ResidueField R) p] (n : ℕ+) :
    ∃ σ : ResidueField R →+* congruenceRing R n,
      (congruenceResidue R n).comp σ = RingHom.id _ := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hle : (n : ℕ) ≤ p ^ (n : ℕ) := (Nat.lt_pow_self hp).le
  let τ : R →+* congruenceRing R n :=
    (congruenceQuotient R n).comp (iterateFrobenius R p n)
  have hτ : ∀ r ∈ maximalIdeal R, τ r = 0 := by
    intro r hr
    change Ideal.Quotient.mk _ (r ^ p ^ (n : ℕ)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_le_pow_right hle (Ideal.pow_mem_pow hr _)
  let τ' : ResidueField R →+* congruenceRing R n := Ideal.Quotient.lift _ τ hτ
  refine ⟨τ'.comp (iterateFrobeniusEquiv (ResidueField R) p n).symm.toRingHom,
    RingHom.ext fun x => ?_⟩
  obtain ⟨r, hr⟩ := residue_surjective
    ((iterateFrobeniusEquiv (ResidueField R) p n).symm x)
  have hx : x = iterateFrobenius (ResidueField R) p n (residue R r) := by
    rw [hr, ← coe_iterateFrobeniusEquiv, RingEquiv.apply_symm_apply]
  change congruenceResidue R n
    (τ' ((iterateFrobeniusEquiv (ResidueField R) p n).symm x)) = x
  rw [← hr]
  change residue R (r ^ p ^ (n : ℕ)) = x
  rw [map_pow, hx, iterateFrobenius_def]

/-- **Coefficient fields in equal characteristic.** If the residue field of a local ring
is algebraically closed and has the same characteristic as the ring, every positive
congruence quotient has a ring section of its residue map. -/
theorem exists_coefficientField [IsAlgClosed (ResidueField R)]
    (hchar : ringChar R = ringChar (ResidueField R)) (n : ℕ+) :
    ∃ σ : ResidueField R →+* congruenceRing R n,
      (congruenceResidue R n).comp σ = RingHom.id _ := by
  rcases CharP.char_is_prime_or_zero (ResidueField R) (ringChar (ResidueField R)) with
    hp | h0
  · have : Fact (ringChar (ResidueField R)).Prime := ⟨hp⟩
    have : CharP R (ringChar (ResidueField R)) := ringChar.of_eq hchar
    have : CharP (ResidueField R) (ringChar (ResidueField R)) := ringChar.charP _
    exact exists_coefficientField_of_charP R (ringChar (ResidueField R)) n
  · have : CharP (ResidueField R) 0 := h0 ▸ ringChar.charP (ResidueField R)
    have : CharZero (ResidueField R) := CharP.charP_to_charZero (ResidueField R)
    exact exists_coefficientField_of_charZero R n

end Coefficient

section Finite

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- A congruence quotient of a DVR is finite over any ring section of its residue map:
it is spanned by the powers of a uniformizer below the level. -/
theorem congruenceRing_finite (n : ℕ+) (σ : ResidueField R →+* congruenceRing R n)
    (hσ : (congruenceResidue R n).comp σ = RingHom.id _) :
    letI := σ.toAlgebra
    Module.Finite (ResidueField R) (congruenceRing R n) := by
  let _ : Algebra (ResidueField R) (congruenceRing R n) := σ.toAlgebra
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let π : congruenceRing R n := congruenceQuotient R n ϖ
  have hker : ∀ y : congruenceRing R n, congruenceResidue R n y = 0 → ∃ z, y = π * z := by
    intro y hy
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hr : r ∈ maximalIdeal R := (residue_eq_zero_iff r).mp hy
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hr
    obtain ⟨a, rfl⟩ := hr
    exact ⟨congruenceQuotient R n a, by
      change congruenceQuotient R n (a * ϖ) = _
      rw [map_mul, mul_comm]⟩
  let S : Submodule (ResidueField R) (congruenceRing R n) :=
    Submodule.span (ResidueField R) (Set.range fun i : Fin n => π ^ (i : ℕ))
  have hstep : ∀ j : ℕ, j ≤ n → ∀ x : congruenceRing R n,
      ∃ s ∈ S, ∃ y, x = s + π ^ j * y := by
    intro j
    induction j with
    | zero => intro _ x; exact ⟨0, S.zero_mem, x, by simp⟩
    | succ j ih =>
      intro hj x
      obtain ⟨s, hs, y, rfl⟩ := ih (by omega) x
      let c := σ (congruenceResidue R n y)
      obtain ⟨z, hz⟩ := hker (y - c) (by
        rw [map_sub]
        change _ - ((congruenceResidue R n).comp σ) _ = 0
        rw [hσ, RingHom.id_apply, sub_self])
      refine ⟨s + (congruenceResidue R n y) • π ^ j, ?_, z, ?_⟩
      · refine S.add_mem hs (S.smul_mem _ (Submodule.subset_span ⟨⟨j, by omega⟩, rfl⟩))
      · rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
        linear_combination (π ^ j) * hz
  have hπn : π ^ (n : ℕ) = 0 := by
    change congruenceQuotient R n (ϖ ^ (n : ℕ)) = 0
    rw [congruenceQuotient, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow (hϖ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self ϖ) _
  have htop : S = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨s, hs, y, rfl⟩ := hstep n le_rfl x
    rw [hπn, zero_mul, add_zero]
    exact hs
  rw [Module.finite_def, ← htop]
  exact Submodule.fg_span (Set.finite_range _)

end Finite

end Langlands.GroupScheme.IntegralModel
