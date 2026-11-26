import Langlands.Global.Arithmetic.HarrisAuxiliaryConjugatePairStatement
import Langlands.Global.Arithmetic.HarrisDatumCharacterRealizationProof
import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# A place above a split imaginary quadratic prime differs from its conjugate

Let `E` be a CM field, `K₀ ⊆ E` an imaginary quadratic subfield in which the rational prime
`p` splits, and `v` a finite place of `E` above `p`. Complex conjugation of `E` restricts to
the complex conjugation of `K₀`, so if `v` were equal to its conjugate, the place of `K₀`
below `v` would be fixed by the complex conjugation of `K₀`. That conjugation is the
non-trivial element of the group `Gal(K₀/ℚ)` of order two, so this place would be fixed by
the whole Galois group, which acts transitively on the primes above `p`. Hence there would be
only one prime of `K₀` above `p`, contradicting the splitting of `p`.
-/

noncomputable section

universe u

set_option autoImplicit false

namespace Langlands.Global.Harris

open NumberField IsDedekindDomain Langlands.Global.AdelicFunctoriality
open scoped Pointwise

section QuadraticField

variable {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
/-- A finite place of a number field containing the rational prime `p` lies over `(p)`. -/
theorem under_eq_span_of_natCast_mem (p : ℕ) [hp : Fact p.Prime] (w : FinitePlace K)
    (h : (p : 𝓞 K) ∈ w.asIdeal) :
    w.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := by
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp.out).irreducible
  refine (hmax.eq_of_le (Ideal.IsPrime.under ℤ w.asIdeal).ne_top ?_).symm
  rw [Ideal.span_le, Set.singleton_subset_iff]
  change algebraMap ℤ (𝓞 K) (p : ℤ) ∈ w.asIdeal
  rw [map_natCast]
  exact h

/-- Let `K` be a CM field of degree two over `ℚ`, that is, an imaginary quadratic field. If a
finite place `w` above the rational prime `p` is fixed by complex conjugation, then every
finite place `P` above `p` equals `w`. -/
theorem eq_of_conjPlace_eq_self [IsCMField K] (p : ℕ) [Fact p.Prime]
    (h2 : Module.finrank ℚ K = 2) {w P : FinitePlace K} (hw : (p : 𝓞 K) ∈ w.asIdeal)
    (hP : (p : 𝓞 K) ∈ P.asIdeal) (hc : conjPlace K w = w) : P = w := by
  have : Algebra.IsQuadraticExtension ℚ K := ⟨h2⟩
  have hcard : Nat.card Gal(K/ℚ) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, h2]
  have : Fact (Nat.card Gal(K/ℚ)).Prime := ⟨hcard ▸ Nat.prime_two⟩
  let τ : Gal(K/ℚ) := (IsCMField.complexConj K).restrictScalars ℚ
  have hτ : τ ≠ 1 := by
    intro h
    apply IsCMField.complexConj_ne_one K
    ext x
    exact congrArg (fun σ : Gal(K/ℚ) ↦ σ x) h
  -- `τ` preserves `w`.
  have hkey : ∀ x : 𝓞 K, τ • x ∈ w.asIdeal ↔ x ∈ w.asIdeal := by
    intro x
    have hx : x ∈ (conjPlace K w).asIdeal ↔ x ∈ w.asIdeal := by rw [hc]
    rw [← hx]
    exact Iff.rfl
  have hstab : τ ∈ MulAction.stabilizer Gal(K/ℚ) w.asIdeal := by
    rw [MulAction.mem_stabilizer_iff]
    ext x
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← hkey, smul_inv_smul]
  have htop : MulAction.stabilizer Gal(K/ℚ) w.asIdeal = ⊤ := by
    rcases (MulAction.stabilizer Gal(K/ℚ) w.asIdeal).eq_bot_or_eq_top_of_prime_card with h | h
    · rw [h, Subgroup.mem_bot] at hstab
      exact absurd hstab hτ
    · exact h
  have hunder : w.asIdeal.under ℤ = P.asIdeal.under ℤ := by
    rw [under_eq_span_of_natCast_mem p w hw, under_eq_span_of_natCast_mem p P hP]
  obtain ⟨σ, hσ⟩ :=
    Algebra.IsInvariant.exists_smul_of_under_eq ℤ (𝓞 K) Gal(K/ℚ) w.asIdeal P.asIdeal hunder
  have hσw : σ • w.asIdeal = w.asIdeal :=
    MulAction.mem_stabilizer_iff.mp (htop ▸ Subgroup.mem_top σ)
  exact HeightOneSpectrum.ext (hσ.trans hσw)

end QuadraticField

/-- If the rational prime `p` splits in an imaginary quadratic subfield `K₀` of the CM field
`E`, then every finite place of `E` above `p` differs from its complex conjugate. -/
theorem splitPlaceNeConjPlace : SplitPlaceNeConjPlaceStatement.{u} := by
  intro p _ E _ _ _ K₀ v ⟨h2, hTC, P, Q, hPQ, hpP, hpQ⟩ hpv hv
  have : Algebra.IsQuadraticExtension ℚ K₀ := ⟨h2⟩
  have : IsCMField K₀ := IsCMField.ofCMExtension ℚ K₀
  let w : FinitePlace K₀ := HeightOneSpectrum.under (𝓞 K₀) v
  have hw : (p : 𝓞 K₀) ∈ w.asIdeal := by
    change algebraMap (𝓞 K₀) (𝓞 E) (p : 𝓞 K₀) ∈ v.asIdeal
    rw [map_natCast]
    exact hpv
  have : v.asIdeal.LiesOver w.asIdeal := ⟨rfl⟩
  have := HarrisDatum.conjPlace_liesOver w v
  have hcw : conjPlace K₀ w = w := by
    by_contra hne
    exact HarrisDatum.ne_of_liesOver (v₁ := conjPlace K₀ w) (v₂ := w)
      (w₁ := finitePlaceEquiv (IsCMField.complexConj E).toRingEquiv v) (w₂ := v) hne hv.symm
  exact hPQ ((eq_of_conjPlace_eq_self p h2 hw hpP hcw).trans
    (eq_of_conjPlace_eq_self p h2 hw hpQ hcw).symm)

end Langlands.Global.Harris
