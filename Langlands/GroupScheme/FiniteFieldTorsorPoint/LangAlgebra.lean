import Mathlib

/-! # Commutative algebra for Lang's theorem -/

namespace Langlands.GroupScheme.FiniteFieldTorsorPoint

open Submodule

section Finite

variable {C A : Type*} [CommRing C] [CommRing A] [Algebra C A]

private theorem prod_pow_add_single {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → A)
    (n : ι → ℕ) (j : ι) (k : ℕ) :
    ∏ l, v l ^ (n + Pi.single j k : ι → ℕ) l = v j ^ k * ∏ l, v l ^ n l := by
  simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
  rw [mul_comm]
  congr 1
  rw [Finset.prod_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
  simp

/-- If the `q`-th power of each generator lies in the span of `1` and the generators, then
every monomial lies in the span of the monomials with all exponents below `q`. -/
theorem monomial_mem_span_of_pow_mem_span {ι : Type*} [Fintype ι] (v : ι → A) {q : ℕ}
    (hq : 2 ≤ q) (hv : ∀ i, v i ^ q ∈ span C (insert 1 (Set.range v))) (n : ι → ℕ) :
    ∏ i, v i ^ n i ∈ span C (Set.range fun e : ι → Fin q => ∏ i, v i ^ (e i : ℕ)) := by
  classical
  set N := span C (Set.range fun e : ι → Fin q => ∏ i, v i ^ (e i : ℕ))
  induction h : ∑ i, n i using Nat.strong_induction_on generalizing n with
  | _ d ih =>
    by_cases hlt : ∀ i, n i < q
    · exact subset_span ⟨fun i => ⟨n i, hlt i⟩, rfl⟩
    simp only [not_forall, not_lt] at hlt
    obtain ⟨i, hi⟩ := hlt
    obtain ⟨a, z, hz, hza⟩ := mem_span_insert.mp (hv i)
    obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun C).mp hz
    set n' : ι → ℕ := n - Pi.single i q
    have hn : n = n' + Pi.single i q := by
      funext l
      by_cases hl : l = i
      · subst hl; simp [n']; omega
      · simp [n', hl]
    have hsum : ∀ (j : ι) (k : ℕ), ∑ l, (n' + Pi.single j k : ι → ℕ) l = ∑ l, n' l + k := by
      intro j k
      simp [Finset.sum_add_distrib]
    have hd : ∑ l, n' l + q = d := by rw [← hsum, ← hn, h]
    rw [hn, prod_pow_add_single, hza, add_mul, Finset.sum_mul]
    refine N.add_mem ?_ (N.sum_mem fun j _ => ?_)
    · rw [smul_mul_assoc, one_mul]
      exact N.smul_mem _ (ih _ (by omega) n' rfl)
    · rw [smul_mul_assoc, ← pow_one (v j), ← prod_pow_add_single]
      exact N.smul_mem _ (ih _ (by rw [hsum]; omega) _ rfl)

/-- A finitely generated algebra whose generators have `q`-th powers in the span of `1` and the
generators is a finite module. -/
theorem finite_of_pow_mem_span {ι : Type*} [Finite ι] (v : ι → A)
    (hgen : Algebra.adjoin C (Set.range v) = ⊤) {q : ℕ} (hq : 2 ≤ q)
    (hv : ∀ i, v i ^ q ∈ span C (insert 1 (Set.range v))) : Module.Finite C A := by
  classical
  have := Fintype.ofFinite ι
  refine ⟨⟨Finset.univ.image fun e : ι → Fin q => ∏ i, v i ^ (e i : ℕ), ?_⟩⟩
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, eq_top_iff]
  rintro x -
  have hx : x ∈ Subalgebra.toSubmodule (Algebra.adjoin C (Set.range v)) := by
    rw [hgen]; trivial
  rw [Algebra.adjoin_eq_span] at hx
  refine span_le.mpr ?_ hx
  rintro _ hy
  obtain ⟨a, rfl⟩ := Submonoid.mem_closure_range_iff.mp hy
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  exact monomial_mem_span_of_pow_mem_span v hq hv a

end Finite

section Dimension

variable {C A : Type*} [CommRing C] [CommRing A] [Algebra C A]

/-- An integral extension has Krull dimension at most that of its base. -/
theorem ringKrullDim_le_of_isIntegral [Algebra.IsIntegral C A] :
    ringKrullDim A ≤ ringKrullDim C :=
  Order.krullDim_le_of_strictMono
    (fun P : PrimeSpectrum A => (⟨P.asIdeal.under C, inferInstance⟩ : PrimeSpectrum C))
    (fun _ _ h => Ideal.IsIntegral.under_lt_under (R := C) h)

/-- A finitely generated algebra over a field has finite Krull dimension. -/
theorem exists_ringKrullDim_eq_of_finiteType (k A : Type*) [Field k] [CommRing A] [Nontrivial A]
    [Algebra k A] [Algebra.FiniteType k A] : ∃ m : ℕ, ringKrullDim A = m := by
  obtain ⟨n, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType k A›
  have hle : ringKrullDim A ≤ n :=
    (ringKrullDim_le_of_surjective g.toRingHom hg).trans
      (by simp [ringKrullDim_eq_zero_of_field])
  have h0 : 0 ≤ ringKrullDim A := ringKrullDim_nonneg_of_nontrivial
  generalize ringKrullDim A = d at hle h0
  induction d using WithBot.recBotCoe with
  | bot => exact absurd h0 (by simp)
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      have : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast hle
      exact absurd (top_le_iff.mp (WithBot.coe_le_coe.mp this)).symm (ENat.top_ne_natCast n)
    | coe m => exact ⟨m, rfl⟩

/-- An algebra endomorphism of a finitely generated domain over a field is injective if the
domain is integral over its image. -/
theorem injective_of_isIntegral_range {k A : Type*} [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] (ψ : A →ₐ[k] A)
    [Algebra.IsIntegral ψ.range A] : Function.Injective ψ := by
  obtain ⟨m, hm⟩ := exists_ringKrullDim_eq_of_finiteType k A
  have h1 : ringKrullDim A ≤ ringKrullDim ψ.range := ringKrullDim_le_of_isIntegral
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hx0
  have h2 := ringKrullDim_succ_le_of_surjective (ψ.rangeRestrict : A →+* ψ.range)
    ψ.rangeRestrict_surjective (mem_nonZeroDivisors_of_ne_zero hx0)
    (Subtype.ext (by simpa using hx))
  have h3 := (add_le_add_left h1 1).trans h2
  rw [hm] at h3
  exact absurd h3 (by norm_cast; omega)

end Dimension

section Lift

/-- A ring map from the base of an injective integral extension to an algebraically closed field
extends to the extension. -/
theorem exists_lift_of_isIntegral {C A K : Type*} [CommRing C] [CommRing A] [Algebra C A]
    [Algebra.IsIntegral C A] (hinj : Function.Injective (algebraMap C A))
    [Field K] [IsAlgClosed K] (f : C →+* K) :
    ∃ g : A →+* K, g.comp (algebraMap C A) = f := by
  classical
  have := RingHom.ker_isPrime f
  obtain ⟨P, -, hP, hPp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker f)
    (⊥ : Ideal A) (by
      intro x hx
      have : algebraMap C A x = 0 := hx
      rw [hinj (this.trans (map_zero _).symm)]
      exact zero_mem _)
  have : P.LiesOver (RingHom.ker f) := ⟨hPp.symm⟩
  let : Algebra (C ⧸ RingHom.ker f) K := (RingHom.kerLift f).toAlgebra
  have : Module.IsTorsionFree (C ⧸ RingHom.ker f) (A ⧸ P) :=
    FaithfulSMul.to_isTorsionFree _ _
  have : Module.IsTorsionFree (C ⧸ RingHom.ker f) K :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr (RingHom.kerLift_injective f)
  have : Algebra.IsAlgebraic (C ⧸ RingHom.ker f) (A ⧸ P) := Algebra.IsIntegral.isAlgebraic
  let φ : (A ⧸ P) →ₐ[C ⧸ RingHom.ker f] K := IsAlgClosed.lift
  refine ⟨φ.toRingHom.comp (Ideal.Quotient.mk P), ?_⟩
  ext c
  have := φ.commutes (Ideal.Quotient.mk _ c)
  simpa [RingHom.algebraMap_toAlgebra] using this

/-- Let `ψ` be an algebra endomorphism of a finitely generated domain `A` over a field `k`, such
that `A` is integral over the image of `ψ`. Then every `k`-algebra map from `A` to an
algebraically closed field factors as `g ∘ ψ`. -/
theorem exists_comp_eq_of_isIntegral_range {k A K : Type*} [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] (ψ : A →ₐ[k] A) [Algebra.IsIntegral ψ.range A]
    [Field K] [IsAlgClosed K] [Algebra k K] (y : A →ₐ[k] K) :
    ∃ g : A →ₐ[k] K, g.comp ψ = y := by
  have hψ := injective_of_isIntegral_range ψ
  let e := AlgEquiv.ofInjective ψ hψ
  obtain ⟨g, hg⟩ := exists_lift_of_isIntegral (C := ψ.range) (A := A) Subtype.val_injective
    (y.toRingHom.comp e.symm.toRingHom)
  have hgψ : ∀ a, g (ψ a) = y a := by
    intro a
    have := congr($hg (e a))
    simpa [e] using this
  refine ⟨{ g with commutes' := fun c => by simpa using hgψ (algebraMap k A c) }, ?_⟩
  ext a
  exact hgψ a

end Lift

end Langlands.GroupScheme.FiniteFieldTorsorPoint
