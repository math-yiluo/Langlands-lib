import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.NumberTheory.NumberField.ExistsRamified
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Unramified.Field

/-! # Finite étale algebras over `ℤ` have trivial Picard groups -/

universe u v w

open scoped TensorProduct

namespace Langlands.Algebra

/-- Every module-finite étale `R`-algebra (in universe `v`) has trivial Picard group. -/
def FiniteEtaleAlgebrasHaveTrivialPicard (R : Type u) [CommRing R] : Prop :=
  ∀ (R' : Type v) [CommRing R'] [Algebra R R'], Algebra.Etale R R' → Module.Finite R R' →
    Subsingleton (CommRing.Pic R')

/-- Trivial Picard groups transfer along ring isomorphisms. -/
theorem subsingleton_pic_of_ringEquiv {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) [Subsingleton (CommRing.Pic S)] : Subsingleton (CommRing.Pic R) := by
  have h : Function.LeftInverse (CommRing.Pic.mapRingHom (e.symm : S →+* R))
      (CommRing.Pic.mapRingHom (e : R →+* S)) := fun M => by
    rw [CommRing.Pic.mapRingHom_mapRingHom, RingEquiv.symm_comp,
      CommRing.Pic.mapRingHom_id_apply]
  exact h.injective.subsingleton

/-- If the structure map of `R` into a finite product of `R`-algebras with trivial Picard
groups is bijective, then `R` has trivial Picard group. -/
theorem subsingleton_pic_of_bijective_algebraMap_pi {R : Type u} [CommRing R] {ι : Type w}
    [Finite ι] (B : ι → Type v) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    [∀ i, Subsingleton (CommRing.Pic (B i))]
    (h : Function.Bijective (algebraMap R (∀ i, B i))) : Subsingleton (CommRing.Pic R) := by
  classical
  have := Fintype.ofFinite ι
  rw [CommRing.Pic.subsingleton_iff]
  intro M _ _ _
  let e₀ : R ≃ₗ[R] (∀ i, B i) := LinearEquiv.ofBijective (Algebra.linearMap R (∀ i, B i)) h
  have hfree : ∀ i, Nonempty ((B i ⊗[R] M) ≃ₗ[B i] B i) := fun i =>
    Module.Invertible.free_iff_linearEquiv.mp inferInstance
  let f : ∀ i, (B i ⊗[R] M) ≃ₗ[R] B i := fun i => (hfree i).some.restrictScalars R
  let e : M ≃ₗ[R] R :=
    (TensorProduct.lid R M).symm ≪≫ₗ e₀.rTensor M ≪≫ₗ TensorProduct.piLeft R M B ≪≫ₗ
      LinearEquiv.piCongrRight f ≪≫ₗ e₀.symm
  exact Module.Invertible.free_iff_linearEquiv.mpr ⟨e⟩

section Integer

variable (A : Type u) [CommRing A]

/-- A flat `ℤ`-algebra embeds into its rationalization `ℚ ⊗[ℤ] A`. -/
theorem injective_includeRight_rat [Module.Flat ℤ A] :
    Function.Injective
      (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := A)) := by
  have : ⇑(Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := A)) =
      (LinearMap.rTensor A (Algebra.ofId ℤ ℚ).toLinearMap).comp
        (Algebra.TensorProduct.lid ℤ A).symm.toLinearMap := by
    ext x; simp
  rw [this, LinearMap.coe_comp]
  exact (Module.Flat.rTensor_preserves_injective_linearMap _
    (algebraMap ℤ ℚ).injective_int).comp (Algebra.TensorProduct.lid ℤ A).symm.injective

variable [Algebra.Etale ℤ A]

/-- An étale `ℤ`-algebra is reduced. -/
theorem isReduced_of_etale_int : IsReduced A := by
  have := Algebra.FormallyUnramified.isReduced_of_field ℚ (ℚ ⊗[ℤ] A)
  exact isReduced_of_injective _ (injective_includeRight_rat A)

/-- Nonzero integers are non-zero-divisors in an étale `ℤ`-algebra. -/
theorem intCast_mem_nonZeroDivisors {n : ℤ} (hn : n ≠ 0) : (n : A) ∈ nonZeroDivisors A := by
  rw [mem_nonZeroDivisors_iff_right]
  intro y hy
  apply injective_includeRight_rat A
  have hu : IsUnit (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := A) (n : A)) := by
    rw [map_intCast, ← map_intCast (algebraMap ℚ (ℚ ⊗[ℤ] A))]
    exact (isUnit_iff_ne_zero.mpr (by exact_mod_cast hn)).map _
  have := congrArg (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := A)) hy
  rw [map_mul, map_zero] at this
  rw [map_zero]
  exact hu.mul_left_eq_zero.mp this

variable [Module.Finite ℤ A]

/-- A characteristic-zero domain that is a quotient of a module-finite étale `ℤ`-algebra is
`ℤ` (Hermite–Minkowski, via Mathlib). -/
theorem bijective_intCast_of_surjective {B : Type v} [CommRing B] [IsDomain B] [CharZero B]
    (f : A →+* B) (hf : Function.Surjective f) : Function.Bijective (Int.castRingHom B) := by
  have : Module.Finite ℤ B := Module.Finite.of_surjective f.toIntAlgHom.toLinearMap hf
  have : Algebra.FormallyUnramified ℤ B :=
    Algebra.FormallyUnramified.of_surjective f.toIntAlgHom hf
  have : Algebra.Unramified ℤ B := {}
  have : FaithfulSMul ℤ B := by
    rw [faithfulSMul_iff_algebraMap_injective]
    exact Int.cast_injective
  exact bijective_algebraMap_int_of_finite_of_unramified

/-- The quotient of a module-finite étale `ℤ`-algebra by a minimal prime is `ℤ`. -/
theorem bijective_intCast_quotient_minimalPrime {p : Ideal A} (hp : p ∈ minimalPrimes A) :
    Function.Bijective (Int.castRingHom (A ⧸ p)) := by
  have : p.IsPrime := hp.1.1
  have : CharZero (A ⧸ p) := by
    refine charZero_of_inj_zero fun n hn => ?_
    by_contra hn0
    rw [← map_natCast (Ideal.Quotient.mk p), Ideal.Quotient.eq_zero_iff_mem] at hn
    have := intCast_mem_nonZeroDivisors A (n := (n : ℤ)) (by exact_mod_cast hn0)
    rw [Int.cast_natCast] at this
    exact Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hp) hn this
  exact bijective_intCast_of_surjective A (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective

/-- The `ℤ`-point of a module-finite étale `ℤ`-algebra cut out by a minimal prime. -/
noncomputable def minimalPrimePoint {p : Ideal A} (hp : p ∈ minimalPrimes A) : A →+* ℤ :=
  (RingEquiv.ofBijective (Int.castRingHom (A ⧸ p))
    (bijective_intCast_quotient_minimalPrime A hp)).symm.toRingHom.comp
    (Ideal.Quotient.mk p)

theorem intCast_minimalPrimePoint {p : Ideal A} (hp : p ∈ minimalPrimes A) (x : A) :
    Ideal.Quotient.mk p ((minimalPrimePoint A hp x : ℤ) : A) = Ideal.Quotient.mk p x := by
  rw [map_intCast]
  exact (RingEquiv.ofBijective (Int.castRingHom (A ⧸ p))
    (bijective_intCast_quotient_minimalPrime A hp)).apply_symm_apply _

theorem ker_minimalPrimePoint {p : Ideal A} (hp : p ∈ minimalPrimes A) :
    RingHom.ker (minimalPrimePoint A hp) = p := by
  ext x
  rw [RingHom.mem_ker, minimalPrimePoint, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, map_eq_zero_iff _ (RingEquiv.injective _),
    Ideal.Quotient.eq_zero_iff_mem]

/-- Distinct minimal primes of a module-finite étale `ℤ`-algebra are comaximal. -/
theorem isCoprime_of_mem_minimalPrimes {p q : Ideal A} (hp : p ∈ minimalPrimes A)
    (hq : q ∈ minimalPrimes A) (hpq : p ≠ q) : IsCoprime p q := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  let J : Ideal ℤ := (p ⊔ q).comap (Int.castRingHom A)
  have hJ : J ≠ ⊤ := Ideal.comap_ne_top _ hne
  have hdiff : ∀ x, minimalPrimePoint A hp x - minimalPrimePoint A hq x ∈ J := by
    intro x
    have h₁ : x - ((minimalPrimePoint A hp x : ℤ) : A) ∈ p := by
      rw [← Ideal.Quotient.eq, intCast_minimalPrimePoint]
    have h₂ : x - ((minimalPrimePoint A hq x : ℤ) : A) ∈ q := by
      rw [← Ideal.Quotient.eq, intCast_minimalPrimePoint]
    have : (((minimalPrimePoint A hp x - minimalPrimePoint A hq x : ℤ)) : A) =
        (x - ((minimalPrimePoint A hq x : ℤ) : A)) -
          (x - ((minimalPrimePoint A hp x : ℤ) : A)) := by
      push_cast; ring
    show (((minimalPrimePoint A hp x - minimalPrimePoint A hq x : ℤ)) : A) ∈ p ⊔ q
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mem_sup_right h₂) (Ideal.mem_sup_left h₁)
  have heq : (minimalPrimePoint A hp).toIntAlgHom = (minimalPrimePoint A hq).toIntAlgHom :=
    Algebra.FormallyUnramified.ext_of_iInf J (Ideal.iInf_pow_eq_bot_of_isDomain J hJ)
      fun x => (Ideal.Quotient.eq).mpr (hdiff x)
  apply hpq
  rw [← ker_minimalPrimePoint A hp, ← ker_minimalPrimePoint A hq]
  congr 1
  exact RingHom.ext fun x => AlgHom.congr_fun heq x

/-- **Finite étale `ℤ`-algebras have trivial Picard group.** A module-finite étale algebra
over `ℤ` is the product of its quotients by its finitely many minimal primes, each of which
is `ℤ`, so its Picard group is trivial. -/
theorem subsingleton_pic_of_etale_int : Subsingleton (CommRing.Pic A) := by
  have hred := isReduced_of_etale_int A
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  let ι := minimalPrimes A
  have : Finite ι := (minimalPrimes.finite_of_isNoetherianRing A).to_subtype
  have hZ : ∀ p : ι, Subsingleton (CommRing.Pic (A ⧸ p.1)) := fun p =>
    subsingleton_pic_of_ringEquiv (RingEquiv.ofBijective (Int.castRingHom (A ⧸ p.1))
      (bijective_intCast_quotient_minimalPrime A p.2)).symm
  have hbot : sInf (minimalPrimes A) = ⊥ := by
    rw [minimalPrimes, Ideal.sInf_minimalPrimes, Ideal.radical_bot_of_isReduced]
  refine subsingleton_pic_of_bijective_algebraMap_pi (fun p : ι => A ⧸ p.1) ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have hmem : x ∈ sInf (minimalPrimes A) := by
      rw [Submodule.mem_sInf]
      intro p hp
      have := congrFun hx ⟨p, hp⟩
      rwa [Pi.algebraMap_apply, Pi.zero_apply, Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem] at this
    rw [hbot] at hmem
    exact (Submodule.mem_bot _).mp hmem
  · intro y
    obtain ⟨r, hr⟩ := Ideal.pi_quotient_surjective (I := fun p : ι => p.1)
      (fun p q hpq => isCoprime_of_mem_minimalPrimes A p.2 q.2
        (fun h => hpq (Subtype.ext h))) y
    exact ⟨r, funext fun p => hr p⟩

end Integer

/-- **Clause-2 Picard input.** Over a ring isomorphic to `ℤ`, every module-finite étale
algebra has trivial Picard group. -/
theorem finiteEtaleAlgebrasHaveTrivialPicard_of_ringEquiv_int (R : Type u) [CommRing R]
    (h : Nonempty (R ≃+* ℤ)) : FiniteEtaleAlgebrasHaveTrivialPicard.{u, v} R := by
  intro R' _ _ hét hfin
  obtain ⟨e⟩ := h
  have hbij : Function.Bijective (algebraMap ℤ R) := by
    have : algebraMap ℤ R = (e.symm : ℤ →+* R) := RingHom.ext_int _ _
    rw [this]
    exact e.symm.bijective
  let eZ : ℤ ≃ₐ[ℤ] R := AlgEquiv.ofBijective (Algebra.ofId ℤ R) hbij
  have : Algebra.Etale ℤ R := Algebra.Etale.of_equiv eZ
  have : Module.Finite ℤ R := Module.Finite.equiv eZ.toLinearEquiv
  have : Algebra.Etale ℤ R' := Algebra.Etale.comp ℤ R R'
  have : Module.Finite ℤ R' := Module.Finite.trans R R'
  exact subsingleton_pic_of_etale_int R'

end Langlands.Algebra
