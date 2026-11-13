import Langlands.AlgebraicGeometry.NoetherianApproximation.IntegerFiniteTypeNormalizationProof
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! # The normalization cover of a finite-type `ℤ`-algebra

For a commutative ring `R` and a prime `p`, let `(R ⧸ p)^ν` be the integral closure of
`R ⧸ p` in its fraction field. The morphism `∐_p Spec (R ⧸ p)^ν ⟶ Spec R`, over the minimal
primes `p` of `R`, is surjective, and finite when `R` is of finite type over `ℤ`. Each
`(R ⧸ p)^ν` is then an integrally closed domain of finite type over `ℤ`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.NoetherianApproximation.MinimalPrimeNormalization

/-- A finite product of finite ring maps out of a common source is finite. -/
theorem pi_ringHom_finite {R : Type u} [CommRing R] {ι : Type u} [Finite ι]
    {B : ι → Type u} [∀ i, CommRing (B i)] (f : ∀ i, R →+* B i) (hf : ∀ i, (f i).Finite) :
    (RingHom.pi f).Finite := by
  let _ : ∀ i, Algebra R (B i) := fun i ↦ (f i).toAlgebra
  have : ∀ i, Module.Finite R (B i) := hf
  change (algebraMap R (∀ i, B i)).Finite
  rw [RingHom.finite_algebraMap]
  infer_instance

variable (R : Type u) [CommRing R]

/-- The normalization of `R ⧸ p`: the integral closure of `R ⧸ p` in its fraction field. -/
abbrev Normalization (p : Ideal R) : Type u :=
  integralClosure (R ⧸ p) (FractionRing (R ⧸ p))

/-- The composite `R ⟶ R ⧸ p ⟶ (R ⧸ p)^ν`. -/
def toNormalization (p : Ideal R) : R →+* Normalization R p :=
  (algebraMap (R ⧸ p) (Normalization R p)).comp (Ideal.Quotient.mk p)

/-- The normalization cover `∐_p Spec (R ⧸ p)^ν ⟶ Spec R` over the minimal primes `p`. -/
def cover : (∐ fun p : minimalPrimes R ↦ Spec (CommRingCat.of (Normalization R p.1))) ⟶
    Spec (CommRingCat.of R) :=
  Sigma.desc fun p ↦ Spec.map (CommRingCat.ofHom (toNormalization R p.1))

@[reassoc (attr := simp)]
lemma ι_cover (p : minimalPrimes R) :
    Sigma.ι (fun p : minimalPrimes R ↦ Spec (CommRingCat.of (Normalization R p.1))) p ≫
      cover R = Spec.map (CommRingCat.ofHom (toNormalization R p.1)) :=
  Sigma.ι_comp_desc _ _

variable {R}

section Prime

variable (p : Ideal R) [p.IsPrime]

instance : IsIntegrallyClosed (Normalization R p) :=
  integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing (R ⧸ p))

/-- For `R` of finite type over `ℤ`, the map `R ⟶ (R ⧸ p)^ν` is finite. -/
theorem toNormalization_finite [Algebra.FiniteType ℤ R] : (toNormalization R p).Finite := by
  have hft : Algebra.FiniteType ℤ (R ⧸ p) := by
    rw [← RingHom.finiteType_algebraMap]
    have h : algebraMap ℤ (R ⧸ p) = (Ideal.Quotient.mk p).comp (algebraMap ℤ R) :=
      RingHom.ext_int _ _
    rw [h]
    exact (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective).comp
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  have := @integerFiniteTypeNormalization (R ⧸ p) _ _ (by convert hft; exact Subsingleton.elim _ _)
  exact (RingHom.finite_algebraMap.mpr this).comp
    (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective)

theorem normalization_finiteType [Algebra.FiniteType ℤ R] :
    Algebra.FiniteType ℤ (Normalization R p) := by
  rw [← RingHom.finiteType_algebraMap]
  have h : algebraMap ℤ (Normalization R p) = (toNormalization R p).comp (algebraMap ℤ R) :=
    RingHom.ext_int _ _
  rw [h]
  exact (toNormalization_finite p).to_finiteType.comp
    (RingHom.finiteType_algebraMap.mpr inferInstance)

/-- `(R ⧸ p)^ν` is of finite type over `ℤ` for the canonical `ℤ`-algebra structure. -/
instance [Algebra.FiniteType ℤ R] :
    @Algebra.FiniteType ℤ (Normalization R p) _ _ (Ring.toIntAlgebra _) := by
  convert normalization_finiteType p <;> exact Subsingleton.elim _ _

omit [p.IsPrime] in
/-- Every prime containing `p` is the contraction of a prime of `(R ⧸ p)^ν`. -/
theorem exists_comap_toNormalization_eq (q : Ideal R) [q.IsPrime] (hpq : p ≤ q) :
    ∃ Q : Ideal (Normalization R p), Q.IsPrime ∧ Q.comap (toNormalization R p) = q := by
  let P : Ideal (R ⧸ p) := q.map (Ideal.Quotient.mk p)
  have hP : P.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rwa [Ideal.mk_ker])
  have hbot : (⊥ : Ideal (Normalization R p)).under (R ⧸ p) ≤ P := by
    intro x hx
    have h0 : algebraMap (R ⧸ p) (FractionRing (R ⧸ p)) x = 0 :=
      congrArg Subtype.val (Ideal.mem_bot.mp (Ideal.mem_comap.mp hx))
    have hx0 : x = 0 :=
      IsFractionRing.injective (R ⧸ p) (FractionRing (R ⧸ p)) (h0.trans (map_zero _).symm)
    exact hx0 ▸ P.zero_mem
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P _ hbot
  refine ⟨Q, hQ, ?_⟩
  rw [toNormalization, ← Ideal.comap_comap]
  change (Q.under (R ⧸ p)).comap _ = q
  rw [hQP, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hpq]

end Prime

variable (R)

/-- The normalization cover is surjective. -/
theorem cover_surjective : Surjective (cover R) := by
  constructor
  intro x
  have := x.isPrime
  obtain ⟨p, hp, hpx⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := x.asIdeal) bot_le
  have : p.IsPrime := hp.1.1
  obtain ⟨Q, hQ, hQx⟩ := exists_comap_toNormalization_eq p x.asIdeal hpx
  let y : Spec (CommRingCat.of (Normalization R p)) := (⟨Q, hQ⟩ : PrimeSpectrum _)
  refine ⟨Sigma.ι (fun p : minimalPrimes R ↦ Spec (CommRingCat.of (Normalization R p.1)))
    ⟨p, hp⟩ y, ?_⟩
  rw [← Scheme.Hom.comp_apply, ι_cover, Spec.map_apply]
  exact PrimeSpectrum.ext hQx

/-- For `R` of finite type over `ℤ`, the minimal primes are finite in number. -/
instance [Algebra.FiniteType ℤ R] : Finite (minimalPrimes R) :=
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  (minimalPrimes.finite_of_isNoetherianRing R).to_subtype

/-- For `R` of finite type over `ℤ`, the normalization cover is finite. -/
theorem cover_isFinite [Algebra.FiniteType ℤ R] : IsFinite (cover R) := by
  let B : minimalPrimes R → CommRingCat.{u} := fun p ↦ CommRingCat.of (Normalization R p.1)
  let Φ : R →+* ((p : minimalPrimes R) → Normalization R p.1) :=
    RingHom.pi fun p ↦ toNormalization R p.1
  have hcover : cover R = sigmaSpec B ≫ Spec.map (CommRingCat.ofHom Φ) := by
    refine Sigma.hom_ext _ _ fun p ↦ ?_
    rw [ι_cover, ι_sigmaSpec_assoc, ← Spec.map_comp]
    rfl
  have : IsFinite (Spec.map (CommRingCat.ofHom Φ)) := by
    rw [IsFinite.SpecMap_iff]
    exact pi_ringHom_finite _ fun p ↦
      have : p.1.IsPrime := p.2.1.1
      toNormalization_finite p.1
  rw [hcover]
  infer_instance

end Langlands.AlgebraicGeometry.NoetherianApproximation.MinimalPrimeNormalization
