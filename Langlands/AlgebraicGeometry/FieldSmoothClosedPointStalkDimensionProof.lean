import Langlands.AlgebraicGeometry.FieldSmoothClosedPointStalkDimensionGeometry
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.Smooth.Flat

/-! # Stalk dimension at closed points of smooth schemes over fields

The algebraic calculation uses an étale map from a polynomial ring, preservation
of prime height under flat quasi-finite maps, and maximal heights in polynomial rings.
-/

universe u v

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Going-down and quasi-finite incomparability preserve prime height. -/
private lemma height_eq_under_of_flat_quasiFinite
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] [Algebra.QuasiFinite R S] (P : Ideal S) [P.IsPrime] :
    P.height = (P.under R).height := by
  have hstrict : StrictMono (PrimeSpectrum.comap (algebraMap R S)) := by
    intro p q hpq
    change p.asIdeal.under R < q.asIdeal.under R
    refine lt_of_le_of_ne (Ideal.comap_mono hpq.le) ?_
    intro heq
    exact hpq.ne (PrimeSpectrum.ext
      (Algebra.QuasiFinite.eq_of_le_of_under_eq p.asIdeal q.asIdeal hpq.le heq))
  have hlift : ∀ (p : PrimeSpectrum S) (q : PrimeSpectrum R),
      q < PrimeSpectrum.comap (algebraMap R S) p →
        ∃ p' < p, PrimeSpectrum.comap (algebraMap R S) p' = q := by
    intro p q hq
    obtain ⟨P', hP', hprime, hlo⟩ :=
      Ideal.exists_ideal_lt_liesOver_of_lt p.asIdeal (p := q.asIdeal) hq
    exact ⟨⟨P', hprime⟩, hP', PrimeSpectrum.ext hlo.over.symm⟩
  simpa only [← PrimeSpectrum.height_eq_orderHeight, PrimeSpectrum.comap_asIdeal] using
    Order.height_eq_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
      hstrict hlift ⟨P, inferInstance⟩

/-- Every maximal ideal of affine `n`-space over a field has height `n`. -/
private lemma maximal_height_mvPolynomial (k : Type u) [Field k] (n : ℕ)
    (P : Ideal (MvPolynomial (Fin n) k)) [P.IsMaximal] :
    P.height = (n : ℕ∞) := by
  induction n with
  | zero =>
    let e : MvPolynomial (Fin 0) k ≃+* k := MvPolynomial.isEmptyRingEquiv _ _
    rw [← e.height_map P]
    have : P.map e = ⊥ := Ideal.eq_bot_of_prime (P.map e)
    simp [this]
  | succ n ih =>
    let e := (MvPolynomial.finSuccEquiv k n).toRingEquiv
    let Q := P.map e
    have : Q.IsMaximal := Ideal.map_isMaximal_of_equiv e
    have : (Q.under (MvPolynomial (Fin n) k)).IsMaximal :=
      Polynomial.isMaximal_comap_C_of_isJacobsonRing Q
    calc
      P.height = Q.height := (e.height_map P).symm
      _ = (Q.under (MvPolynomial (Fin n) k)).height + 1 :=
        Polynomial.height_eq_height_add_one _ _
      _ = (n + 1 : ℕ) := by rw [ih]; simp

/-- Finite-type maps out of Jacobson rings contract maximal ideals to maximal ideals. -/
private lemma maximal_under_of_finiteType (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S] [IsJacobsonRing R]
    [Algebra.FiniteType R S] (P : Ideal S) [P.IsMaximal] :
    (P.under R).IsMaximal := by
  let : Field (S ⧸ P) := Ideal.Quotient.field P
  have : Module.Finite R (S ⧸ P) := finite_of_finite_type_of_isJacobsonRing R (S ⧸ P)
  have h := Ideal.isMaximal_under_of_isIntegral_of_isMaximal
    (R := R) (⊥ : Ideal (S ⧸ P))
  change (Ideal.comap (algebraMap R (S ⧸ P)) ⊥).IsMaximal at h
  rw [IsScalarTower.algebraMap_eq R S (S ⧸ P), ← Ideal.comap_comap] at h
  change ((RingHom.ker (Ideal.Quotient.mk P)).comap (algebraMap R S)).IsMaximal at h
  simpa only [Ideal.mk_ker] using h

/-- A maximal ideal in a standard-smooth algebra has the prescribed relative height. -/
private lemma maximal_height_standardSmooth (k : Type u) (S : Type v)
    [Field k] [CommRing S] [Algebra k S] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n k S]
    (P : Ideal S) [P.IsMaximal] : P.height = (n : ℕ∞) := by
  obtain ⟨φ, hφ⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial n k S
  let : Algebra (MvPolynomial (Fin n) k) S := φ.toRingHom.toAlgebra
  have : Algebra.Etale (MvPolynomial (Fin n) k) S :=
    (RingHom.etale_algebraMap).mp hφ
  have : (P.under (MvPolynomial (Fin n) k)).IsMaximal :=
    maximal_under_of_finiteType (MvPolynomial (Fin n) k) S P
  rw [height_eq_under_of_flat_quasiFinite (MvPolynomial (Fin n) k) S P]
  exact maximal_height_mvPolynomial k n _

/-- At every closed point of a scheme smooth of relative dimension `g` over a field,
the actual stalk has Krull dimension `g`. -/
theorem fieldSmoothClosedPointStalkDimension :
    FieldSmoothClosedPointStalkDimensionStatement.{u} :=
  fieldSmoothClosedPointStalkDimension_of_maximalHeight
    (fun k S _ _ _ n _ P _ => maximal_height_standardSmooth k S n P)

end Langlands.AlgebraicGeometry
