import Langlands.AlgebraicGeometry.SmoothRelationGoodPointChoice

/-! # Lifting simple integer coordinates through an open spectral image -/

noncomputable section

universe u v w

open Polynomial

namespace Langlands.AlgebraicGeometry.SmoothRelationGoodPoint

variable {A : Type u} {B : Type v} {ι : Type w} [CommRing A] [CommRing B]

/-- In an open spectral image, one can preserve the base prime while making
all polynomial coordinates simple roots of integer polynomials. -/
lemma exists_prime_simpleIntegerRoots_of_openImage
    (Φ : MvPolynomial ι A →+* B) (O : Set (PrimeSpectrum B))
    (hO : IsOpen (PrimeSpectrum.comap Φ '' O))
    (q : PrimeSpectrum B) (hq : q ∈ O) :
    ∃ r : PrimeSpectrum B, r ∈ O ∧
      r.asIdeal.comap (Φ.comp MvPolynomial.C) =
        q.asIdeal.comap (Φ.comp MvPolynomial.C) ∧
      ∀ i : ι, ∃ P : Polynomial ℤ,
        aeval (Φ (MvPolynomial.X i)) P ∈ r.asIdeal ∧
        aeval (Φ (MvPolynomial.X i)) P.derivative ∉ r.asIdeal := by
  obtain ⟨_, ⟨h, rfl⟩, hh, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (Set.mem_image_of_mem (PrimeSpectrum.comap Φ) hq) hO
  obtain ⟨a, hha, hbase, hcoord⟩ :=
    exists_prime_simpleIntegerRoots (PrimeSpectrum.comap Φ q) h hh
  obtain ⟨r, hr, heq⟩ := hsub hha
  refine ⟨r, hr, ?_, ?_⟩
  · change (PrimeSpectrum.comap Φ r).asIdeal.comap MvPolynomial.C =
      (PrimeSpectrum.comap Φ q).asIdeal.comap MvPolynomial.C
    rw [heq]
    exact hbase
  · have hΦ (i : ι) (P : Polynomial ℤ) :
        Φ (aeval (MvPolynomial.X i) P) = aeval (Φ (MvPolynomial.X i)) P := by
      simpa only [Polynomial.map_id] using
        (Polynomial.map_aeval_eq_aeval_map (φ := RingHom.id ℤ) (ψ := Φ)
          (by ext z; simp) P (MvPolynomial.X i))
    intro i
    obtain ⟨P, hP, hdP⟩ := hcoord i
    refine ⟨P, ?_, ?_⟩
    · rw [← hΦ]
      change aeval (MvPolynomial.X i) P ∈ (PrimeSpectrum.comap Φ r).asIdeal
      rw [heq]
      exact hP
    · rw [← hΦ]
      change aeval (MvPolynomial.X i) P.derivative ∉ (PrimeSpectrum.comap Φ r).asIdeal
      rw [heq]
      exact hdP

/-- A chosen prime in a prescribed spectral subset with the same base
contraction and simple integer equations for all coordinate images. -/
structure SimpleIntegerRootOpenImageData
    (Φ : MvPolynomial ι A →+* B) (O : Set (PrimeSpectrum B)) (q : PrimeSpectrum B) where
  prime : PrimeSpectrum B
  mem : prime ∈ O
  comap_eq : prime.asIdeal.comap (Φ.comp MvPolynomial.C) =
    q.asIdeal.comap (Φ.comp MvPolynomial.C)
  coordinate : ∀ i : ι, ∃ P : Polynomial ℤ,
    aeval (Φ (MvPolynomial.X i)) P ∈ prime.asIdeal ∧
    aeval (Φ (MvPolynomial.X i)) P.derivative ∉ prime.asIdeal

/-- Choose a prime with simple integer coordinates in a subset with open spectral image. -/
def simpleIntegerRootOpenImage
    (Φ : MvPolynomial ι A →+* B) (O : Set (PrimeSpectrum B))
    (hO : IsOpen (PrimeSpectrum.comap Φ '' O))
    (q : PrimeSpectrum B) (hq : q ∈ O) : SimpleIntegerRootOpenImageData Φ O q :=
  Classical.choice (by
    obtain ⟨r, hr, hbase, hcoord⟩ :=
      exists_prime_simpleIntegerRoots_of_openImage Φ O hO q hq
    exact ⟨⟨r, hr, hbase, hcoord⟩⟩)

end Langlands.AlgebraicGeometry.SmoothRelationGoodPoint
