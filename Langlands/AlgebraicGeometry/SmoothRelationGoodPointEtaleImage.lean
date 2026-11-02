import Langlands.AlgebraicGeometry.SmoothRelationGoodPointOpenImage

/-! # Open spectral images from localized flat algebras -/

noncomputable section

universe u v w

namespace Langlands.AlgebraicGeometry.SmoothRelationGoodPoint

/-- A flat, finitely presented algebra structure on a localization makes the
image of every open subset of its principal open neighborhood open. -/
lemma isOpen_comap_image_of_flat_finitePresentation_away
    {S B : Type*} [CommRing S] [CommRing B] [Algebra S B]
    (c : B) (C : Type*) [CommRing C] [Algebra B C] [Algebra S C]
    [IsScalarTower S B C] [IsLocalization.Away c C]
    [Module.Flat S C] [Algebra.FinitePresentation S C]
    (O : Set (PrimeSpectrum B)) (hO : IsOpen O)
    (hOc : O ⊆ PrimeSpectrum.basicOpen c) :
    IsOpen (PrimeSpectrum.comap (algebraMap S B) '' O) := by
  have : Algebra.HasGoingDown S C := Algebra.HasGoingDown.of_flat
  have hopen := PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
    (R := S) (S := C) _ (hO.preimage (PrimeSpectrum.continuous_comap (algebraMap B C)))
  rw [IsScalarTower.algebraMap_eq S B C, PrimeSpectrum.comap_comp,
    Set.image_comp, Set.image_preimage_eq_inter_range,
    PrimeSpectrum.localization_away_comap_range C c, Set.inter_eq_left.mpr hOc] at hopen
  exact hopen

/-- In an open subset of an etale coordinate neighborhood, preserve the base
prime and choose simple integer equations for all polynomial coordinates. -/
lemma exists_prime_simpleIntegerRoots_of_etale_away
    {A : Type u} {B : Type v} {ι : Type w} [CommRing A] [CommRing B]
    [Algebra (MvPolynomial ι A) B] (c : B)
    [Algebra.Etale (MvPolynomial ι A) (Localization.Away c)]
    (O : Set (PrimeSpectrum B)) (hO : IsOpen O)
    (hOc : O ⊆ PrimeSpectrum.basicOpen c)
    (q : PrimeSpectrum B) (hq : q ∈ O) :
    ∃ r : PrimeSpectrum B, r ∈ O ∧
      r.asIdeal.comap ((algebraMap (MvPolynomial ι A) B).comp MvPolynomial.C) =
        q.asIdeal.comap ((algebraMap (MvPolynomial ι A) B).comp MvPolynomial.C) ∧
      ∀ i : ι, ∃ P : Polynomial ℤ,
        Polynomial.aeval (algebraMap (MvPolynomial ι A) B (MvPolynomial.X i)) P
          ∈ r.asIdeal ∧
        Polynomial.aeval (algebraMap (MvPolynomial ι A) B (MvPolynomial.X i)) P.derivative
          ∉ r.asIdeal :=
  exists_prime_simpleIntegerRoots_of_openImage _ O
    (isOpen_comap_image_of_flat_finitePresentation_away c (Localization.Away c) O hO hOc) q hq

/-- The actual prime and simple-root data chosen in an open subset of an
etale polynomial coordinate neighborhood. -/
def simpleIntegerRootEtaleAway
    {A : Type u} {B : Type v} {ι : Type w} [CommRing A] [CommRing B]
    [Algebra (MvPolynomial ι A) B] (c : B)
    [Algebra.Etale (MvPolynomial ι A) (Localization.Away c)]
    (O : Set (PrimeSpectrum B)) (hO : IsOpen O)
    (hOc : O ⊆ PrimeSpectrum.basicOpen c)
    (q : PrimeSpectrum B) (hq : q ∈ O) :
    SimpleIntegerRootOpenImageData (algebraMap (MvPolynomial ι A) B) O q :=
  simpleIntegerRootOpenImage _ O
    (isOpen_comap_image_of_flat_finitePresentation_away c (Localization.Away c) O hO hOc) q hq

end Langlands.AlgebraicGeometry.SmoothRelationGoodPoint
