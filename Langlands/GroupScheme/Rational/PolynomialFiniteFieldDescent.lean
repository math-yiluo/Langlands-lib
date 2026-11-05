import Langlands.GroupScheme.Rational.PolynomialNormInput
import Langlands.GroupScheme.Torus.CocharacterDatum
import Langlands.GroupScheme.AffineCoordinatesFiniteType
import Mathlib.FieldTheory.Galois.GaloisClosure

/-! # Finite fields of definition of actual additive polynomial points -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.PolynomialPoint

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Extension of coefficients of an actual polynomial point. -/
def mapCoefficients {A D : Type u} [CommRing A] [Algebra k A]
    [CommRing D] [Algebra k D] {I : Type} (f : A →ₐ[k] D) :
    Lie.AffinePoints G (MvPolynomial I A) →*
      Lie.AffinePoints G (MvPolynomial I D) :=
  Lie.affineMap G (MvPolynomial.mapAlgHom f)

theorem mapCoefficients_comp {A D E : Type u}
    [CommRing A] [Algebra k A] [CommRing D] [Algebra k D]
    [CommRing E] [Algebra k E] {I : Type}
    (f : A →ₐ[k] D) (g : D →ₐ[k] E)
    (x : Lie.AffinePoints G (MvPolynomial I A)) :
    mapCoefficients g (mapCoefficients f x) = mapCoefficients (g.comp f) x := by
  change Lie.affineMap G (MvPolynomial.mapAlgHom g)
      (Lie.affineMap G (MvPolynomial.mapAlgHom f) x) =
    Lie.affineMap G (MvPolynomial.mapAlgHom (g.comp f)) x
  rw [← Lie.affineMap_comp]
  have h : (MvPolynomial.mapAlgHom (σ := I) g).comp (MvPolynomial.mapAlgHom f) =
      MvPolynomial.mapAlgHom (g.comp f) := by
    apply AlgHom.ext
    intro p
    exact MvPolynomial.map_map f.toRingHom g.toRingHom p
  rw [h]

section FiniteModel

open CocharacterDatum

variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    {L : Type u} [Field L] [Algebra k L] {I : Type}

/-- An actual polynomial point over an algebraic field extension has a finite
field of definition, with the original point recovered after coefficient extension. -/
theorem exists_finiteDimensional_mapCoefficients_eq [Algebra.IsAlgebraic k L]
    (x : Lie.AffinePoints G (MvPolynomial I L)) :
    ∃ E : IntermediateField k L, FiniteDimensional k E ∧
      ∃ y : Lie.AffinePoints G (MvPolynomial I E),
        mapCoefficients E.val y = x := by
  classical
  obtain ⟨s, hs⟩ := (AffineCoordinates.algebraFiniteType G).out
  let T : Finset L := s.biUnion fun c => ((coord x).hom c).coeff.frange
  let E : IntermediateField k L := IntermediateField.adjoin k (T : Set L)
  have hE : FiniteDimensional k E :=
    IntermediateField.finiteDimensional_adjoin fun c _ => Algebra.IsIntegral.isIntegral c
  let f : E →ₐ[k] L := E.val
  have hgen : ∀ c ∈ s, (coord x).hom c ∈ (MvPolynomial.mapAlgHom f).range := by
    intro c hc
    change (coord x).hom c ∈ Set.range (MvPolynomial.map f.toRingHom)
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro a ha
    obtain ⟨m, hm, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp ha
    refine ⟨⟨_, IntermediateField.subset_adjoin k _ ?_⟩, rfl⟩
    exact Finset.mem_biUnion.mpr
      ⟨c, hc, Finsupp.mem_frange.mpr ⟨Finsupp.mem_support_iff.mp hm, m, rfl⟩⟩
  have hall : ∀ c, (coord x).hom c ∈ (MvPolynomial.mapAlgHom f).range := by
    intro c
    have hc : c ∈ Algebra.adjoin (CommRingCat.of k)
        (s : Set (AffineCoordinates.algebra G)) := by
      rw [hs]
      trivial
    induction hc using Algebra.adjoin_induction with
    | mem c hc => exact hgen c hc
    | algebraMap r =>
      rw [AlgHom.commutes]
      exact Subalgebra.algebraMap_mem _ (r : k)
    | add a b _ _ ha hb =>
      rw [map_add]
      exact add_mem ha hb
    | mul a b _ _ ha hb =>
      rw [map_mul]
      exact mul_mem ha hb
  obtain ⟨y, hy⟩ := exists_affineMap_eq (MvPolynomial.mapAlgHom f)
    (MvPolynomial.map_injective _ Subtype.val_injective) x hall
  exact ⟨E, hE, y, hy⟩

/-- The exact polynomial point over a Galois extension has a finite Galois
field of definition. -/
theorem exists_finiteGalois_mapCoefficients_eq [IsGalois k L]
    (x : Lie.AffinePoints G (MvPolynomial I L)) :
    ∃ E : FiniteGaloisIntermediateField k L,
      ∃ y : Lie.AffinePoints G (MvPolynomial I E),
        mapCoefficients E.toIntermediateField.val y = x := by
  obtain ⟨E, hE, y, hy⟩ := exists_finiteDimensional_mapCoefficients_eq x
  let := hE
  let N : FiniteGaloisIntermediateField k L :=
    { IntermediateField.normalClosure k E L with
      finiteDimensional := _root_.normalClosure.is_finiteDimensional k E L
      isGalois := IsGalois.normalClosure k E L }
  let i : E →ₐ[k] N := IntermediateField.inclusion
    (IntermediateField.le_normalClosure E)
  refine ⟨N, mapCoefficients i y, ?_⟩
  rw [mapCoefficients_comp]
  exact hy

/-- A finite Galois coefficient model of a polynomial point, retaining the
coefficient-extension equation. -/
structure FiniteGaloisModel (x : Lie.AffinePoints G (MvPolynomial I L)) where
  field : FiniteGaloisIntermediateField k L
  point : Lie.AffinePoints G (MvPolynomial I field)
  extension_eq : mapCoefficients field.toIntermediateField.val point = x

/-- Choose a finite Galois coefficient model of the original polynomial point. -/
def finiteGaloisModel [IsGalois k L]
    (x : Lie.AffinePoints G (MvPolynomial I L)) : FiniteGaloisModel x := by
  apply Classical.choice
  obtain ⟨E, y, hy⟩ := exists_finiteGalois_mapCoefficients_eq x
  exact ⟨⟨E, y, hy⟩⟩

end FiniteModel

end Langlands.GroupScheme.PolynomialPoint
