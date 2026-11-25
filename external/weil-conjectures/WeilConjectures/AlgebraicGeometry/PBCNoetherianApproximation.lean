/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionPresentation
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Algebra.MvPolynomial.Basic
import WeilConjectures.RingTheory.PolynomialQuotientDimensionLowerBound
import Mathlib.RingTheory.Extension.Presentation.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import WeilConjectures.AlgebraicGeometry.NoetherianCoefficientNeighborhood
import WeilConjectures.AlgebraicGeometry.NoetherianBoundedCoverDescent

/-! # Noetherian approximation of a relative global complete intersection

Source: Stacks Project, Algebra, Lemma Tag 00SU
(blueprint: lem-weil-pbc-relative-global-complete-intersection-noetherian-approximation).
-/

@[expose] public section

universe u

namespace Algebra

/-- The coefficient ring is constructed by adjoining the finite union of coefficient sets. -/
private theorem finite_coefficient_model
    (R : Type u) [CommRing R] (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) R) :
    ∃ (R₀ : Subring R), Algebra.FiniteType ℤ R₀ ∧
      ∃ f₀ : Fin c → MvPolynomial (Fin n) R₀,
        ∀ i, MvPolynomial.map R₀.subtype (f₀ i) = f i := by
  classical
  let t : Set R := ⋃ i, ((f i).coeffs : Set R)
  have ht : t.Finite := Set.finite_iUnion fun i ↦ (f i).coeffs.finite_toSet
  let A := Algebra.adjoin ℤ t
  have hA : Algebra.FiniteType ℤ A := Algebra.FiniteType.adjoin_of_finite ht
  have hcoeff (i : Fin c) :
      ((f i).coeffs : Set R) ⊆ Set.range A.toSubring.subtype := by
    intro r hr
    exact ⟨⟨r, Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨i, hr⟩)⟩, rfl⟩
  choose f₀ hf₀ using fun i ↦ MvPolynomial.mem_range_map_iff_coeffs_subset.mpr (hcoeff i)
  exact ⟨A.toSubring, hA, f₀, hf₀⟩

/-- A nonempty original spectrum forces the equation count to be at most the variable count. -/
private theorem equation_count_le_of_point
    {R : Type u} [CommRing R] {n c : ℕ} (f : Fin c → MvPolynomial (Fin n) R)
    (h : IsRelativeGlobalCompleteIntersectionPresentation f)
    (q : PrimeSpectrum (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))) : c ≤ n := by
  let S := MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)
  let p := PrimeSpectrum.comap (algebraMap R S) q
  have hn : Nontrivial (p.asIdeal.Fiber S) :=
    (PrimeSpectrum.nontrivial_iff_mem_rangeComap p).mpr ⟨q, rfl⟩
  exact (h p.asIdeal hn).1

/-- Scalar extension identifies a fibre with the quotient by the residue-field equations. -/
private theorem polynomial_quotient_fibre_lower_bound
    {R : Type u} [CommRing R] {n c : ℕ} (f : Fin c → MvPolynomial (Fin n) R)
    (hc : c ≤ n) (p : Ideal R) [p.IsPrime]
    (hn : Nontrivial (p.Fiber (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)))) :
    ((n - c : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim
      (PrimeSpectrum (p.Fiber (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)))) := by
  classical
  let k := p.ResidueField
  let P := (Presentation.naive (v := f)).baseChange k
  let e := (Ideal.quotientEquivAlgOfEq k P.span_range_relation_eq_ker).trans
    (P.quotientEquiv.restrictScalars k)
  have : Nontrivial (p.Fiber (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))) := hn
  have : Nontrivial (MvPolynomial (Fin n) k ⧸ Ideal.span
      (Set.range (fun i ↦ MvPolynomial.map (algebraMap R k) (f i)))) :=
    e.toEquiv.nontrivial
  have hl := AlgebraicGeometry.sub_le_topologicalKrullDim_spec_mvPolynomial_quotient
    k n c hc (fun i ↦ MvPolynomial.map (algebraMap R k) (f i))
  have hd := IsHomeomorph.topologicalKrullDim_eq
    (PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv)
    (PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv).isHomeomorph
  change ((n - c : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim
    (PrimeSpectrum (MvPolynomial (Fin n) k ⧸ Ideal.span
      (Set.range (fun i ↦ MvPolynomial.map (algebraMap R k) (f i))))) at hl
  exact hl.trans_eq hd

/-- Descend the specified complete-intersection presentation to a finite type subring.
Source: Stacks Project, Algebra, Lemma Tag 00SU
(blueprint: lem-weil-pbc-relative-global-complete-intersection-noetherian-approximation).

Proof, following the six blueprint steps:
1. Generate a finite type subring by the coefficients of the relations, and form its
polynomial quotient. Polynomial scalar extension and tensor-quotient base change identify
its base change with the original quotient (`lem-weil-pbc-polynomial-scalar-extension`,
`lem-weil-pbc-tensor-quotient-base-change`, `def-weil-pbc-finite-type-algebra`).
2. Contract a prime of the original quotient to the coefficient model and both bases.
The fibre rings are nonzero, and tensor cancellation identifies one as the field extension
of the other. Faithful flatness makes the map of spectra surjective. Local dimension is
unchanged under field extension; taking suprema shows global dimensions agree, hence the
model fibre has dimension `n-c`. Use `lem-weil-pbc-tensor-cancel-base-change`,
`lem-weil-pbc-prime-in-image-iff-fibre-ring-nonzero`,
`lem-weil-pbc-field-extension-base-change-faithfully-flat`,
`lem-weil-pbc-faithfully-flat-surjective-spectrum`,
`lem-weil-pbc-dimension-at-point-field-extension`, and
`lem-weil-pbc-dimension-supremum-local-dimensions`.
3. Apply `lem-weil-pbc-fibre-dimension-neighborhood` at the contracted prime with its
actual local dimension. Obtain a principal open on which all nonzero fibres have dimension
at most `n-c`; its pullback contains the original prime
(`lem-weil-pbc-spec-localization-away-basic-open`).
4. Quasi-compactness gives finitely many such opens covering the original spectrum.
Lift their generators and a unit-ideal identity to polynomials, obtaining an identity
`1 - ∑ hⱼ Gⱼ = ∑ aᵢ fᵢ`. For the zero quotient take the empty cover and the identity
`1 = ∑ aᵢ fᵢ` (`lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`).
5. Enlarge the coefficient subring by the finitely many coefficients in this identity.
The identity now holds in the new model, so its principal opens cover its spectrum.
Fibre bounds persist under enlargement by polynomial and quotient base change, localization
base change (`lem-weil-pbc-algebra-localization-away-base-change`), field-extension invariance
of local dimension, and the supremum formula. Local dimension is unchanged on these opens
(`lem-weil-pbc-dimension-at-point-open-subspace`), giving the bound on every nonzero fibre.
6. If the new quotient is zero the condition is vacuous. Otherwise a nonzero fibre
forces `c ≤ n`. Each nonzero fibre is the quotient of a polynomial ring over its residue
field by these same `c` equations. The bound
`lem-weil-pbc-polynomial-quotient-dimension-lower-bound` gives dimension at least `n-c`.
Together with step 5 this gives equality, so take the enlarged subring.
-/
theorem exists_finiteType_subring_relativeGlobalCompleteIntersection
    (R : Type u) [CommRing R] (n c : ℕ)
    (f : Fin c → MvPolynomial (Fin n) R)
    (h : IsRelativeGlobalCompleteIntersectionPresentation f) :
    ∃ (R₀ : Subring R), Algebra.FiniteType ℤ R₀ ∧
      ∃ (f₀ : Fin c → MvPolynomial (Fin n) R₀),
        (∀ (i : Fin c) (d : Fin n →₀ ℕ),
          (AddMonoidAlgebra.coeff (f i) d) = (((AddMonoidAlgebra.coeff (f₀ i) d) : R₀) : R)) ∧
        IsRelativeGlobalCompleteIntersectionPresentation f₀ := by
  classical
  obtain ⟨R₀, hR₀, f₀, hf₀⟩ := finite_coefficient_model R n c f
  let S := MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)
  choose G hG hbound using
    exists_coefficient_model_principal_neighborhood R n c f h R₀ f₀ hf₀
  obtain ⟨R₁, hR₁, f₁, hf₁, hupper⟩ :=
    exists_finiteType_model_of_bounded_principal_cover R n c (n - c) f R₀ hR₀ f₀ hf₀
      (PrimeSpectrum S) G (fun q ↦ ⟨q, hG q⟩) hbound
  refine ⟨R₁, hR₁, f₁, ?_, ?_⟩
  · intro i d
    have hc := congrArg (fun f ↦ AddMonoidAlgebra.coeff f d) (hf₁ i)
    exact hc.symm.trans (MvPolynomial.coeff_map R₁.subtype (f₁ i) d)
  · intro p hp hn
    obtain ⟨⟨q⟩, hu⟩ := hupper p hn
    have hc : c ≤ n := equation_count_le_of_point f h q
    exact ⟨hc, le_antisymm hu (polynomial_quotient_fibre_lower_bound f₁ hc p hn)⟩

end Algebra
