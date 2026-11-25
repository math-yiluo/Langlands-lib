module

public import Mathlib.CategoryTheory.Presentable.Directed
public import Mathlib.FieldTheory.CardinalEmb
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.SeparableDegree
public import Mathlib.RingTheory.Adjoin.Field
public import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Algebra.Category.AlgCat.FilteredColimits
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Etale.Finite
public import Mathlib.RingTheory.Ideal.HasGoingUp
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.RingHom.PurelyInseparable
public import StacksFrontier.RingTheory.Flat.TowerLTensor
public import StacksFrontier.RingTheory.Henselian.FiniteType.Basic.ProductOfLocalRings
public import StacksFrontier.RingTheory.GeometricallyNormal.TFAE
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
public import StacksFrontier.RingTheory.Smooth.Normal

set_option autoImplicit false
set_option maxSynthPendingDepth 3

@[expose] public section

/-!
# Shared correspondences between minimal and maximal primes

This module collects the ring-theoretic correspondences used to compute the branches of a local
ring, both from a henselization and from an adic completion. The results describe how
contraction along a base change behaves on maximal ideals and on minimal primes, when a minimal
prime below a given prime is unique, and when normality is inherited by a tensor product
presented as a filtered colimit of etale algebras or by an integral closure of a finite product.

## Main results

* `bijOn_maximalIdeals_tensorProduct`: contraction is bijective from the maximal ideals of a
  base change to those of the base, given a bijection on residue fields.
* `bijOn_minimalPrimes_integralClosure_tensorProduct`: contraction is bijective on minimal
  primes for the integral closure of a base change.
* `existsUnique_minimalPrime_le_of_isNormalRing`: a maximal ideal of a normal ring contains a
  unique minimal prime.
* `isNormalRing_tensorProduct_of_ind_etale`: a tensor product with an ind-etale algebra of a
  normal ring is normal.
* `isNormalRing_integralClosure_fractionRing_reduction`: the integral closure of a reduction in
  its total ring of fractions is normal.
-/

universe u v w

set_option maxRecDepth 4096

open Topology
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

/-- If `A` has finitely many minimal primes, then so does its reduction `A ⧸ nilradical A`. -/
theorem finite_minimalPrimes_quotient_nilradical
    (A : Type u) [CommRing A] (hmin : (minimalPrimes A).Finite) :
    (minimalPrimes (A ⧸ nilradical A)).Finite := by
  apply Set.Finite.of_finite_image (f := Ideal.comap (Ideal.Quotient.mk (nilradical A)))
  · rw [← Ideal.minimalPrimes_eq_comap]
    simpa [nilradical, Ideal.radical_minimalPrimes, minimalPrimes] using hmin
  · exact (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective).injOn

end
