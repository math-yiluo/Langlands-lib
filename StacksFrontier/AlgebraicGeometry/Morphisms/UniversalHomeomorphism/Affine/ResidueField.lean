module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Ideal.Quotient.Operations

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Residue fields of affine schemes and of prime ideals

A point of `Spec R` has two residue fields: the scheme-theoretic one, `(Spec R).residueField`,
and the algebraic one, `Ideal.ResidueField` of the corresponding prime. They agree, and a
morphism `Spec.map f` induces the same map on both. This file records that comparison and
the transfer of `IsIso` across it, so that a statement about scheme-theoretic residue fields
can be proved by a computation with `Ideal.ResidueField.map`.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.specResidueFieldMap_bridge` identifies the residue-field map of
  `Spec.map f` with `Ideal.ResidueField.map` of the underlying ring map.
* `AlgebraicGeometry.idealResidueFieldMap_isIso_of_specMap` and
  `AlgebraicGeometry.specResidueFieldMap_isIso_of_idealResidueFieldMap` transfer `IsIso`
  in either direction across that identification.
* `AlgebraicGeometry.idealResidueFieldMap_comp` is the composition law for
  `Ideal.ResidueField.map`, and `AlgebraicGeometry.idealResidueFieldMap_id_isIso` says that the
  map attached to the identity and two equal primes is an isomorphism.
* `AlgebraicGeometry.isIso_residueFieldMap_of_isIso_comp` cancels a composite in the second
  factor of a residue-field map.

## Implementation notes

The comparison isomorphism is Mathlib's `Scheme.Spec.residueFieldIso`. Conjugating by it turns
the scheme-theoretic map into the algebraic one; both directions of the resulting `IsIso`
transfer are recorded because the proofs below use each of them.

## References

* [Stacks Project, Tag 0CN7](https://stacks.math.columbia.edu/tag/0CN7)
* [Stacks Project, Tag 0CN8](https://stacks.math.columbia.edu/tag/0CN8)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A point of an affine scheme is a prime ideal of the ring, so its underlying ideal is
prime. This bridging instance lets `Ideal.ResidueField` be applied to a point of `Spec R`. -/
instance specPoint_asIdeal_isPrime (R : CommRingCat.{u}) (y : Spec R) :
    y.asIdeal.IsPrime :=
  y.isPrime

/-- Conjugating the residue-field map of `Spec.map f` by the comparison isomorphisms between
the scheme-theoretic and the algebraic residue fields yields `Ideal.ResidueField.map` of the
underlying ring map. -/
lemma specResidueFieldMap_bridge {R T : CommRingCat.{u}} (f : R ⟶ T) (z : Spec T) :
    ((Scheme.Spec.residueFieldIso R (Spec.map f z)).inv ≫
      (Spec.map f).residueFieldMap z ≫ (Scheme.Spec.residueFieldIso T z).hom).hom =
      Ideal.ResidueField.map (Spec.map f z).asIdeal z.asIdeal f.hom
        (by simpa only [Spec.map_apply] using PrimeSpectrum.comap_asIdeal f.hom z) := by
  apply Ideal.ResidueField.ringHom_ext
  ext r
  simp only [RingHom.comp_apply, Ideal.ResidueField.map_algebraMap]
  have H := (Spec.map f).SpecMap_residueFieldMap_fromSpecResidueField z
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField R (Spec.map f z),
    ← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField T z] at H
  simp only [← Spec.map_comp, Category.assoc] at H
  have H' := Spec.map_injective H
  have H'' := congrArg
    (fun h : R ⟶ (Spec T).residueField z => h ≫ (Scheme.Spec.residueFieldIso T z).hom) H'
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at H''
  simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] using
    congrArg (fun h : R ⟶ CommRingCat.of z.asIdeal.ResidueField => h.hom r) H''

end AlgebraicGeometry

end
