import Langlands.Galois.FiniteUnramifiedGaloisRestriction
import Langlands.Galois.FrobeniusDensity
import Langlands.ClassFieldTheory.Global.Artin.ArtinUniqueness

/-!
# Inertia and Frobenius under restriction to finite abelian subfields

This file proves `Langlands.GaloisRepresentation.FiniteUnramifiedGaloisRestrictionStatement`:
for a finite abelian subextension `E` of `AlgebraicClosure K` and a prime `w` of `E` above a
finite place `v` of `K` at which `E / K` is unramified, the composite of the map
`localToGlobalGalois v` from the absolute Galois group of the completion with the restriction
`finiteGaloisRestriction E` kills local inertia and sends the inverse of every geometric
Frobenius lift to an arithmetic Frobenius at `w`.

No class field theory is used. The comparison with the completion is the one of
`Langlands/Galois/FrobeniusDensity.lean`: the inverse of the image of a geometric Frobenius lift
restricts to an arithmetic Frobenius at the prime `inducedPrime v E` induced by the completion
embedding (`arithmeticFrobeniusAt_inducedPrime`). The primes above `v` are conjugate under
`E ≃ₐ[K] E`, and conjugation moves an arithmetic Frobenius at a prime to one at the conjugate
prime; in an abelian group it does not change the element, so the restriction is an arithmetic
Frobenius at every prime above `v`. A geometric Frobenius lift times an element of local inertia
is again a geometric Frobenius lift, and an arithmetic Frobenius at an unramified prime is unique
(`eq_of_isArithFrobAt_mapAlgHom`), so local inertia restricts to `1`.

## Main declarations

* `isGeometricFrobeniusLift_mul_of_mem_localInertia`.
* `finiteGaloisRestriction_localToGlobalGalois_inv_isArithFrobAt`: Frobenius at every prime above
  `v`, without an unramifiedness hypothesis.
* `finiteGaloisRestriction_localToGlobalGalois_of_mem_localInertia`: inertia at an unramified
  prime.
* `finiteUnramifiedGaloisRestriction`: the published statement.
-/

noncomputable section

universe uK

namespace Langlands.GaloisRepresentation

open Langlands.Global
open scoped NumberField Pointwise

variable {K : Type uK} [Field K] [NumberField K]

/-- A geometric Frobenius lift times an element of local inertia is a geometric Frobenius
lift. -/
theorem isGeometricFrobeniusLift_mul_of_mem_localInertia {v : FinitePlace K}
    {g i : LocalGroup v} (hg : IsGeometricFrobeniusLift v g) (hi : i ∈ localInertia v) :
    IsGeometricFrobeniusLift v (g * i) := by
  intro x
  have hi' : localResidueAction v i⁻¹ = 1 := by
    rw [map_inv, MonoidHom.mem_ker.mp hi, inv_one]
  rw [mul_inv_rev, map_mul, hi', one_mul]
  exact hg x

variable (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] [IsGalois K E]

/-- In a finite abelian subextension `E` of `AlgebraicClosure K`, the inverse of every geometric
Frobenius lift at `v`, mapped to the global absolute Galois group and restricted to `E`, is an
arithmetic Frobenius at every prime `w` of `E` above `v`. -/
theorem finiteGaloisRestriction_localToGlobalGalois_inv_isArithFrobAt [NumberField E]
    (hcomm : ∀ σ τ : E ≃ₐ[K] E, σ * τ = τ * σ) (v : FinitePlace K) (w : FinitePlace E)
    (hw : w.asIdeal.LiesOver v.asIdeal) {g : LocalGroup v} (hg : IsGeometricFrobeniusLift v g) :
    (NumberField.RingOfIntegers.mapAlgHom
      (finiteGaloisRestriction E (localToGlobalGalois v g⁻¹))).IsArithFrobAt w.asIdeal := by
  let := inducedPrime_isPrime v E
  let := inducedPrime_liesOver v E
  obtain ⟨a, ha⟩ := Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal (inducedPrime v E)
    w.asIdeal (E ≃ₐ[K] E)
  let σ := AlgEquiv.restrictNormalHom E
    ((Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v) g)⁻¹)
  have hfrob : IsArithFrobAt (𝓞 K) σ (inducedPrime v E) :=
    arithmeticFrobeniusAt_inducedPrime v E hg
  have hconj := hfrob.conj a
  rw [ha, hcomm a σ, mul_inv_cancel_right] at hconj
  change IsArithFrobAt (𝓞 K) (AlgEquiv.restrictNormalHom E
    (Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v) g⁻¹)) w.asIdeal
  rw [map_inv]
  exact hconj

/-- In a finite abelian subextension `E` of `AlgebraicClosure K`, if `E / K` is unramified at a
prime `w` above `v`, every element of local inertia at `v`, mapped to the global absolute Galois
group, restricts to `1` on `E`. -/
theorem finiteGaloisRestriction_localToGlobalGalois_of_mem_localInertia [NumberField E]
    (hcomm : ∀ σ τ : E ≃ₐ[K] E, σ * τ = τ * σ) (v : FinitePlace K) (w : FinitePlace E)
    (hw : w.asIdeal.LiesOver v.asIdeal) (hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal)
    {i : LocalGroup v} (hi : i ∈ localInertia v) :
    finiteGaloisRestriction E (localToGlobalGalois v i) = 1 := by
  obtain ⟨g, hg⟩ := exists_geometricFrobeniusLift v
  have h := ClassFieldTheory.Global.Artin.eq_of_isArithFrobAt_mapAlgHom w hunram
    (finiteGaloisRestriction_localToGlobalGalois_inv_isArithFrobAt E hcomm v w hw
      (isGeometricFrobeniusLift_mul_of_mem_localInertia hg hi))
    (finiteGaloisRestriction_localToGlobalGalois_inv_isArithFrobAt E hcomm v w hw hg)
  rw [mul_inv_rev, map_mul, map_mul, mul_eq_right, map_inv, map_inv, inv_eq_one] at h
  exact h

/-- At an unramified prime of a finite abelian subextension of `AlgebraicClosure K`, restriction
from the absolute Galois group of the completion kills local inertia and sends the inverse of
every geometric Frobenius lift to an arithmetic Frobenius. -/
theorem finiteUnramifiedGaloisRestriction : FiniteUnramifiedGaloisRestrictionStatement.{uK} := by
  intro K _ _ E _ _ hcomm v w hw hunram
  have : NumberField E := NumberField.of_module_finite K E
  exact ⟨fun i => finiteGaloisRestriction_localToGlobalGalois_of_mem_localInertia E hcomm v w hw
      hunram i.2,
    fun _ hg => finiteGaloisRestriction_localToGlobalGalois_inv_isArithFrobAt E hcomm v w hw hg⟩

end Langlands.GaloisRepresentation
