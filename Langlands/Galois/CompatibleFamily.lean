import Langlands.Galois.CoefficientRepresentation
import Langlands.Galois.Local.SpectralDefinitions
import Langlands.Cohomology.Weights.Polynomial

/-!
# Compatibility using actual residue actions and geometric Frobenius

Frobenius matching includes existence of a lift, not just a universal implication.
Neither a supplied Galois group nor a freely declared inertia predicate is used.
-/

noncomputable section

universe uK uL uV

namespace Langlands.GaloisRepresentation

open Polynomial
open scoped Valued

variable {K : Type uK} [Field K] [NumberField K]

/-- The residue characteristic of an actual nonzero prime of the ring of integers. -/
def residueCharacteristic (v : Global.FinitePlace K) : ℕ :=
  ringChar (NumberField.RingOfIntegers K ⧸ v.asIdeal)

/-- Cardinality of the residue field of the global finite place. -/
def residueCardinality (v : Global.FinitePlace K) : ℕ :=
  Ideal.absNorm v.asIdeal

/-- The actual absolute Galois group of the completion. -/
abbrev LocalGroup (v : Global.FinitePlace K) :=
  Field.absoluteGaloisGroup (Global.FiniteCompletion K v)

/-- The residue field of the spectral valuation on the actual algebraic closure. -/
abbrev LocalResidueClosure (v : Global.FinitePlace K) :=
  IsLocalRing.ResidueField (Langlands.LocalGalois.extensionIntegers
    (Global.FiniteCompletion K v) (AlgebraicClosure (Global.FiniteCompletion K v)))

/-- Reduction of actual local Galois automorphisms, constructed in the Library. -/
def localResidueAction (v : Global.FinitePlace K) : LocalGroup v →*
    (LocalResidueClosure v ≃ₐ[
      IsLocalRing.ResidueField (Langlands.LocalGalois.baseIntegers
        (Global.FiniteCompletion K v))] LocalResidueClosure v) :=
  Langlands.LocalGalois.residueHom
    (Global.FiniteCompletion K v) (AlgebraicClosure (Global.FiniteCompletion K v))

/-- The actual kernel of reduction, not an independently supplied subgroup. -/
abbrev localInertia (v : Global.FinitePlace K) : Subgroup (LocalGroup v) :=
  (localResidueAction v).ker

/-- A lift of geometric Frobenius: its inverse acts on residues by the
cardinality power. This defines a condition on actual automorphisms. -/
def IsGeometricFrobeniusLift (v : Global.FinitePlace K) (g : LocalGroup v) : Prop :=
  ∀ x : LocalResidueClosure v,
    localResidueAction v (g⁻¹) x = x ^ residueCardinality v

theorem residueAction_eq_of_geometricFrobenius
    {v : Global.FinitePlace K} {g h : LocalGroup v}
    (hg : IsGeometricFrobeniusLift v g) (hh : IsGeometricFrobeniusLift v h) :
    localResidueAction v g = localResidueAction v h := by
  apply inv_injective
  rw [← map_inv, ← map_inv]
  ext x
  exact (hg x).trans (hh x).symm

variable {L : Type uL} [Field L] [TopologicalSpace L]

/-- Unramifiedness of the actual restricted representation is triviality on
the kernel of the constructed residue action. -/
def IsUnramifiedAt (A : Objects.{uK, uL, uV} K L) (v : Global.FinitePlace K) : Prop :=
  ∀ i : localInertia v, (atFinitePlace v A).val.representation i.val = 1

theorem action_eq_of_residueAction_eq
    {A : Objects.{uK, uL, uV} K L} {v : Global.FinitePlace K}
    (hA : IsUnramifiedAt A v) {g h : LocalGroup v}
    (hres : localResidueAction v g = localResidueAction v h) :
    (atFinitePlace v A).val.representation g =
      (atFinitePlace v A).val.representation h := by
  have hker : g * h⁻¹ ∈ localInertia v := by
    change localResidueAction v (g * h⁻¹) = 1
    rw [map_mul, map_inv, hres, mul_inv_cancel]
  have hprod := hA ⟨g * h⁻¹, hker⟩
  let r := (atFinitePlace v A).val.representation
  change r (g * h⁻¹) = 1 at hprod
  change r g = r h
  calc
    r g = r g * (r (h⁻¹) * r h) := by
      rw [← map_mul, inv_mul_cancel, map_one, mul_one]
    _ = r (g * h⁻¹) * r h := by rw [map_mul, mul_assoc]
    _ = r h := by rw [hprod, one_mul]

theorem eulerPolynomial_eq_of_geometricFrobenius
    {A : Objects.{uK, uL, uV} K L} {v : Global.FinitePlace K}
    (hA : IsUnramifiedAt A v) {g h : LocalGroup v}
    (hg : IsGeometricFrobeniusLift v g) (hh : IsGeometricFrobeniusLift v h) :
    eulerPolynomial (atFinitePlace v A) g =
      eulerPolynomial (atFinitePlace v A) h := by
  unfold eulerPolynomial characteristicPolynomial
  rw [action_eq_of_residueAction_eq hA
    (residueAction_eq_of_geometricFrobenius hg hh)]

/-- Matching includes unramifiedness and an actual geometric-Frobenius lift.
Independence of the chosen lift is proved, not an input field. -/
def HasEulerPolynomialAt (A : Objects.{uK, uL, uV} K L)
    (v : Global.FinitePlace K) (P : L[X]) : Prop :=
  IsUnramifiedAt A v ∧
    ∃ g : LocalGroup v, IsGeometricFrobeniusLift v g ∧
      eulerPolynomial (atFinitePlace v A) g = P

theorem HasEulerPolynomialAt.forall_lifts
    {A : Objects.{uK, uL, uV} K L} {v : Global.FinitePlace K} {P : L[X]}
    (hA : HasEulerPolynomialAt A v P) (g : LocalGroup v)
    (hg : IsGeometricFrobeniusLift v g) :
    eulerPolynomial (atFinitePlace v A) g = P := by
  obtain ⟨hur, h, hh, hP⟩ := hA
  exact (eulerPolynomial_eq_of_geometricFrobenius hur hg hh).trans hP

section Families

variable {L : Type uL} [Field L] [NumberField L]

/-- A collection of genuine lambda-adic representations, with finitely many
coefficient places omitted. The name alone imposes no compatibility condition. -/
abbrev Collection (K : Type uK) [Field K] (L : Type uL) [Field L] [NumberField L]
    (excluded : Finset (Global.FinitePlace L)) :=
  (lam : {lam : Global.FinitePlace L // lam ∉ excluded}) →
    LambdaAdic.{uK, uL, uV} K L lam.val

/-- A common finite exceptional set and common coefficient-field Euler
polynomials, only away from the coefficient residue characteristic. -/
def MatchesOutside (excluded : Finset (Global.FinitePlace L))
    (R : Collection.{uK, uL, uV} K L excluded)
    (S : Finset (Global.FinitePlace K)) (P : Global.FinitePlace K → L[X]) : Prop :=
  ∀ (lam : {lam : Global.FinitePlace L // lam ∉ excluded}) (v : Global.FinitePlace K),
    v ∉ S → residueCharacteristic v ≠ residueCharacteristic lam.val →
      HasEulerPolynomialAt (R lam) v
        ((P v).map (NumberField.FinitePlace.embedding lam.val))

/-- Compatibility is a proposition on actual representations, not a field
asserting that an automorphic-existence theorem already holds. -/
def IsCompatible (excluded : Finset (Global.FinitePlace L))
    (R : Collection.{uK, uL, uV} K L excluded) : Prop :=
  ∃ S : Finset (Global.FinitePlace K), ∃ P : Global.FinitePlace K → L[X],
    MatchesOutside excluded R S P

/-- A fixed rank is separate from compatibility and semisimplicity. -/
def HasRank (excluded : Finset (Global.FinitePlace L))
    (R : Collection.{uK, uL, uV} K L excluded) (n : ℕ) : Prop :=
  ∀ lam, (R lam).val.rank = n

/-- Purity of a single compatible collection, using all rational conjugates
of every eigenvalue, with the monic/eigenvalue polynomial recovered by reversal. -/
def IsPureCompatible (excluded : Finset (Global.FinitePlace L))
    (R : Collection.{uK, uL, uV} K L excluded) (w : ℤ) : Prop :=
  ∃ S : Finset (Global.FinitePlace K), ∃ P : Global.FinitePlace K → L[X],
    MatchesOutside excluded R S P ∧
      ∀ v, v ∉ S → Cohomology.Weights.IsPurePolynomial
        (residueCardinality v) w (P v).reverse

end Families

end Langlands.GaloisRepresentation
