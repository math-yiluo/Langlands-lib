import Langlands.Global.ArithmeticExceptionalSets
import Langlands.Global.CurvePlaceAdeleRing
import Langlands.Global.AdelicFunctoriality.LocalDegree
import Mathlib.RingTheory.Valuation.LocalSubring

noncomputable section

universe u

open IsDedekindDomain
open scoped NumberField

namespace Langlands.Global

section Curve

variable {k K L : Type u} [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L]
  [IsScalarTower k K L] [FiniteDimensional K L]
  (S : Finset (AlgebraicCurve.Place k K))

/-- Integrality outside the full upper preimage reflects integrality below. -/
theorem curvePlaceSIntegers_algebraMap_mem_iff (x : K) :
    algebraMap K L x ∈ curvePlaceSIntegers k L
      (curvePlaceExceptionalPreimage (L := L) S) ↔ x ∈ curvePlaceSIntegers k K S := by
  constructor
  · intro hx p hp
    obtain ⟨q, hq⟩ := curvePlaceRestriction_surjective (L := L) p
    have h := hx q (by simpa [hq] using hp)
    rw [← hq]
    exact (curvePlaceRestriction_mem_iff q x).mpr h
  · intro hx q hq
    exact (curvePlaceRestriction_mem_iff q x).mp
      (hx _ (by simpa using hq))

/-- The original field embedding restricted to the actual outside-S integer rings. -/
def curvePlaceSIntegersExtension :
    curvePlaceSIntegers k K S →+*
      curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) S) :=
  ((algebraMap K L).comp (curvePlaceSIntegers k K S).subtype).codRestrict _
    (fun x => (curvePlaceSIntegers_algebraMap_mem_iff S x).mpr x.property)

@[simp]
theorem curvePlaceSIntegersExtension_coe (x : curvePlaceSIntegers k K S) :
    (curvePlaceSIntegersExtension (L := L) S x : L) = algebraMap K L (x : K) := rfl

/-- The S-integer extension retains the injectivity of the original field embedding. -/
theorem curvePlaceSIntegersExtension_injective :
    Function.Injective (curvePlaceSIntegersExtension (L := L) S) := by
  intro x y h
  exact Subtype.ext ((algebraMap K L).injective (congrArg Subtype.val h))

scoped instance curvePlaceSIntegersExtensionAlgebra :
    Algebra (curvePlaceSIntegers k K S)
      (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) S)) :=
  (curvePlaceSIntegersExtension S).toAlgebra

scoped instance curvePlaceSIntegersExtensionFieldAlgebra :
    Algebra (curvePlaceSIntegers k K S) L :=
  ((algebraMap K L).comp (curvePlaceSIntegers k K S).subtype).toAlgebra

scoped instance curvePlaceSIntegersExtensionLowerTower :
    IsScalarTower (curvePlaceSIntegers k K S) K L :=
  .of_algebraMap_eq fun _ => rfl

scoped instance curvePlaceSIntegersExtensionUpperTower :
    IsScalarTower (curvePlaceSIntegers k K S)
      (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) S)) L :=
  .of_algebraMap_eq fun _ => rfl

/-- Lower integral elements belong to every required upper valuation ring. -/
theorem curvePlaceSIntegers_integralClosure_le :
    (integralClosure (curvePlaceSIntegers k K S) L).toSubring ≤
      curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) S) := by
  intro x hx q hq
  let R := curvePlaceSIntegers k K S
  let f : R →+* q.toValuationSubring :=
    ((algebraMap K L).comp R.subtype).codRestrict _ fun a =>
      (curvePlaceRestriction_mem_iff q (a : K)).mp (a.property _ (by simpa using hq))
  let : Algebra R q.toValuationSubring := f.toAlgebra
  let : IsScalarTower R q.toValuationSubring L := .of_algebraMap_eq fun _ => rfl
  obtain ⟨a, ha⟩ := (isIntegrallyClosed_iff L).mp
    (inferInstance : IsIntegrallyClosed q.toValuationSubring)
    (hx.tower_top : IsIntegral q.toValuationSubring x)
  exact ha ▸ a.property

end Curve

section NumberField

variable {K L : Type u} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]

/-- The original finite-place integrality test is preserved and reflected upstairs. -/
theorem numberFieldPlace_algebraMap_integral_iff
    (p : FinitePlace K) (q : FinitePlace L) [q.asIdeal.LiesOver p.asIdeal] (x : K) :
    q.valuation L (algebraMap K L x) ≤ 1 ↔ p.valuation K x ≤ 1 := by
  rw [← HeightOneSpectrum.valuation_liesOver L p q]
  exact pow_le_one_iff_of_nonneg zero_le
    (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver q.asIdeal p.ne_bot)

omit [NumberField K] [NumberField L] in
/-- Restriction of every upper finite place is the given lower place. -/
private theorem under_eq_of_liesOver
    (p : FinitePlace K) (q : FinitePlace L) [q.asIdeal.LiesOver p.asIdeal] :
    q.under (NumberField.RingOfIntegers K) = p := by
  apply HeightOneSpectrum.ext
  exact (Ideal.over_def q.asIdeal p.asIdeal).symm

variable (S : Finset (FinitePlace K))

/-- The full-preimage S-integer test reflects the original lower S-integer test. -/
theorem numberFieldSIntegers_algebraMap_mem_iff (x : K) :
    algebraMap K L x ∈ ((numberFieldExceptionalPreimage (L := L) S :
      Finset (FinitePlace L)) : Set (FinitePlace L)).integer L ↔
      x ∈ (S : Set (FinitePlace K)).integer K := by
  constructor
  · intro hx p hp
    let q := AdelicFunctoriality.placeAbove L p
    have : q.1.asIdeal.LiesOver p.asIdeal := q.2
    exact (numberFieldPlace_algebraMap_integral_iff p q.1 x).mp
      (hx q.1 (by simpa [under_eq_of_liesOver p q.1] using hp))
  · intro hx q hq
    exact (numberFieldPlace_algebraMap_integral_iff
      (q.under (NumberField.RingOfIntegers K)) q x).mpr
      (hx _ (by simpa using hq))

/-- The original number-field embedding restricted to the actual S-integer rings. -/
def numberFieldSIntegersExtension :
    (S : Set (FinitePlace K)).integer K →+*
      ((numberFieldExceptionalPreimage (L := L) S :
        Finset (FinitePlace L)) : Set (FinitePlace L)).integer L :=
  ((algebraMap K L).comp ((S : Set (FinitePlace K)).integer K).toSubring.subtype).codRestrict _
    (fun x => (numberFieldSIntegers_algebraMap_mem_iff S x).mpr x.property)

@[simp]
theorem numberFieldSIntegersExtension_coe
    (x : (S : Set (FinitePlace K)).integer K) :
    (numberFieldSIntegersExtension (L := L) S x : L) = algebraMap K L (x : K) := rfl

theorem numberFieldSIntegersExtension_injective :
    Function.Injective (numberFieldSIntegersExtension (L := L) S) := by
  intro x y h
  exact Subtype.ext ((algebraMap K L).injective (congrArg Subtype.val h))

scoped instance numberFieldSIntegersExtensionAlgebra :
    Algebra ((S : Set (FinitePlace K)).integer K)
      (((numberFieldExceptionalPreimage (L := L) S :
        Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) :=
  (numberFieldSIntegersExtension S).toAlgebra

scoped instance numberFieldSIntegersExtensionFieldAlgebra :
    Algebra ((S : Set (FinitePlace K)).integer K) L :=
  Subalgebra.toAlgebra _

scoped instance numberFieldSIntegersExtensionLowerTower :
    IsScalarTower ((S : Set (FinitePlace K)).integer K) K L :=
  .of_algebraMap_eq fun _ => rfl

scoped instance numberFieldSIntegersExtensionUpperTower :
    IsScalarTower ((S : Set (FinitePlace K)).integer K)
      (((numberFieldExceptionalPreimage (L := L) S :
        Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) L :=
  .of_algebraMap_eq fun _ => rfl

/-- Lower integral elements are upper S-integers at the full exceptional preimage. -/
theorem numberFieldSIntegers_integralClosure_le :
    (integralClosure ((S : Set (FinitePlace K)).integer K) L).toSubring ≤
      (((numberFieldExceptionalPreimage (L := L) S :
        Finset (FinitePlace L)) : Set (FinitePlace L)).integer L).toSubring := by
  intro x hx q hq
  let R := (S : Set (FinitePlace K)).integer K
  let V := (q.valuation L).valuationSubring
  let f : R →+* V :=
    ((algebraMap K L).comp R.toSubring.subtype).codRestrict _ fun a =>
      (numberFieldPlace_algebraMap_integral_iff
        (q.under (NumberField.RingOfIntegers K)) q a).mpr
        (a.property _ (by simpa using hq))
  let : Algebra R V := f.toAlgebra
  let : IsScalarTower R V L := .of_algebraMap_eq fun _ => rfl
  obtain ⟨a, ha⟩ := (isIntegrallyClosed_iff L).mp
    (inferInstance : IsIntegrallyClosed V) (hx.tower_top : IsIntegral V x)
  exact ha ▸ a.property

end NumberField

end Langlands.Global
