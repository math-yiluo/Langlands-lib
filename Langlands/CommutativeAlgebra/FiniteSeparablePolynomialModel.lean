import Langlands.CommutativeAlgebra.FiniteSeparableIntegralModel
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.IsAdjoinRoot

/-! # Finite free polynomial models of separable fraction-field extensions -/

universe u v w

open scoped nonZeroDivisors
open Algebra IntermediateField Polynomial

namespace Langlands.CommutativeAlgebra

variable (R : Type u) (K : Type v) (L : Type w)
  [CommRing R] [IsDomain R] [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K] [Algebra R L] [Algebra K L]
  [IsScalarTower R K L]

/-- A polynomial presentation of an actual integral primitive-element model.
Its defining monic polynomial maps to the generic minimal polynomial. -/
structure FiniteSeparablePolynomialModel extends FiniteSeparableIntegralModel R K L where
  polynomial : R[X]
  monic : polynomial.Monic
  map_eq_minpoly : polynomial.map (algebraMap R K) = minpoly K generator

theorem nonempty_finiteSeparablePolynomialModel
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    Nonempty (FiniteSeparablePolynomialModel R K L) := by
  obtain ⟨a, ha⟩ := Field.exists_primitive_element K L
  let m := minpoly K a
  have hm : m.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral a)
  let r := IsLocalization.commonDenom R⁰ m.support m.coeff
  have hr : algebraMap R K r ≠ 0 := by
    exact fun h => (mem_nonZeroDivisors_iff_ne_zero.mp r.property)
      ((IsFractionRing.to_map_eq_zero_iff (R := R) (K := K)).mp h)
  obtain ⟨p, hp, _, hpm⟩ := lifts_and_natDegree_eq_and_monic
    (IsLocalization.scaleRoots_commonDenom_mem_lifts R⁰ m (by
      rw [hm.leadingCoeff]; exact one_mem _))
    (by simpa only [monic_scaleRoots_iff] using hm)
  have hbmin : minpoly K (r • a) = p.map (algebraMap R K) := by
    rw [hp]
    convert IsIntegrallyClosed.minpoly_smul hr (Algebra.IsIntegral.isIntegral a) using 1
    simp only [Submonoid.smul_def, Algebra.smul_def, IsScalarTower.algebraMap_apply R K L]
  have hbint : IsIntegral R (r • a) := by
    refine ⟨p, hpm, ?_⟩
    change aeval (r • a) p = 0
    rw [Polynomial.aeval_eq_aeval_map
      (IsScalarTower.algebraMap_eq R K L).symm, ← hbmin]
    exact minpoly.aeval K (r • a)
  have hbprim : K⟮r • a⟯ = ⊤ := by
    simp only [Submonoid.smul_def, Algebra.smul_def]
    rw [mul_comm, IsScalarTower.algebraMap_apply R K L,
      IntermediateField.adjoin_simple_mul_algebraMap a _ hr, ha]
  exact ⟨⟨⟨r • a, hbint, hbprim⟩, p, hpm, hbmin.symm⟩⟩

/-- Choose the proved polynomial model. -/
noncomputable def finiteSeparablePolynomialModel
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    FiniteSeparablePolynomialModel R K L :=
  Classical.choice (nonempty_finiteSeparablePolynomialModel R K L)

namespace FiniteSeparablePolynomialModel

variable {R K L}

abbrev Carrier (d : FiniteSeparablePolynomialModel R K L) :=
  d.toFiniteSeparableIntegralModel.Carrier

/-- The defining polynomial cuts out precisely the actual subalgebra inside L. -/
noncomputable def presentation (d : FiniteSeparablePolynomialModel R K L) :
    IsAdjoinRootMonic d.Carrier d.polynomial := by
  let b : d.Carrier := ⟨d.generator, Algebra.self_mem_adjoin_singleton R d.generator⟩
  have hval (p : R[X]) : (↑(aeval b p) : L) = aeval d.generator p :=
    (Polynomial.aeval_algHom_apply d.Carrier.val b p).symm
  refine
    { map := aeval b
      map_surjective := ?_
      ker_map := ?_
      monic := d.monic }
  · intro s
    obtain ⟨p, hp⟩ := Algebra.adjoin_eq_exists_aeval (R := R) d.generator s
    refine ⟨p, Subtype.ext ?_⟩
    exact (hval p).trans hp
  · ext p
    change aeval b p = 0 ↔ p ∈ Ideal.span {d.polynomial}
    rw [Ideal.mem_span_singleton]
    have heval : aeval b p = 0 ↔ aeval d.generator p = 0 := by
      constructor
      · intro h
        have h' := congrArg (fun x : d.Carrier => (x : L)) h
        simpa only [hval, ZeroMemClass.coe_zero] using h'
      · intro h
        apply Subtype.ext
        exact (hval p).trans h
    rw [heval, ← Polynomial.map_dvd_map (algebraMap R K)
      (IsFractionRing.injective R K) d.monic, d.map_eq_minpoly]
    rw [minpoly.dvd_iff]
    rw [← Polynomial.aeval_eq_aeval_map (IsScalarTower.algebraMap_eq R K L).symm]

/-- The powers below the generic degree form a basis over the original domain. -/
noncomputable def powerBasis (d : FiniteSeparablePolynomialModel R K L) :
    PowerBasis R d.Carrier :=
  d.presentation.powerBasis

instance free (d : FiniteSeparablePolynomialModel R K L) : Module.Free R d.Carrier :=
  Module.Free.of_basis d.powerBasis.basis

instance finitePresentation (d : FiniteSeparablePolynomialModel R K L) :
    Algebra.FinitePresentation R d.Carrier :=
  Algebra.FinitePresentation.equiv d.presentation.toIsAdjoinRoot.adjoinRootAlgEquiv

end FiniteSeparablePolynomialModel

end Langlands.CommutativeAlgebra
