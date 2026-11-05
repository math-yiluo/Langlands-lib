import Langlands.CommutativeAlgebra.FiniteSeparablePolynomialModel
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Etale.Field

/-! # Finite etale models after shrinking a domain -/

universe u v w

open scoped nonZeroDivisors TensorProduct
open Algebra

namespace Langlands.CommutativeAlgebra

variable {R : Type u} {K : Type v} {L : Type w}
  [CommRing R] [IsDomain R] [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K] [Algebra R L] [Algebra K L]
  [IsScalarTower R K L]

namespace FiniteSeparablePolynomialModel

omit [IsDomain R] in
/-- The actual domain model is formally etale at its generic point. -/
theorem isEtaleAt_bot (d : FiniteSeparablePolynomialModel R K L)
    [Algebra.IsAlgebraic K L] [Algebra.IsSeparable K L] :
    Algebra.IsEtaleAt R (⊥ : Ideal d.Carrier) := by
  have := d.toFiniteSeparableIntegralModel.localized
  let M := Algebra.algebraMapSubmonoid d.Carrier R⁰
  have hinj : Function.Injective (algebraMap R d.Carrier) :=
    algebraMap_injective_of_field_isFractionRing R d.Carrier K L
  have : IsLocalization (⊥ : Ideal d.Carrier).primeCompl L :=
    IsLocalization.of_le M _
      (by
        rw [Ideal.primeCompl_bot]
        exact map_le_nonZeroDivisors_of_injective _ hinj le_rfl)
      (by
        intro x hx
        apply isUnit_iff_ne_zero.mpr
        change (x : L) ≠ 0
        exact fun h => hx (Subtype.ext h))
  have : Algebra.FormallyEtale R K := Algebra.FormallyEtale.of_isLocalization R⁰
  have : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  have : Algebra.FormallyEtale R L := Algebra.FormallyEtale.comp R K L
  exact Algebra.FormallyEtale.of_equiv
    ((IsLocalization.algEquiv (⊥ : Ideal d.Carrier).primeCompl
      (Localization.AtPrime (⊥ : Ideal d.Carrier)) L).restrictScalars R).symm

/-- Shrinking the original base, rather than only the model, makes the actual
localized domain model etale over the original base. -/
theorem exists_etale_away_base (d : FiniteSeparablePolynomialModel R K L)
    [Algebra.IsAlgebraic K L] [Algebra.IsSeparable K L] :
    ∃ r : R, r ≠ 0 ∧
      Algebra.Etale R (Localization.Away (algebraMap R d.Carrier r)) := by
  have := d.isEtaleAt_bot
  obtain ⟨f, hf, hfe⟩ := Algebra.exists_etale_of_isEtaleAt (R := R) (⊥ : Ideal d.Carrier)
  have hf0 : f ≠ 0 := by simpa using hf
  have : Module.Finite R d.Carrier := d.toFiniteSeparableIntegralModel.finite
  obtain ⟨r, hr, hdvd⟩ := (Algebra.IsIntegral.isIntegral (R := R) f).isAlgebraic.exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero hf0)
  refine ⟨r, hr, Algebra.basicOpen_subset_etaleLocus_iff_etale.mp ?_⟩
  intro q hq
  apply Algebra.basicOpen_subset_etaleLocus_iff_etale.mpr hfe
  exact fun h => hq (q.asIdeal.mem_of_dvd hdvd h)

/-- The actual scalar extension of the polynomial model to a principal open
of the original base. -/
abbrev AwayCarrier (d : FiniteSeparablePolynomialModel R K L) (r : R) :=
  Localization.Away r ⊗[R] d.Carrier

instance awayFinite (d : FiniteSeparablePolynomialModel R K L) (r : R) :
    Module.Finite (Localization.Away r) (d.AwayCarrier r) := by
  have : Module.Finite R d.Carrier := d.toFiniteSeparableIntegralModel.finite
  infer_instance

instance awayFree (d : FiniteSeparablePolynomialModel R K L) (r : R) :
    Module.Free (Localization.Away r) (d.AwayCarrier r) := by
  infer_instance

/-- The scalar extension is finite free and etale after inverting a nonzero
element of the original base. -/
theorem exists_etale_away (d : FiniteSeparablePolynomialModel R K L)
    [Algebra.IsAlgebraic K L] [Algebra.IsSeparable K L] :
    ∃ r : R, r ≠ 0 ∧ Algebra.Etale (Localization.Away r) (d.AwayCarrier r) := by
  obtain ⟨r, hr, he⟩ := d.exists_etale_away_base
  let : Algebra d.Carrier (d.AwayCarrier r) := Algebra.TensorProduct.rightAlgebra
  have e := IsLocalization.Away.tensorRightEquiv (r := r)
    (A := Localization.Away r) d.Carrier
  have : Algebra.Etale R (d.AwayCarrier r) :=
    Algebra.Etale.of_equiv (e.restrictScalars R).symm
  have : Algebra.Etale R (Localization.Away r) := Algebra.Etale.of_isLocalizationAway r
  exact ⟨r, hr, Algebra.Etale.of_restrictScalars R (Localization.Away r) (d.AwayCarrier r)⟩

end FiniteSeparablePolynomialModel

variable (R K L)

/-- A polynomial model together with a proved principal shrinking on which its
actual base change is finite free and etale. -/
structure FiniteSeparableEtaleModel extends FiniteSeparablePolynomialModel R K L where
  denominator : R
  denominator_ne_zero : denominator ≠ 0
  etale : Algebra.Etale (Localization.Away denominator)
    (toFiniteSeparablePolynomialModel.AwayCarrier denominator)

/-- Construct a finite free etale model of the specified finite separable
fraction-field extension after shrinking the original domain. -/
noncomputable def finiteSeparableEtaleModel
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    FiniteSeparableEtaleModel R K L := by
  let d := finiteSeparablePolynomialModel R K L
  let h := d.exists_etale_away
  exact ⟨d, Classical.choose h, (Classical.choose_spec h).1, (Classical.choose_spec h).2⟩

namespace FiniteSeparableEtaleModel

variable {R K L}

/-- The principal localization of the original base. -/
abbrev Base (d : FiniteSeparableEtaleModel R K L) :=
  Localization.Away d.denominator

/-- The actual base change of the monogenic subalgebra. -/
abbrev Carrier (d : FiniteSeparableEtaleModel R K L) :=
  d.toFiniteSeparablePolynomialModel.AwayCarrier d.denominator

instance baseIsDomain (d : FiniteSeparableEtaleModel R K L) : IsDomain d.Base :=
  IsLocalization.Away.isDomain d.Base d.denominator_ne_zero

instance carrierIsDomain (d : FiniteSeparableEtaleModel R K L) : IsDomain d.Carrier := by
  let A := d.toFiniteSeparablePolynomialModel.Carrier
  let : Algebra A d.Carrier := Algebra.TensorProduct.rightAlgebra
  apply IsLocalization.Away.isDomain d.Carrier (x := algebraMap R A d.denominator)
  intro h
  exact d.denominator_ne_zero
    ((algebraMap_injective_of_field_isFractionRing R A K L)
      (h.trans (map_zero (algebraMap R A)).symm))

instance finite (d : FiniteSeparableEtaleModel R K L) :
    Module.Finite d.Base d.Carrier :=
  d.toFiniteSeparablePolynomialModel.awayFinite d.denominator

instance free (d : FiniteSeparableEtaleModel R K L) :
    Module.Free d.Base d.Carrier :=
  d.toFiniteSeparablePolynomialModel.awayFree d.denominator

instance isEtale (d : FiniteSeparableEtaleModel R K L) :
    Algebra.Etale d.Base d.Carrier := d.etale

/-- The original fraction-field map extends over the chosen base localization. -/
noncomputable def baseToFractionField (d : FiniteSeparableEtaleModel R K L) :
    d.Base →ₐ[R] K :=
  IsLocalization.Away.liftAlgHom (f := Algebra.ofId R K) d.denominator
    (isUnit_iff_ne_zero.mpr fun h => d.denominator_ne_zero
      ((IsFractionRing.injective R K) (h.trans (map_zero (algebraMap R K)).symm)))

noncomputable instance fractionAlgebra (d : FiniteSeparableEtaleModel R K L) :
    Algebra d.Base K :=
  d.baseToFractionField.toRingHom.toAlgebra

instance fractionTower (d : FiniteSeparableEtaleModel R K L) :
    IsScalarTower R d.Base K :=
  IsScalarTower.of_algHom d.baseToFractionField

/-- The generic fibre is the specified extension with its original
`K`-algebra structure. -/
noncomputable def genericEquiv (d : FiniteSeparableEtaleModel R K L)
    [Algebra.IsAlgebraic K L] : K ⊗[d.Base] d.Carrier ≃ₐ[K] L :=
  (Algebra.TensorProduct.cancelBaseChange R d.Base K K
    d.toFiniteSeparablePolynomialModel.Carrier).trans
      d.toFiniteSeparableIntegralModel.genericEquiv

omit [IsDomain R] in
@[simp]
theorem genericEquiv_tmul (d : FiniteSeparableEtaleModel R K L)
    [Algebra.IsAlgebraic K L] (k : K) (s : d.Base)
    (a : d.toFiniteSeparablePolynomialModel.Carrier) :
    d.genericEquiv (k ⊗ₜ[d.Base] (s ⊗ₜ[R] a)) =
      algebraMap K L (algebraMap d.Base K s * k) * (a : L) := by
  simp [genericEquiv, Algebra.smul_def]

end FiniteSeparableEtaleModel

end Langlands.CommutativeAlgebra
