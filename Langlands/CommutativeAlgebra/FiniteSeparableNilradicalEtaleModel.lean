import Langlands.CommutativeAlgebra.FiniteSeparableNilradicalModel
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Etale.Field

/-! # Etale shrinking of a finite free model over an irreducible ring -/

noncomputable section

universe u v w

open scoped TensorProduct
open Algebra Polynomial

namespace Langlands.CommutativeAlgebra

/-- A monic polynomial quotient becomes etale after inverting its derivative. -/
theorem etale_away_adjoinRoot_derivative
    {R : Type u} [CommRing R] (p : R[X]) (hp : p.Monic) :
    Algebra.Etale R (Localization.Away (AdjoinRoot.mk p p.derivative)) := by
  let P : StandardEtalePair R :=
    ⟨p, hp, p.derivative, 1, 0, 1, by simp⟩
  exact Algebra.Etale.of_equiv P.equivAwayAdjoinRoot

variable (R : Type u) (K : Type v) (L : Type w)
  [CommRing R] [IrreducibleSpace (PrimeSpectrum R)] [Field K] [Field L]

local instance etaleNilradicalIsPrime : (nilradical R).IsPrime :=
  PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp inferInstance

variable [Algebra (R ⧸ nilradical R) K] [IsFractionRing (R ⧸ nilradical R) K]
  [Algebra (R ⧸ nilradical R) L] [Algebra K L]
  [IsScalarTower (R ⧸ nilradical R) K L]
  [Algebra R K] [IsScalarTower R (R ⧸ nilradical R) K]

namespace FiniteSeparableNilradicalModel

variable {R K L}

/-- The derivative of the actual lifted defining polynomial does not vanish at
the generic prime, because its image is the derivative of a separable minpoly. -/
theorem derivative_notMem_genericPrime (d : FiniteSeparableNilradicalModel R K L)
    [Algebra.IsAlgebraic K L] [Algebra.IsSeparable K L] :
    AdjoinRoot.mk d.polynomial d.polynomial.derivative ∉ d.genericPrime.asIdeal := by
  have hcoeff : d.genericMap.comp (algebraMap R d.Carrier) =
      (algebraMap K L).comp (algebraMap R K) := by
    ext r
    rw [RingHom.comp_apply, AdjoinRoot.algebraMap_eq, d.genericMap_of,
      RingHom.comp_apply, IsScalarTower.algebraMap_apply R (R ⧸ nilradical R) K,
      ← IsScalarTower.algebraMap_apply (R ⧸ nilradical R) K L]
  have hne : d.genericMap (AdjoinRoot.mk d.polynomial d.polynomial.derivative) ≠ 0 := by
    rw [← AdjoinRoot.aeval_eq]
    change d.genericMap (d.polynomial.derivative.eval₂ (algebraMap R d.Carrier)
      (AdjoinRoot.root d.polynomial)) ≠ 0
    rw [Polynomial.hom_eval₂, hcoeff, d.genericMap_root,
      ← Polynomial.eval₂_map, ← Polynomial.derivative_map, d.map_eq_minpoly]
    exact (Algebra.IsSeparable.isSeparable K d.quotientModel.generator).aeval_derivative_ne_zero
      (minpoly.aeval K _)
  intro h
  apply hne
  change d.reductionMap (AdjoinRoot.mk d.polynomial d.polynomial.derivative) = 0 at h
  rw [d.genericMap_eq_reductionMap, RingHom.comp_apply, h, map_zero]

/-- The actual finite free model is etale at its specified generic prime. -/
theorem isEtaleAt_genericPrime (d : FiniteSeparableNilradicalModel R K L)
    [Algebra.IsAlgebraic K L] [Algebra.IsSeparable K L] :
    Algebra.IsEtaleAt R d.genericPrime.asIdeal := by
  have he := etale_away_adjoinRoot_derivative d.polynomial d.monic
  exact (Algebra.basicOpen_subset_etaleLocus_iff_etale.mpr he)
    d.derivative_notMem_genericPrime

/-- Remove the closed image of the non-etale locus in the original base.
The denominator avoids the prime nilradical even when the base is nonreduced. -/
theorem exists_etale_away_base (d : FiniteSeparableNilradicalModel R K L)
    [Algebra.IsAlgebraic K L] [Algebra.IsSeparable K L] :
    ∃ r : R, r ∉ nilradical R ∧
      Algebra.Etale R (Localization.Away (algebraMap R d.Carrier r)) := by
  let f := PrimeSpectrum.comap (algebraMap R d.Carrier)
  let Z := (Algebra.etaleLocus R d.Carrier)ᶜ
  let p : PrimeSpectrum R := ⟨nilradical R, inferInstance⟩
  have hZ : IsClosed (f '' Z) :=
    PrimeSpectrum.isClosedMap_comap_of_isIntegral (algebraMap R d.Carrier)
      (fun a => Algebra.IsIntegral.isIntegral a) Z Algebra.isOpen_etaleLocus.isClosed_compl
  have hp : p ∈ (f '' Z)ᶜ := by
    rintro ⟨q, hq, heq⟩
    have hu : q.asIdeal.under R = nilradical R :=
      congrArg PrimeSpectrum.asIdeal heq
    have hq' := d.prime_eq_genericPrime q hu
    subst q
    exact hq d.isEtaleAt_genericPrime
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hr, hsub⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hp hZ.isOpen_compl
  refine ⟨r, hr, Algebra.basicOpen_subset_etaleLocus_iff_etale.mp ?_⟩
  intro q hq
  by_contra hn
  have hmem : f q ∈ PrimeSpectrum.basicOpen r := hq
  exact hsub hmem ⟨q, hn, rfl⟩

/-- The actual scalar extension to a principal open of the original ring. -/
abbrev AwayCarrier (d : FiniteSeparableNilradicalModel R K L) (r : R) :=
  Localization.Away r ⊗[R] d.Carrier

instance awayFinite (d : FiniteSeparableNilradicalModel R K L) (r : R) :
    Module.Finite (Localization.Away r) (d.AwayCarrier r) := by
  infer_instance

instance awayFree (d : FiniteSeparableNilradicalModel R K L) (r : R) :
    Module.Free (Localization.Away r) (d.AwayCarrier r) := by
  infer_instance

/-- Actual base change to a nonempty principal open is finite free and etale. -/
theorem exists_etale_away (d : FiniteSeparableNilradicalModel R K L)
    [Algebra.IsAlgebraic K L] [Algebra.IsSeparable K L] :
    ∃ r : R, r ∉ nilradical R ∧
      Algebra.Etale (Localization.Away r) (d.AwayCarrier r) := by
  obtain ⟨r, hr, he⟩ := d.exists_etale_away_base
  let : Algebra d.Carrier (d.AwayCarrier r) := Algebra.TensorProduct.rightAlgebra
  have e := IsLocalization.Away.tensorRightEquiv (r := r)
    (A := Localization.Away r) d.Carrier
  have : Algebra.Etale R (d.AwayCarrier r) :=
    Algebra.Etale.of_equiv (e.restrictScalars R).symm
  have : Algebra.Etale R (Localization.Away r) := Algebra.Etale.of_isLocalizationAway r
  exact ⟨r, hr, Algebra.Etale.of_restrictScalars R (Localization.Away r) (d.AwayCarrier r)⟩

end FiniteSeparableNilradicalModel

/-- An actual lifted model and a proved nonempty principal shrinking of the
original base on which its scalar extension is etale. -/
structure FiniteSeparableNilradicalEtaleModel extends
    toFiniteSeparableNilradicalModel : FiniteSeparableNilradicalModel R K L where
  denominator : R
  denominator_notMem : denominator ∉ nilradical R
  etale : Algebra.Etale (Localization.Away denominator)
    (FiniteSeparableNilradicalModel.AwayCarrier toFiniteSeparableNilradicalModel denominator)

/-- Construct the finite free etale model over an arbitrary irreducible ring. -/
def finiteSeparableNilradicalEtaleModel
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    FiniteSeparableNilradicalEtaleModel R K L := by
  let d := finiteSeparableNilradicalModel R K L
  let h := d.exists_etale_away
  exact ⟨d, Classical.choose h, (Classical.choose_spec h).1, (Classical.choose_spec h).2⟩

namespace FiniteSeparableNilradicalEtaleModel

variable {R K L}

/-- The actual principal localization of the original base. -/
abbrev Base (d : FiniteSeparableNilradicalEtaleModel R K L) :=
  Localization.Away d.denominator

/-- The actual finite free scalar extension of the lifted polynomial quotient. -/
abbrev Carrier (d : FiniteSeparableNilradicalEtaleModel R K L) :=
  FiniteSeparableNilradicalModel.AwayCarrier d.toFiniteSeparableNilradicalModel d.denominator

instance finite (d : FiniteSeparableNilradicalEtaleModel R K L) :
    Module.Finite d.Base d.Carrier :=
  FiniteSeparableNilradicalModel.awayFinite d.toFiniteSeparableNilradicalModel d.denominator

instance free (d : FiniteSeparableNilradicalEtaleModel R K L) :
    Module.Free d.Base d.Carrier :=
  FiniteSeparableNilradicalModel.awayFree d.toFiniteSeparableNilradicalModel d.denominator

instance isEtale (d : FiniteSeparableNilradicalEtaleModel R K L) :
    Algebra.Etale d.Base d.Carrier := d.etale

omit [IrreducibleSpace (PrimeSpectrum R)] [IsScalarTower (R ⧸ nilradical R) K L] in
/-- The chosen denominator has nonzero image in the specified generic field. -/
theorem denominator_map_ne_zero (d : FiniteSeparableNilradicalEtaleModel R K L) :
    algebraMap R K d.denominator ≠ 0 := by
  rw [IsScalarTower.algebraMap_apply R (R ⧸ nilradical R) K,
    map_ne_zero_iff _ (IsFractionRing.injective (R ⧸ nilradical R) K)]
  exact fun h => d.denominator_notMem (Ideal.Quotient.eq_zero_iff_mem.mp h)

/-- The original generic-field map extends to the chosen base localization. -/
def baseToFractionField (d : FiniteSeparableNilradicalEtaleModel R K L) :
    d.Base →ₐ[R] K :=
  IsLocalization.Away.liftAlgHom (f := Algebra.ofId R K) d.denominator
    (isUnit_iff_ne_zero.mpr d.denominator_map_ne_zero)

instance fractionAlgebra (d : FiniteSeparableNilradicalEtaleModel R K L) :
    Algebra d.Base K := d.baseToFractionField.toRingHom.toAlgebra

instance fractionTower (d : FiniteSeparableNilradicalEtaleModel R K L) :
    IsScalarTower R d.Base K :=
  IsScalarTower.of_algHom d.baseToFractionField

/-- The generic base change retains the originally specified field extension. -/
def genericEquiv (d : FiniteSeparableNilradicalEtaleModel R K L)
    [Algebra.IsAlgebraic K L] : K ⊗[d.Base] d.Carrier ≃ₐ[K] L :=
  (Algebra.TensorProduct.cancelBaseChange R d.Base K K
    d.toFiniteSeparableNilradicalModel.Carrier).trans
      d.toFiniteSeparableNilradicalModel.genericEquiv

omit [IrreducibleSpace (PrimeSpectrum R)] [IsScalarTower (R ⧸ nilradical R) K L] in
@[simp]
theorem genericEquiv_tmul (d : FiniteSeparableNilradicalEtaleModel R K L)
    [Algebra.IsAlgebraic K L] (k : K) (s : d.Base)
    (a : d.toFiniteSeparableNilradicalModel.Carrier) :
    d.genericEquiv (k ⊗ₜ[d.Base] (s ⊗ₜ[R] a)) =
      algebraMap K L (algebraMap d.Base K s * k) *
        d.toFiniteSeparableNilradicalModel.genericMap a := by
  simp only [genericEquiv, AlgEquiv.trans_apply,
    Algebra.TensorProduct.cancelBaseChange_tmul]
  simpa [FiniteSeparableLiftedPolynomialModel.genericMap,
    TensorProduct.smul_tmul', Algebra.smul_def] using
      d.toFiniteSeparableNilradicalModel.genericEquiv.toLinearEquiv.map_smul (s • k) (1 ⊗ₜ[R] a)

end FiniteSeparableNilradicalEtaleModel

end Langlands.CommutativeAlgebra
