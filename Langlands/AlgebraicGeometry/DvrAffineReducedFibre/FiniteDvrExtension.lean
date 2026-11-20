import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.FiniteNormalization
import Langlands.CommutativeAlgebra.DvrFiniteSeparableExtension
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.AdicPowerCompletenessProof
import Mathlib.FieldTheory.PurelyInseparable.Tower
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-! # Finite field extensions of the complete DVR base -/

open IsLocalRing
open Langlands.CommutativeAlgebra.DvrFiniteSeparableExtension
  (isDiscreteValuationRing_and_isAdicComplete)
open Langlands.NYLL.ValuationTheory.DiscreteValuationField
  (isAdicComplete_of_isAdicComplete_pow)

noncomputable section

universe u

namespace Langlands.AlgebraicGeometry.DvrAffineReducedFibre

section Basis

variable {R : Type*} {K : Type*} {L : Type*} [CommRing R] [IsDomain R]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra R L] [Algebra K L] [IsScalarTower R K L]

/-- The algebra generated over `R` by a basis of `L` over its fraction field
has fraction field `L`. -/
def basisAdjoinFractionEquiv {ι : Type*} (b : Module.Basis ι K L) :
    let C := Algebra.adjoin R (Set.range b)
    FractionRing C ≃ₐ[C] L := by
  let C := Algebra.adjoin R (Set.range b)
  let f : FractionRing C →ₐ[C] L := IsFractionRing.liftAlgHom
    (g := Algebra.ofId C L) Subtype.val_injective
  have hC (x : L) (hx : x ∈ C) : x ∈ f.toRingHom.fieldRange :=
    RingHom.mem_fieldRange.mpr ⟨algebraMap C (FractionRing C) ⟨x, hx⟩, f.commutes ⟨x, hx⟩⟩
  have hK (k : K) : algebraMap K L k ∈ f.toRingHom.fieldRange := by
    obtain ⟨a, d, _, rfl⟩ := IsFractionRing.div_surjective R k
    rw [map_div₀, ← IsScalarTower.algebraMap_apply R K L, ← IsScalarTower.algebraMap_apply R K L]
    exact f.toRingHom.fieldRange.div_mem (hC _ (C.algebraMap_mem a))
      (hC _ (C.algebraMap_mem d))
  let M : Submodule K L :=
    { f.toRingHom.fieldRange.toAddSubgroup with
      smul_mem' := fun k x hx => by
        change k • x ∈ f.toRingHom.fieldRange
        rw [Algebra.smul_def]
        exact f.toRingHom.fieldRange.mul_mem (hK k) hx }
  have hM : M = ⊤ := top_unique (by
    rw [← b.span_eq]
    exact Submodule.span_le.mpr fun x hx => hC x (Algebra.subset_adjoin hx))
  refine AlgEquiv.ofBijective f ⟨f.injective, ?_⟩
  intro x
  apply RingHom.mem_fieldRange.mp
  change x ∈ M
  rw [hM]
  trivial

end Basis

section CompleteDvr

variable (R L : Type u) [CommRing R] [IsDomain R]
    [Field L] [Algebra R L] [Algebra (FractionRing R) L] [IsScalarTower R (FractionRing R) L]

local notation "K" => FractionRing R
local notation "B" => integralClosure R L

private theorem scalar_injective : Function.Injective (algebraMap R L) := by
  rw [IsScalarTower.algebraMap_eq R K L]
  exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)

private theorem faithfulSMul_integralClosure : FaithfulSMul R B :=
  (faithfulSMul_iff_algebraMap_injective R B).mpr fun a b h =>
    scalar_injective R L (show algebraMap R L a = algebraMap R L b from
      congrArg (fun z : B => z.val) h)

variable [IsDiscreteValuationRing R] [IsAdicComplete (maximalIdeal R) R]
    [FiniteDimensional (FractionRing R) L]

/-- Over a complete DVR with perfect residue field, integral closure in any
finite fraction-field extension is finite. -/
theorem finite_integralClosure_of_finiteExtension [PerfectField (ResidueField R)] :
    Module.Finite R B := by
  obtain ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral R K L
  let C := Algebra.adjoin R (Set.range b)
  have hfinC : Module.Finite R C := Algebra.finite_adjoin_of_finite_of_isIntegral
    (Set.finite_range b) (by rintro _ ⟨i, rfl⟩; exact hb i)
  have hinjC : Function.Injective (algebraMap R C) := fun a b h =>
    scalar_injective R L (show algebraMap R L a = algebraMap R L b from
      congrArg (fun z : C => z.val) h)
  have hfinite : Module.Finite C (integralClosure C (FractionRing C)) :=
    finite_normalization_of_completeDvr_of_isDomain R C hinjC
  let e : FractionRing C ≃ₐ[C] L := basisAdjoinFractionEquiv (R := R) b
  have : Module.Finite C (integralClosure C L) := Module.Finite.equiv
    e.mapIntegralClosure.toLinearEquiv
  have : Module.Finite R (integralClosure C L) := Module.Finite.trans C _
  have hsame : B = (integralClosure C L).restrictScalars R := by
    ext x
    change IsIntegral R x ↔ IsIntegral C x
    exact ⟨IsIntegral.tower_top, isIntegral_trans (R := R) (A := ↥C) x⟩
  exact hsame ▸ inferInstanceAs (Module.Finite R (integralClosure C L))

private theorem isLocalRing_integralClosure_of_finiteExtension : IsLocalRing B := by
  let S := separableClosure K L
  let C := integralClosure R S
  have : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨hDvr, _⟩ := isDiscreteValuationRing_and_isAdicComplete R S
  have : IsLocalRing C := inferInstance
  let g : S →ₐ[R] L := IsScalarTower.toAlgHom R S L
  let f : C →ₐ[R] B := g.mapIntegralClosure
  let : Algebra C B := f.toRingHom.toAlgebra
  have : IsScalarTower R C B := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  have : Algebra.IsIntegral C B := ⟨fun x => (Algebra.IsIntegral.isIntegral (R := R) x).tower_top⟩
  let p := ringExpChar K
  let n := IsPurelyInseparable.exponent S L
  let F : L →+* S := IsPurelyInseparable.iterateFrobenius S L p (le_refl n)
  have hpow (x : B) : ∃ y : C, f y = x ^ p ^ n := by
    have he : g (F x.val) = x.val ^ p ^ n :=
      IsPurelyInseparable.algebraMap_iterateFrobenius S p (le_refl n) x.val
    have hy : IsIntegral R (F x.val) := (isIntegral_algHom_iff g g.injective).mp
      (he.symm ▸ x.property.pow _)
    exact ⟨⟨_, hy⟩, Subtype.ext he⟩
  have : Subsingleton (MaximalSpectrum B) := by
    constructor
    intro q q'
    have hq : (q.asIdeal.under C).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal _
    have hq' : (q'.asIdeal.under C).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal _
    have he : q.asIdeal.under C = q'.asIdeal.under C :=
      (eq_maximalIdeal hq).trans (eq_maximalIdeal hq').symm
    apply MaximalSpectrum.ext
    ext x
    obtain ⟨y, hy⟩ := hpow x
    have hm : x ^ p ^ n ∈ q.asIdeal ↔ x ^ p ^ n ∈ q'.asIdeal := by
      rw [← hy]
      change y ∈ q.asIdeal.under C ↔ y ∈ q'.asIdeal.under C
      rw [he]
    have hn : 0 < p ^ n := pow_pos (Nat.pos_of_ne_zero (expChar_ne_zero K p)) n
    exact (q.isMaximal.isPrime.pow_mem_iff_mem _ hn).symm.trans
      (hm.trans (q'.isMaximal.isPrime.pow_mem_iff_mem _ hn))
  exact IsLocalRing.of_singleton_maximalSpectrum

/-- The integral closure of a complete DVR with perfect residue field in a
finite extension is a complete DVR. -/
theorem isDiscreteValuationRing_and_isAdicComplete_of_finiteExtension
    [PerfectField (ResidueField R)] :
    ∃ _ : IsDiscreteValuationRing B, IsAdicComplete (maximalIdeal B) B := by
  have hfin : Module.Finite R B := finite_integralClosure_of_finiteExtension R L
  have : IsLocalRing B := isLocalRing_integralClosure_of_finiteExtension R L
  have : IsNoetherianRing B := IsNoetherianRing.of_finite R B
  have : IsIntegrallyClosed B := IsIntegrallyClosed.of_isIntegrallyClosedIn B L
  have hDedekind : IsDedekindDomain B := {}
  have : FaithfulSMul R B := faithfulSMul_integralClosure R L
  have hinj := FaithfulSMul.algebraMap_injective R B
  have hn : ¬IsField B := fun h => IsDiscreteValuationRing.not_isField R
    (isField_of_isIntegral_of_isField hinj h)
  have : IsDiscreteValuationRing B := ((IsDiscreteValuationRing.TFAE B hn).out 3 1).mp hDedekind
  refine ⟨inferInstance, ?_⟩
  let I := (maximalIdeal R).map (algebraMap R B)
  have hI : IsAdicComplete I B := (IsAdicComplete.map_algebraMap_iff (maximalIdeal R) B).mpr
    (IsAdicComplete.of_finite_of_isNoetherianRing _ _)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible B
  have hπB : algebraMap R B π ≠ 0 := (map_ne_zero_iff _ hinj).mpr hπ.ne_zero
  obtain ⟨n, u, hpow⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hπB ht
  have heq : I = maximalIdeal B ^ n := by
    rw [show I = (maximalIdeal R).map (algebraMap R B) from rfl, hπ.maximalIdeal_eq,
      Ideal.map_span, Set.image_singleton, hpow, ht.maximalIdeal_eq, Ideal.span_singleton_pow,
      Ideal.span_singleton_eq_span_singleton]
    exact associated_unit_mul_left _ _ u.isUnit
  have : IsLocalHom (algebraMap R B) := (inferInstance : Algebra.IsIntegral R B).isLocalHom
  have hle : I ≤ maximalIdeal B := ((local_hom_TFAE (algebraMap R B)).out 1 3 rfl rfl).mp inferInstance
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    exact (maximalIdeal.isMaximal B).ne_top (top_le_iff.mp (by simpa [heq, hn0] using hle))
  have : IsAdicComplete (maximalIdeal B ^ n) B := heq ▸ hI
  exact isAdicComplete_of_isAdicComplete_pow B B (maximalIdeal B) hn

/-- In a finite extension of the complete DVR, an algebraically closed residue
field is preserved. -/
def residueEquiv_of_finiteExtension [IsAlgClosed (ResidueField R)] [IsDiscreteValuationRing B] :
    ResidueField R ≃+* ResidueField B := by
  have : FaithfulSMul R B := faithfulSMul_integralClosure R L
  have : IsLocalHom (algebraMap R B) := (inferInstance : Algebra.IsIntegral R B).isLocalHom
  have : Module.Finite R B := finite_integralClosure_of_finiteExtension R L
  exact RingEquiv.ofBijective (algebraMap (ResidueField R) (ResidueField B))
    IsAlgClosed.algebraMap_bijective_of_isIntegral

end CompleteDvr

end Langlands.AlgebraicGeometry.DvrAffineReducedFibre
