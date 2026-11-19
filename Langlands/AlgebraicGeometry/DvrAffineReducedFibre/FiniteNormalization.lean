import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.ClosedFibreChart
import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.FiniteFrobenius
import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.TotalFractions
import Langlands.AlgebraicGeometry.NoetherianApproximation.InseparableNormalization
import Langlands.AlgebraicGeometry.NoetherianApproximation.NormalizationLocalization
import Langlands.AlgebraicGeometry.Picard.DiscreteValuationRingSelfProductLineBundleExtensionProof
import Langlands.AlgebraicGeometry.SmoothReducedProof
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.RingHom.Finite

/-! # Finiteness of normalization over a complete DVR -/

open IsLocalRing TensorProduct
open Langlands.AlgebraicGeometry.NoetherianApproximation

noncomputable section

universe u v w

namespace Langlands.AlgebraicGeometry.DvrAffineReducedFibre

private theorem finite_frobenius_of_finiteType (R : Type u) (A : Type v)
    [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (p : ℕ) [ExpChar R p] [ExpChar A p] (hR : (frobenius R p).Finite) :
    (frobenius A p).Finite := by
  have hint : (frobenius A p).IsIntegral := by
    intro x
    refine ⟨Polynomial.X ^ p - Polynomial.C x,
      Polynomial.monic_X_pow_sub_C x (expChar_ne_zero A p), ?_⟩
    simp [frobenius_def]
  have hcomp : (frobenius A p).comp (algebraMap R A) =
      (algebraMap R A).comp (frobenius R p) := by
    ext r
    exact (map_pow (algebraMap R A) r p).symm
  have htype : ((frobenius A p).comp (algebraMap R A)).FiniteType := by
    rw [hcomp]
    exact (RingHom.finiteType_algebraMap.mpr inferInstance).comp hR.finiteType
  exact hint.to_finite (RingHom.FiniteType.of_comp_finiteType htype)

private theorem finite_iterateFrobenius_of_finite (R : Type u) [CommRing R]
    (p : ℕ) [ExpChar R p] (hf : (frobenius R p).Finite) (n : ℕ) :
    (iterateFrobenius R p n).Finite := by
  induction n with
  | zero =>
    rw [iterateFrobenius_zero]
    exact RingHom.Finite.of_surjective _ Function.surjective_id
  | succ n ih =>
    rw [iterateFrobenius_add, iterateFrobenius_one]
    exact ih.comp hf

private theorem finite_frobenius_of_completeDvr (R : Type u) [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] [IsAdicComplete (maximalIdeal R) R]
    [PerfectField (ResidueField R)] (p : ℕ) [hp : ExpChar R p] :
    (frobenius R p).Finite := by
  rcases hp with ⟨_⟩ | ⟨hprime⟩
  · have h : frobenius R 1 = RingHom.id R := RingHom.ext fun x => pow_one x
    rw [h]
    exact RingHom.Finite.of_surjective _ Function.surjective_id
  · have : Fact p.Prime := ⟨hprime⟩
    exact finite_frobenius_of_isAdicComplete R p

private theorem finite_frobenius_fractionRing (R : Type u) [CommRing R] [IsDomain R]
    (p : ℕ) [ExpChar R p] [ExpChar (FractionRing R) p] (hF : (frobenius R p).Finite) :
    (frobenius (FractionRing R) p).Finite := by
  let K := FractionRing R
  let M := nonZeroDivisors R
  let f := frobenius R p
  have hle : M.map f ≤ M := map_le_nonZeroDivisors_of_injective f (frobenius_inj R p) le_rfl
  have hex (r : R) (hr : r ∈ M) : ∃ s ∈ M.map f, r ∣ s :=
    ⟨f r, ⟨r, hr, rfl⟩, dvd_pow_self r (expChar_ne_zero R p)⟩
  have : IsLocalization (M.map f) K :=
    (IsLocalization.iff_of_le_of_exists_dvd (S := K) (M.map f) M hle hex).mpr inferInstance
  have heq : IsLocalization.map K f (Submonoid.le_comap_map M) = frobenius K p := by
    apply IsLocalization.ringHom_ext M
    apply RingHom.ext
    intro r
    rw [RingHom.comp_apply, RingHom.comp_apply, IsLocalization.map_eq]
    exact map_pow (algebraMap R K) r p
  rw [← heq]
  exact RingHom.finite_localizationPreserves f M K K hF

private theorem finite_integralClosure_of_normal_base (R : Type u) (K : Type v) (L : Type w)
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra R L] [Algebra K L] [IsScalarTower R K L] [FiniteDimensional K L]
    (hFrob : ∀ (p : ℕ) [ExpChar R p], (frobenius R p).Finite) :
    Module.Finite R (integralClosure R L) := by
  let S := separableClosure K L
  let p := ringExpChar K
  have : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : ExpChar R p := (algebraMap R K).expChar (IsFractionRing.injective R K) p
  let n := IsPurelyInseparable.exponent S L
  let F : L →+* S := IsPurelyInseparable.iterateFrobenius S L p (le_refl n)
  have hF (x : L) : algebraMap S L (F x) = x ^ p ^ n :=
    IsPurelyInseparable.algebraMap_iterateFrobenius S p (le_refl n) x
  let G : integralClosure R L →+* integralClosure R S :=
    (F.comp (integralClosure R L).val.toRingHom).codRestrict
      (integralClosure R S).toSubring fun x ↦ by
        apply (isIntegral_algHom_iff (IsScalarTower.toAlgHom R S L)
          (algebraMap S L).injective).mp
        change IsIntegral R (algebraMap S L (F x.val))
        rw [hF]
        exact x.property.pow _
  have hG : Function.Injective G := by
    intro x y h
    apply Subtype.ext
    exact F.injective (congrArg Subtype.val h)
  have hcomp : G.comp (algebraMap R (integralClosure R L)) =
      (algebraMap R (integralClosure R S)).comp (iterateFrobenius R p n) := by
    apply RingHom.ext
    intro r
    apply Subtype.ext
    apply (algebraMap S L).injective
    change algebraMap S L (F (algebraMap R L r)) =
      algebraMap S L (algebraMap R S (iterateFrobenius R p n r))
    rw [hF, ← IsScalarTower.algebraMap_apply R S L,
      iterateFrobenius_def, map_pow]
  have hsep : Module.Finite R (integralClosure R S) :=
    IsIntegralClosure.finite R K S (integralClosure R S)
  apply RingHom.finite_algebraMap.mp
  apply finite_of_finite_comp_of_injective _ G _ hG
  rw [hcomp]
  exact (RingHom.finite_algebraMap.mpr hsep).comp
    (finite_iterateFrobenius_of_finite R p (hFrob p) n)

private theorem finite_normalization_of_finite_polynomial_subbase (R : Type u)
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R]
    (hFrob : ∀ (p : ℕ) [ExpChar R p], (frobenius R p).Finite) (n : ℕ)
    (C : Type u) [CommRing C] [IsDomain C] [Algebra (MvPolynomial (Fin n) R) C]
    [FaithfulSMul (MvPolynomial (Fin n) R) C] [Module.Finite (MvPolynomial (Fin n) R) C] :
    Module.Finite C (integralClosure C (FractionRing C)) := by
  let B := MvPolynomial (Fin n) R
  let : Algebra (FractionRing B) (FractionRing C) :=
    FractionRing.liftAlgebra B (FractionRing C)
  have hF (p : ℕ) [ExpChar B p] : (frobenius B p).Finite := by
    have : ExpChar R p := (MvPolynomial.C (σ := Fin n)).expChar
      (MvPolynomial.C_injective (Fin n) R) p
    exact finite_frobenius_of_finiteType R B p (hFrob p)
  have : Module.Finite B (integralClosure B (FractionRing C)) :=
    finite_integralClosure_of_normal_base B (FractionRing B) (FractionRing C) hF
  let i : integralClosure C (FractionRing C) →ₐ[B] integralClosure B (FractionRing C) :=
    Subalgebra.inclusion
      (show (integralClosure C (FractionRing C)).restrictScalars B ≤
        integralClosure B (FractionRing C) from fun x hx ↦ isIntegral_trans (R := B) x hx)
  have : Module.Finite B (integralClosure C (FractionRing C)) :=
    Module.Finite.of_injective i.toLinearMap fun x y h =>
      Subtype.ext (congrArg (fun z : integralClosure B (FractionRing C) => z.val) h)
  exact Module.Finite.of_restrictScalars_finite B C _

private theorem finite_normalization_of_field (K A : Type u) [Field K]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A]
    (hFrob : ∀ (p : ℕ) [ExpChar K p], (frobenius K p).Finite) :
    Module.Finite A (integralClosure A (FractionRing A)) := by
  obtain ⟨n, f, hfi, hfin⟩ := exists_finite_inj_algHom_of_fg K A
  let B := MvPolynomial (Fin n) K
  let : Algebra B A := f.toRingHom.toAlgebra
  have : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).mpr hfi
  have : Module.Finite B A := RingHom.finite_algebraMap.mp hfin
  exact finite_normalization_of_finite_polynomial_subbase K hFrob n A

section DVR

variable (R A : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing A] [IsDomain A] [Algebra R A] [Algebra.FiniteType R A]
  [IsAdicComplete (maximalIdeal R) R] [PerfectField (ResidueField R)]

/-- A finite-type domain over a complete DVR with perfect residue field and
injective structure map has finite normalization in its fraction field. -/
theorem finite_normalization_of_completeDvr_of_isDomain
    (hRA : Function.Injective (algebraMap R A)) :
    Module.Finite A (integralClosure A (FractionRing A)) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let r := algebraMap R A π
  have hr : r ≠ 0 := (map_ne_zero_iff (algebraMap R A) hRA).mpr hπ.ne_zero
  apply finite_of_finite_localizations_near_maximal
  intro q hq
  by_cases hqr : r ∈ q
  · obtain ⟨⟨n, f, hfi, hqf⟩⟩ := nonempty_closedFibrePolynomialChart R A hRA hπ q hqr
    let B := MvPolynomial (Fin n) R
    let : Algebra B A := f.toRingHom.toAlgebra
    have : IsScalarTower R B A := IsScalarTower.of_algebraMap_eq fun r ↦ (f.commutes r).symm
    have : Algebra.FiniteType B A := Algebra.FiniteType.of_restrictScalars_finiteType R B A
    have : Algebra.QuasiFiniteAt B q := hqf
    obtain ⟨C, hC, s, hs, hbij⟩ :=
      Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective (R := B) q
    have : Module.Finite B C := ⟨(Submodule.fg_top _).mpr hC⟩
    have : FaithfulSMul B C := (faithfulSMul_iff_algebraMap_injective B C).mpr
      fun x y h ↦ hfi (congrArg (fun z : C ↦ z.val) h)
    have : Module.Finite C (integralClosure C (FractionRing C)) :=
      finite_normalization_of_finite_polynomial_subbase R
        (finite_frobenius_of_completeDvr R) n C
    exact ⟨s.val, hs, finite_normalization_localized_of_finite_subalgebra C s
      (fun h => hs (h ▸ q.zero_mem)) hbij⟩
  · refine ⟨r, hqr, ?_⟩
    let K := FractionRing A
    let U := Localization.Away r
    have : IsDomain U :=
      IsLocalization.isDomain_of_le_nonZeroDivisors U (powers_le_nonZeroDivisors_of_noZeroDivisors hr)
    have hu : IsUnit (algebraMap A K r) :=
      isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hr)
    let : Algebra U K := (IsLocalization.Away.lift r hu).toAlgebra
    have : IsScalarTower A U K := IsScalarTower.of_algebraMap_eq fun a ↦
      (IsLocalization.Away.lift_eq r hu a).symm
    have : IsLocalization.Away (algebraMap A K r) K :=
      IsLocalization.away_of_isUnit_of_bijective K hu Function.bijective_id
    have : IsFractionRing U K :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers r) U K
    have : IsLocalization.Away π (FractionRing R) :=
      isLocalizationAway_fractionRing_of_dvr R (FractionRing R) hπ
    let F := FractionRing R
    let T := A ⊗[R] F
    have : IsLocalization.Away r T := IsLocalization.Away.tensor (A := F) π
    let : Algebra F T := Algebra.TensorProduct.rightAlgebra
    let e := IsLocalization.algEquiv (Submonoid.powers r) T U
    let : Algebra F U := (e.toRingHom.comp (algebraMap F T)).toAlgebra
    let eF : T ≃ₐ[F] U := { e.toRingEquiv with commutes' := fun _ => rfl }
    have hTF : Algebra.FiniteType F (F ⊗[R] A) := inferInstance
    have : Algebra.FiniteType F U :=
      hTF.equiv ((Algebra.TensorProduct.commRight R F A).trans eF)
    have hF (p : ℕ) [ExpChar F p] : (frobenius F p).Finite := by
      have : ExpChar R p := (algebraMap R F).expChar (IsFractionRing.injective R F) p
      exact finite_frobenius_fractionRing R p (finite_frobenius_of_completeDvr R p)
    have : Module.Finite U (integralClosure U (FractionRing U)) :=
      finite_normalization_of_field F U hF
    have : Module.Finite U (integralClosure U K) :=
      Module.Finite.equiv
        (IsLocalization.algEquiv (nonZeroDivisors U) (FractionRing U) K).mapIntegralClosure.toLinearEquiv
    exact finite_localizedModule_integralClosure r

end DVR

section Components

variable (A : Type u) [CommRing A]

local notation "P" => minimalPrimes A
local notation "Aₚ" p => A ⧸ (p : P).1
local notation "Cₚ" p => integralClosure (Aₚ p) (FractionRing (Aₚ p))

private lemma componentDenominators_regular (p : P) (s : nonZeroDivisors A) :
    algebraMap A (Aₚ p) s ∈ nonZeroDivisors (Aₚ p) := by
  have : p.1.IsPrime := p.2.isPrime
  apply mem_nonZeroDivisors_iff_ne_zero.mpr
  intro h
  have hs : (s : A) ∈ p.1 := Ideal.Quotient.eq_zero_iff_mem.mp h
  exact Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes p.2) hs s.2

/-- The map from the total fraction ring to the fraction field of one minimal
prime quotient. -/
def totalFractionsToComponent (p : P) :
    FractionRing A →ₐ[A] FractionRing (Aₚ p) :=
  IsLocalization.liftAlgHom
    (f := Algebra.ofId A (FractionRing (Aₚ p))) fun s : nonZeroDivisors A => by
      change IsUnit (algebraMap A (FractionRing (Aₚ p)) s)
      rw [IsScalarTower.algebraMap_apply A (Aₚ p)]
      exact IsLocalization.map_units (M := nonZeroDivisors (Aₚ p)) (FractionRing (Aₚ p))
        ⟨_, componentDenominators_regular A p s⟩

/-- Map the integral closure in total fractions to the product of integral closures
in the fraction fields of the minimal prime quotients. -/
def normalizationToComponents :
    integralClosure A (FractionRing A) →ₐ[A] (∀ p : P, Cₚ p) where
  toFun x p := ⟨totalFractionsToComponent A p x, (x.property.map (totalFractionsToComponent A p)).tower_top⟩
  map_one' := by ext p; exact map_one (totalFractionsToComponent A p)
  map_mul' x y := by ext p; exact map_mul (totalFractionsToComponent A p) _ _
  map_zero' := by ext p; exact map_zero (totalFractionsToComponent A p)
  map_add' x y := by ext p; exact map_add (totalFractionsToComponent A p) _ _
  commutes' a := by ext p; exact (totalFractionsToComponent A p).commutes a

theorem normalizationToComponents_injective [IsReduced A] :
    Function.Injective (normalizationToComponents A) := by
  apply (injective_iff_map_eq_zero (normalizationToComponents A)).mpr
  intro x hx
  obtain ⟨a, s, hs⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors A) x.val
  have hmul : x.val * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a := by
    rw [← hs, IsLocalization.mk'_spec]
  have hpa (p : P) : a ∈ p.1 := by
    have hzero : totalFractionsToComponent A p x.val = 0 :=
      congrArg (fun t : ∀ p : P, Cₚ p => (t p).val) hx
    have hm := congrArg (totalFractionsToComponent A p) hmul
    rw [map_mul, hzero, zero_mul, AlgHom.commutes,
      IsScalarTower.algebraMap_apply A (Aₚ p)] at hm
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply IsFractionRing.injective (Aₚ p) (FractionRing (Aₚ p))
    rw [map_zero]
    exact hm.symm
  have ha : a = 0 := by
    have hn : a ∈ (⊥ : Ideal A).radical := by
      rw [← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
      exact fun p hp => hpa ⟨p, hp⟩
    exact IsNilpotent.eq_zero (mem_nilradical.mp hn)
  apply Subtype.ext
  rw [← hs, ha, IsLocalization.mk'_zero]
  rfl

/-- For a Noetherian reduced algebra, finite normalization of each minimal-prime
quotient implies finite normalization in the total fraction ring. -/
theorem finite_normalization_of_finite_components [IsNoetherianRing A] [IsReduced A]
    (hf : ∀ p : P, Module.Finite (Aₚ p) (Cₚ p)) :
    Module.Finite A (integralClosure A (FractionRing A)) := by
  classical
  let : Fintype P := (minimalPrimes.finite_of_isNoetherianRing A).fintype
  have (p : P) : Module.Finite A (Cₚ p) :=
    let := hf p
    Module.Finite.trans (Aₚ p) (Cₚ p)
  exact Module.Finite.of_injective (normalizationToComponents A).toLinearMap
    (normalizationToComponents_injective A)

end Components

/-- Over a complete DVR with perfect residue field, the normalization of a
flat finite-type algebra in its smooth generic fibre is finite. -/
theorem finite_integralClosure_genericFibre_of_completeDvr
    (R A : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (maximalIdeal R) R] [PerfectField (ResidueField R)]
    [CommRing A] [Algebra R A] [Module.Flat R A] [Algebra.FiniteType R A]
    [Algebra.Smooth (FractionRing R) (FractionRing R ⊗[R] A)] :
    Module.Finite A (integralClosure A (A ⊗[R] FractionRing R)) := by
  let K := FractionRing R
  let G := A ⊗[R] K
  have : IsReduced (K ⊗[R] A) := SmoothReducedProof.isReduced_of_smooth_of_domain K (K ⊗[R] A)
  have : IsReduced G :=
    isReduced_of_injective (Algebra.TensorProduct.comm R A K).toRingHom
      (Algebra.TensorProduct.comm R A K).injective
  have hregular : Algebra.algebraMapSubmonoid A (nonZeroDivisors R) ≤ nonZeroDivisors A := by
    rintro _ ⟨r, hr, rfl⟩
    apply mem_nonZeroDivisors_iff_left.mpr
    intro a ha
    have h := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := A) hr
    exact h (show r • a = r • (0 : A) by rw [Algebra.smul_def, ha, smul_zero])
  have : IsReduced A := isReduced_of_injective (algebraMap A G)
    (IsLocalization.injective G hregular)
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  have : Module.Finite A (integralClosure A (FractionRing A)) := by
    apply finite_normalization_of_finite_components A
    intro p
    have : p.1.IsPrime := p.2.isPrime
    let S := A ⧸ p.1
    apply finite_normalization_of_completeDvr_of_isDomain R S
    apply (injective_iff_map_eq_zero (algebraMap R S)).mpr
    intro r hr
    by_contra hne
    rw [IsScalarTower.algebraMap_apply R A S] at hr
    have hmem : algebraMap R A r ∈ p.1 := Ideal.Quotient.eq_zero_iff_mem.mp hr
    exact Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes p.2) hmem
      (hregular ⟨r, mem_nonZeroDivisors_of_ne_zero hne, rfl⟩)
  have : IsIntegrallyClosed G := isIntegrallyClosed_genericFibre R A
  exact Module.Finite.equiv (integralClosureGenericFibreEquivTotalFractions R A).symm.toLinearEquiv

end Langlands.AlgebraicGeometry.DvrAffineReducedFibre
