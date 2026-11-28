import Langlands.Global.AdelicLevelBaseChangeStatement
import Langlands.Global.CurvePlaceSinglePoleProof
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.Localization.BaseChange

/-! # The scalar extension identity for actual adelic levels

This file proves `AdelicLevelBaseChangeStatement`, the identity
`O_T ⊗[O_S] A_S ≃ A_T` of the paragraph after Remark 3.5 on p. 6 of
B. Conrad, *Weil and Grothendieck approaches to adelic points* (2011), for
number fields and for global function fields over finite constant fields.
A denominator `d` with valuation `< 1` exactly at the new places and `1` outside
`T` makes both inclusions localizations away from `d`; the base-change property
of localization then identifies the square as a pushout. -/

noncomputable section

universe u

open IsDedekindDomain AlgebraicCurve IntermediateField
open scoped AlgebraicCurve.CurveModel IntermediateField.algebraAdjoinAdjoin
  Langlands.Global.FiniteConstantCurveChart TensorProduct RestrictedProduct

namespace Langlands.Global

/-- The product of prime-power generators has the prescribed finite prime support. -/
private theorem exists_generator_with_support (R : Type u) [CommRing R] [IsDedekindDomain R]
    [Finite (ClassGroup R)] (E : Finset (HeightOneSpectrum R)) :
    ∃ d : R, d ≠ 0 ∧ ∀ P : HeightOneSpectrum R, d ∈ P.asIdeal ↔ P ∈ E := by
  classical
  choose d hd0 hdP hdQ using exists_primePowerGenerator R
  refine ⟨∏ P ∈ E, d P, Finset.prod_ne_zero_iff.mpr (fun P _ => hd0 P), fun P => ?_⟩
  rw [P.isPrime.prod_mem_iff]
  constructor
  · rintro ⟨Q, hQE, hQ⟩
    by_cases h : P = Q
    · exact h.symm ▸ hQE
    · exact (hdQ Q P h hQ).elim
  · intro h
    exact ⟨P, h, hdP P⟩

/-- A common exponent makes an element integral at the finitely many new places. -/
private theorem exists_level_exponent {ι : Type u} {S T : Finset ι}
    (δ α : ι → WithZero (Multiplicative ℤ)) (δ_small : ∀ v, v ∉ S → v ∈ T → δ v < 1)
    (δ_unit : ∀ v, v ∉ S → v ∉ T → δ v = 1)
    (α_integral : ∀ v, v ∉ T → α v ≤ 1) :
    ∃ n : ℕ, ∀ v, v ∉ S → δ v ^ n * α v ≤ 1 := by
  classical
  let E := T \ S
  have hlocal (v : E) : ∃ n : ℕ, δ v.1 ^ n * α v.1 ≤ 1 := by
    by_cases h : δ v.1 = 0
    · exact ⟨1, by simp [h]⟩
    have hv := Finset.mem_sdiff.mp v.property
    have hd := pos_iff_ne_zero.mpr h
    obtain ⟨n, hn⟩ := MulArchimedean.arch (α v.1)
      ((one_lt_inv₀ hd).mpr (δ_small v.1 hv.2 hv.1))
    refine ⟨n, (le_inv_mul_iff₀ (pow_pos hd _)).mp ?_⟩
    simpa only [inv_pow, mul_one] using hn
  choose n hn using hlocal
  refine ⟨∑ v : E, n v, fun v hvS => ?_⟩
  by_cases hvT : v ∈ T
  · let w : E := ⟨v, Finset.mem_sdiff.mpr ⟨hvT, hvS⟩⟩
    have hle : n w ≤ ∑ z : E, n z :=
      Finset.single_le_sum (fun z _ => Nat.zero_le (n z)) (Finset.mem_univ w)
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hle
    rw [hm, pow_add]
    calc
      _ = δ v ^ m * (δ v ^ n w * α v) := by ac_rfl
      _ ≤ δ v ^ m * 1 := mul_le_mul_of_nonneg_left (hn w) (zero_le : 0 ≤ δ v ^ m)
      _ ≤ 1 := by simpa only [mul_one] using pow_le_one₀ zero_le (δ_small v hvS hvT).le
  · simpa only [δ_unit v hvS hvT, one_pow, one_mul] using α_integral v hvT

/-- Two nested subrings form an away localization when the denominator is a unit upstairs
and a power of it clears every element. -/
private theorem isLocalizationAway_subringInclusion {Q : Type u} [CommRing Q]
    {A B : Subring Q} (hAB : A ≤ B) (d : A) (unit : IsUnit (Subring.inclusion hAB d))
    (clears : ∀ b : B, ∃ n : ℕ, (d : Q)^n * (b : Q) ∈ A) :
    letI := (Subring.inclusion hAB).toAlgebra
    IsLocalization.Away d B := by
  let := (Subring.inclusion hAB).toAlgebra
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    rw [map_pow]
    exact unit.pow n
  · intro b
    obtain ⟨n, hn⟩ := clears b
    exact ⟨(⟨(d : Q)^n * (b : Q), hn⟩, ⟨d ^ n, n, rfl⟩), Subtype.ext (mul_comm _ _)⟩
  · intro a b hab
    have eq : a = b := Subtype.ext (congrArg (fun c : B => (c : Q)) hab)
    exact ⟨1, by simpa only [OneMemClass.coe_one, one_mul] using eq⟩

namespace AdelicLevelBaseChange

/-- A square whose two parallel sides are localizations away from `d` and its image is
a pushout, so its tensor-product equivalence multiplies the images of the coefficients. -/
private theorem exists_pushout_equiv (R B A C : Type u)
    [CommRing R] [CommRing B] [CommRing A] [CommRing C]
    [Algebra R B] [Algebra R A] [Algebra B C] [Algebra A C]
    [Algebra R C] [IsScalarTower R B C] [IsScalarTower R A C]
    (d : R) [IsLocalization.Away d B] [IsLocalization.Away (algebraMap R A d) C] :
    ∃ e : B ⊗[R] A ≃ₐ[B] C, ∀ b a, e (b ⊗ₜ a) = algebraMap B C b * algebraMap A C a := by
  have hp : Algebra.IsPushout R A B C := by
    apply (Algebra.isLocalization_iff_isPushout (Submonoid.powers d) B).mp
    rw [Algebra.algebraMapSubmonoid_powers]
    infer_instance
  let : Algebra.IsPushout R B A C := by
    rw [Algebra.IsPushout.comm]
    exact hp
  exact ⟨Algebra.IsPushout.equiv R B A C, Algebra.IsPushout.equiv_tmul R B A C⟩

section NumberField

/-- A nonzero element of a number field with valuation `< 1` at the finite places of
`T \ S` and valuation `1` outside `T`, from the finite class group of its integers. -/
private theorem numberField_exists_level_denominator (K : Type u) [Field K] [NumberField K]
    (S T : Finset (FinitePlace K)) :
    ∃ d : K, d ≠ 0 ∧
      (∀ v : FinitePlace K, v ∉ S → v ∈ T → v.valuation K d < 1) ∧
      (∀ v : FinitePlace K, v ∉ S → v ∉ T → v.valuation K d = 1) := by
  classical
  obtain ⟨a, ha, ha_support⟩ := exists_generator_with_support (NumberField.RingOfIntegers K) (T \ S)
  have ha0 : algebraMap (NumberField.RingOfIntegers K) K a ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (NumberField.RingOfIntegers K) K).ne ha
  refine ⟨algebraMap _ K a, ha0, ?_, ?_⟩
  · intro v hvS hvT
    exact (v.valuation_lt_one_iff_mem a).mpr ((ha_support v).mpr (Finset.mem_sdiff.mpr ⟨hvT, hvS⟩))
  · intro v _ hvT
    exact v.valuation_eq_one_iff_notMem.mpr
      (fun h => hvT (Finset.mem_sdiff.mp ((ha_support v).mp h)).1)

/-- The completed coordinate of the diagonal image of `d` has the valuation of `d`. -/
private theorem valued_finiteProjection_diagonal (K : Type u) [Field K] [NumberField K]
    (d : K) (v : FinitePlace K) :
    Valued.v (finiteProjection K v (diagonal K d)) = v.valuation K d := by
  change Valued.v (algebraMap K (v.adicCompletion K) d) = _
  simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
    Algebra.algebraMap_self, RingHom.id_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

/-- The canonical scalar extension for every actual number-field level. -/
theorem numberFieldAdelicLevelBaseChange : NumberFieldAdelicLevelBaseChangeStatement.{u} := by
  intro K _ _ S T hST
  classical
  let R := (S : Set (FinitePlace K)).integer K
  let B := (T : Set (FinitePlace K)).integer K
  let A := numberFieldAdeleLevel K S
  let C := numberFieldAdeleLevel K T
  let AB := (numberFieldSIntegersMap K hST).toAlgebra
  let AC := (numberFieldAdeleLevelMap K hST).toAlgebra
  let RC := ((numberFieldAdeleLevelDiagonal K T).comp (numberFieldSIntegersMap K hST)).toAlgebra
  let : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨d, hd0, hd_small, hd_unit⟩ := numberField_exists_level_denominator K S T
  have hdR : d ∈ R := by
    intro v hv
    by_cases h : v ∈ T
    · exact (hd_small v hv h).le
    · exact (hd_unit v hv h).le
  have hdB : d⁻¹ ∈ B := by
    intro v hv
    rw [map_inv₀, hd_unit v (fun h => hv (hST h)) hv, inv_one]
  let dR : R := ⟨d, hdR⟩
  let dB : B := ⟨d⁻¹, hdB⟩
  have hunit : IsUnit (algebraMap R B dR) := IsUnit.of_mul_eq_one dB
    (Subtype.ext (mul_inv_cancel₀ hd0))
  have hcR (b : B) : ∃ n : ℕ, (dR : K)^n * (b : K) ∈ R := by
    obtain ⟨n, hn⟩ := exists_level_exponent (S := S) (T := T) (fun v => v.valuation K d)
      (fun v => v.valuation K (b : K)) hd_small hd_unit b.property
    refine ⟨n, fun v hv => ?_⟩
    rw [map_mul, map_pow]
    exact hn v hv
  let : IsLocalization.Away dR B := isLocalizationAway_subringInclusion
    (A := R.toSubring) (B := B.toSubring)
    (fun _ ha v hv => ha v (fun h => hv (hST h))) dR hunit hcR
  let dA : A := algebraMap R A dR
  have hunitA : IsUnit (algebraMap A C dA) := hunit.map (numberFieldAdeleLevelDiagonal K T)
  have hcA (c : C) : ∃ n : ℕ, (dA : Adeles K)^n * (c : Adeles K) ∈ A := by
    obtain ⟨n, hn⟩ := exists_level_exponent (S := S) (T := T) (fun v => v.valuation K d)
      (fun v => Valued.v (finiteProjection K v (c : Adeles K))) hd_small hd_unit c.property
    refine ⟨n, fun v hv => ?_⟩
    change Valued.v (finiteProjection K v ((diagonal K d)^n * (c : Adeles K))) ≤ 1
    rw [map_mul, map_pow, map_mul, map_pow, valued_finiteProjection_diagonal]
    exact hn v hv
  let : IsLocalization.Away dA C := isLocalizationAway_subringInclusion
    (numberFieldAdeleLevel_mono K hST) dA hunitA hcA
  exact exists_pushout_equiv R B A C dR

end NumberField

section Curve

variable (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]

/-- A normalized chart with one pole in `S` supplies a denominator with the
prescribed support outside `S`. -/
private theorem curvePlace_exists_level_denominator (S T : Finset (Place k F)) (hS : S.Nonempty) :
    ∃ d : F, d ≠ 0 ∧
      (∀ v : Place k F, v ∉ S → v ∈ T → v.adicValuation d < 1) ∧
      (∀ v : Place k F, v ∉ S → v ∉ T → v.adicValuation d = 1) := by
  classical
  obtain ⟨v₀, hv₀⟩ := hS
  obtain ⟨s, hs, hs_other⟩ := exists_curvePlace_singlePole k F v₀
  have hs₀ : s ≠ 0 := fun h => hs (h ▸ v₀.toValuationSubring.zero_mem)
  have hsval : 1 < v₀.adicValuation s :=
    lt_of_not_ge (fun h => hs (v₀.mem_iff_adicValuation_le_one.mpr h))
  have ht : Transcendental k s := Valuation.transcendental_of_ne_one k s hs₀ hsval.ne'
  let : FiniteDimensional k⟮s⟯ F := FunctionField.finiteDimensional_of_adjoin_transcendental ht
  let C := CurveModel.chartRing k ({s} : Set F)
  let : Finite (ClassGroup C) := finite_classGroup_normalizedCurveChart k F s ht
  have hreg (w : {v : Place k F // v ∉ S}) : s ∈ w.1.toValuationSubring :=
    hs_other w.1 (fun h => w.2 (h ▸ hv₀))
  let center (w : {v : Place k F // v ∉ S}) : HeightOneSpectrum C :=
    CurveModel.primeOfValuationSubring k s w.1.toValuationSubring w.1.algebraMap_mem' (hreg w) w.1.ne_top'
  have hcenter (w : {v : Place k F // v ∉ S}) :
      Place.ofHeightOneSpectrum (K := k) (center w) = w.1 :=
    FiniteConstantCurveChart.ofHeightOneSpectrum_center k F s w.1 (hreg w)
  let E := (T \ S).attach.image (fun w => center ⟨w.1, (Finset.mem_sdiff.mp w.2).2⟩)
  obtain ⟨d, hd0, hd_support⟩ := exists_generator_with_support C E
  have hdF : (d : F) ≠ 0 := fun h => hd0 (Subtype.ext h)
  have hmem (w : Place k F) (hw : w ∉ S) :
      d ∈ (center ⟨w, hw⟩).asIdeal ↔ w ∈ T := by
    rw [hd_support]
    constructor
    · rintro h
      obtain ⟨z, _, hz⟩ := Finset.mem_image.mp h
      have he : z.1 = w := by
        simpa only [hcenter] using
          congrArg (fun P : HeightOneSpectrum C => (Place.ofHeightOneSpectrum (K := k) P : Place k F)) hz
      exact he ▸ (Finset.mem_sdiff.mp z.2).1
    · intro hwT
      exact Finset.mem_image.mpr ⟨⟨w, Finset.mem_sdiff.mpr ⟨hwT, hw⟩⟩, Finset.mem_attach _ _, rfl⟩
  have hle (w : Place k F) (hw : w ∉ S) : w.adicValuation (d : F) ≤ 1 :=
    w.mem_iff_adicValuation_le_one.mp (CurveModel.chartRing_le_valuationSubring
      w.toValuationSubring w.algebraMap_mem' (Set.singleton_subset_iff.mpr (hreg ⟨w, hw⟩)) d.2)
  have hlt (w : Place k F) (hw : w ∉ S) : w.adicValuation (d : F) < 1 ↔ w ∈ T := by
    rw [← hmem w hw]
    change w.adicValuation (d : F) < 1 ↔ w.toValuationSubring.valuation (d : F) < 1
    rw [w.adicValuation.val_lt_one_iff hdF, w.toValuationSubring.valuation.val_lt_one_iff hdF]
    simp only [← not_le, ← w.mem_iff_adicValuation_le_one, w.toValuationSubring.valuation_le_one_iff]
  exact ⟨d, hdF, fun w hwS hwT => (hlt w hwS).mpr hwT,
    fun w hwS hwT => (hle w hwS).antisymm (not_lt.mp ((hlt w hwS).not.mpr hwT))⟩

omit [Finite k] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F] in
/-- The image of `d` in the completion at a curve place has the valuation of `d`. -/
private theorem curvePlace_completed_valuation (v : Place k F) (d : F) :
    Valued.v (algebraMap F (curvePlaceCompletion v) d) = v.adicValuation d := by
  change Valued.v (algebraMap F (v.heightOneSpectrum.adicCompletion F) d) = _
  simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
    Algebra.algebraMap_self, RingHom.id_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    Place.adicValuation]

end Curve

/-- The canonical scalar extension for actual global function-field levels. -/
theorem curvePlaceAdelicLevelBaseChange : CurvePlaceAdelicLevelBaseChangeStatement.{u} := by
  intro k F _ _ _ _ _ _ _ S T hS hST
  classical
  let R := curvePlaceSIntegers k F S
  let B := curvePlaceSIntegers k F T
  let A := curvePlaceAdeleLevel k F S
  let C := curvePlaceAdeleLevel k F T
  let AB := (curvePlaceSIntegersMap k F hST).toAlgebra
  let AC := (curvePlaceAdeleLevelMap k F hST).toAlgebra
  let RC := ((curvePlaceAdeleLevelDiagonal k F T).comp (curvePlaceSIntegersMap k F hST)).toAlgebra
  let : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨d, hd0, hd_small, hd_unit⟩ := curvePlace_exists_level_denominator k F S T hS
  have hdR : d ∈ R := by
    intro v hv
    apply v.mem_iff_adicValuation_le_one.mpr
    by_cases h : v ∈ T
    · exact (hd_small v hv h).le
    · exact (hd_unit v hv h).le
  have hdB : d⁻¹ ∈ B := by
    intro v hv
    apply v.mem_iff_adicValuation_le_one.mpr
    rw [map_inv₀, hd_unit v (fun h => hv (hST h)) hv, inv_one]
  let dR : R := ⟨d, hdR⟩
  let dB : B := ⟨d⁻¹, hdB⟩
  have hunit : IsUnit (algebraMap R B dR) := IsUnit.of_mul_eq_one dB
    (Subtype.ext (mul_inv_cancel₀ hd0))
  have hcR (b : B) : ∃ n : ℕ, (dR : F)^n * (b : F) ∈ R := by
    obtain ⟨n, hn⟩ := exists_level_exponent (S := S) (T := T) (fun v => v.adicValuation d)
      (fun v => v.adicValuation (b : F)) hd_small hd_unit
      (fun v hv => v.mem_iff_adicValuation_le_one.mp (b.property v hv))
    refine ⟨n, fun v hv => v.mem_iff_adicValuation_le_one.mpr ?_⟩
    rw [map_mul, map_pow]
    exact hn v hv
  let : IsLocalization.Away dR B := isLocalizationAway_subringInclusion
    (curvePlaceSIntegers_mono k F hST) dR hunit hcR
  let dA : A := algebraMap R A dR
  have hunitA : IsUnit (algebraMap A C dA) := hunit.map (curvePlaceAdeleLevelDiagonal k F T)
  have hcA (c : C) : ∃ n : ℕ, (dA : CurvePlaceAdeleRing k F)^n * (c : CurvePlaceAdeleRing k F) ∈ A := by
    obtain ⟨n, hn⟩ := exists_level_exponent (S := S) (T := T) (fun v => v.adicValuation d)
      (fun v => Valued.v ((c : CurvePlaceAdeleRing k F) v)) hd_small hd_unit c.property
    refine ⟨n, fun v hv => ?_⟩
    let ev : CurvePlaceAdeleRing k F →+* curvePlaceCompletion v :=
      RestrictedProduct.evalRingHom (fun w : Place k F => curvePlaceCompletion w) v
    change Valued.v (ev ((dA : CurvePlaceAdeleRing k F)^n * (c : CurvePlaceAdeleRing k F))) ≤ 1
    rw [map_mul, map_pow, map_mul, map_pow]
    change Valued.v (algebraMap F (curvePlaceCompletion v) d) ^ n *
      Valued.v ((c : CurvePlaceAdeleRing k F) v) ≤ 1
    rw [curvePlace_completed_valuation k F]
    exact hn v hv
  let : IsLocalization.Away dA C := isLocalizationAway_subringInclusion
    (curvePlaceAdeleLevel_mono k F hST) dA hunitA hcA
  exact exists_pushout_equiv R B A C dR

end AdelicLevelBaseChange

/-- Both actual arithmetic base-change identities. -/
theorem adelicLevelBaseChange : AdelicLevelBaseChangeStatement.{u} :=
  ⟨AdelicLevelBaseChange.numberFieldAdelicLevelBaseChange,
    AdelicLevelBaseChange.curvePlaceAdelicLevelBaseChange⟩

end Langlands.Global
