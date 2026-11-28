import StacksFrontier.RingTheory.Henselian.Criteria
import Langlands.CommutativeAlgebra.FiniteTypeIntGRing.CompletionRegular
import Langlands.CommutativeAlgebra.RegularLocalFactorialTools
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-! # Completing a regular local chart mapping to a complete discrete valuation ring -/

universe u w

open IsLocalRing

namespace Langlands.CommutativeAlgebra.ArithmeticRegularLocalApproximation

/-- The chart part of the arithmetic regular local approximation: a Henselian regular local
domain `B` with a regular parameter `t`, a local map `j : B → W'` sending `t` to an irreducible
element, residue field purely inseparable over a finitely generated subfield, and a
factorization of `F : C → Frac W'` through `B[1/t]`. -/
def ChartConclusion (W' : Type u) [CommRing W'] (C : Type w) [CommRing C]
    (F : C →+* FractionRing W') : Prop :=
  ∃ (B : Type u) (_ : CommRing B) (_ : IsDomain B) (_ : IsRegularLocalRing B)
    (_ : HenselianLocalRing B) (t : B) (j : B →+* W') (_ : IsLocalHom j),
    t ∈ maximalIdeal B ∧ t ∉ maximalIdeal B ^ 2 ∧
    IsRegularLocalRing (B ⧸ Ideal.span {t}) ∧ Irreducible (j t) ∧
    (∃ k : Subfield (ResidueField B), Field.FG k ∧ IsPurelyInseparable k (ResidueField B)) ∧
    ∃ (jAway : Localization.Away t →+* FractionRing W') (g : C →+* Localization.Away t),
      jAway.comp (algebraMap B (Localization.Away t)) =
        (algebraMap W' (FractionRing W')).comp j ∧
      jAway.comp g = F

/-- Finite generation of a field passes to surjective images. -/
theorem fieldFG_of_surjective {K L : Type*} [Field K] [Field L] [Field.FG K] (f : K →+* L)
    (hf : Function.Surjective f) : Field.FG L := by
  classical
  obtain ⟨S, hS⟩ := Field.FG.finitely_generated (L := K)
  refine ⟨⟨S.image f, ?_⟩⟩
  rw [Finset.coe_image, ← RingHom.map_field_closure, hS, eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ := hf y
  exact Subfield.mem_map.mpr ⟨x, Subfield.mem_top x, rfl⟩

/-- A field is purely inseparable over its top subfield. -/
theorem isPurelyInseparable_top (K : Type*) [Field K] :
    IsPurelyInseparable (⊤ : Subfield K) K :=
  ⟨⟨fun x => isIntegral_algebraMap (R := (⊤ : Subfield K)) (A := K)
      (x := ⟨x, Subfield.mem_top x⟩)⟩,
    fun x _ => ⟨⟨x, Subfield.mem_top x⟩, rfl⟩⟩

/-- An irreducible element of a discrete valuation ring is not in the square of the maximal
ideal. -/
theorem irreducible_notMem_maximalIdeal_sq {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {ϖ : R} (hϖ : Irreducible ϖ) : ϖ ∉ maximalIdeal R ^ 2 := by
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  rintro ⟨a, ha⟩
  apply hϖ.not_isUnit
  refine IsUnit.of_mul_eq_one a ?_
  apply mul_left_cancel₀ hϖ.ne_zero
  linear_combination ha

/-- A local map `P → W'` extends to the maximal-ideal adic completion of `P` when `W'` is
complete for its maximal ideal. -/
theorem exists_adicCompletion_lift {P W' : Type*} [CommRing P] [IsLocalRing P]
    [CommRing W'] [IsLocalRing W'] [IsAdicComplete (maximalIdeal W') W']
    (h : P →+* W') [IsLocalHom h] :
    ∃ j : AdicCompletion (maximalIdeal P) P →+* W',
      j.comp (algebraMap P (AdicCompletion (maximalIdeal P) P)) = h := by
  have hmap : (maximalIdeal P).map h ≤ maximalIdeal W' :=
    map_maximalIdeal_le h
  have hpow (n : ℕ) : maximalIdeal P ^ n ≤ (maximalIdeal W' ^ n).comap h := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hmap n
  let qmap (n : ℕ) : P ⧸ maximalIdeal P ^ n →+* W' ⧸ maximalIdeal W' ^ n :=
    Ideal.Quotient.lift (maximalIdeal P ^ n) ((Ideal.Quotient.mk (maximalIdeal W' ^ n)).comp h)
      (by
        intro x hx
        simp only [RingHom.comp_apply]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (hpow n hx))
  let fam (n : ℕ) : AdicCompletion (maximalIdeal P) P →+* W' ⧸ maximalIdeal W' ^ n :=
    (qmap n).comp (AdicCompletion.evalₐ (maximalIdeal P) n).toRingHom
  have hfam {m n : ℕ} (hmn : m ≤ n) :
      (Ideal.Quotient.factorPow (maximalIdeal W') hmn).comp (fam n) = fam m := by
    ext x
    induction x using AdicCompletion.induction_on with
    | _ x =>
      simpa [fam, qmap] using
        congrArg (qmap m) (AdicCompletion.Ideal.mk_eq_mk (maximalIdeal P) hmn x)
  refine ⟨IsAdicComplete.liftRingHom (maximalIdeal W') fam hfam, ?_⟩
  apply DFunLike.coe_injective
  apply IsHausdorff.funext' (maximalIdeal W')
  intro n x
  rw [RingHom.comp_apply, IsAdicComplete.mk_liftRingHom]
  simp [fam, qmap, AdicCompletion.algebraMap_apply]

/-- Let `h : P → W'` be a local map from a regular local ring with finitely generated residue
field to a complete discrete valuation ring, sending `t` to a uniformizer. Given a factorization
of `F : C → Frac W'` through `P[1/t]` compatible with `h`, completing `P` gives
`ChartConclusion W' C F` with the extended local map `B → W'`. -/
theorem chartConclusion_of_regularLocal {W' : Type u} [CommRing W'] [IsDomain W']
    [IsDiscreteValuationRing W'] [IsAdicComplete (maximalIdeal W') W']
    {C : Type w} [CommRing C] (F : C →+* FractionRing W')
    (P : Type u) [CommRing P] [IsRegularLocalRing P] [Field.FG (ResidueField P)]
    (h : P →+* W') [IsLocalHom h] (t : P) (ht : Irreducible (h t))
    (jAway₀ : Localization.Away t →+* FractionRing W') (g₀ : C →+* Localization.Away t)
    (hj₀ : jAway₀.comp (algebraMap P (Localization.Away t)) =
      (algebraMap W' (FractionRing W')).comp h)
    (hg₀ : jAway₀.comp g₀ = F) : ChartConclusion W' C F := by
  classical
  have hRB : IsRegularLocalRing (AdicCompletion (maximalIdeal P) P) :=
    FiniteTypeIntGRing.isRegularLocalRing_adicCompletion P
  have hDB : IsDomain (AdicCompletion (maximalIdeal P) P) := regularLocalDomain _ hRB
  have hHB : HenselianLocalRing (AdicCompletion (maximalIdeal P) P) :=
    henselianLocalRing_of_isAdicComplete_maximalIdeal _
  have hmap : (maximalIdeal P).map h ≤ maximalIdeal W' :=
    map_maximalIdeal_le h
  obtain ⟨j, hj⟩ := exists_adicCompletion_lift h
  have hjloc : IsLocalHom j := by
    refine ((local_hom_TFAE j).out 3 1).mp ?_
    rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map, hj]
    exact hmap
  set tB := algebraMap P (AdicCompletion (maximalIdeal P) P) t with htB
  have hjt : j tB = h t := RingHom.congr_fun hj t
  have htm : tB ∈ maximalIdeal (AdicCompletion (maximalIdeal P) P) :=
    (mem_maximalIdeal _).mpr fun hu => ht.not_isUnit (hjt ▸ hu.map j)
  have ht2 : tB ∉ maximalIdeal (AdicCompletion (maximalIdeal P) P) ^ 2 := by
    intro hmem
    apply irreducible_notMem_maximalIdeal_sq ht
    rw [← hjt]
    have h1 := Ideal.mem_map_of_mem j hmem
    rw [Ideal.map_pow] at h1
    exact Ideal.pow_right_mono (map_maximalIdeal_le j) 2 h1
  have hunit : IsUnit (((algebraMap W' (FractionRing W')).comp j) tB) := by
    rw [RingHom.comp_apply, hjt, isUnit_iff_ne_zero]
    exact (IsFractionRing.injective W' (FractionRing W')).ne_iff' (map_zero _) |>.mpr ht.ne_zero
  let jAway : Localization.Away tB →+* FractionRing W' := IsLocalization.Away.lift tB hunit
  have hjAway : jAway.comp (algebraMap _ (Localization.Away tB)) =
      (algebraMap W' (FractionRing W')).comp j :=
    IsLocalization.Away.lift_comp tB hunit
  have hcomp : jAway.comp (Localization.awayMap (algebraMap P _) t) = jAway₀ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers t)
    ext x
    have e1 : Localization.awayMap (algebraMap P (AdicCompletion (maximalIdeal P) P)) t
        (algebraMap P (Localization.Away t) x) = algebraMap _ (Localization.Away tB)
          (algebraMap P (AdicCompletion (maximalIdeal P) P) x) :=
      IsLocalization.map_eq _ _
    simp only [RingHom.comp_apply, e1]
    have hjx : j (algebraMap P (AdicCompletion (maximalIdeal P) P) x) = h x :=
      RingHom.congr_fun hj x
    rw [← RingHom.comp_apply jAway, hjAway, ← RingHom.comp_apply jAway₀, hj₀]
    simp only [RingHom.comp_apply, hjx]
  have hres : Field.FG (⊤ : Subfield (ResidueField (AdicCompletion (maximalIdeal P) P))) :=
    fieldFG_of_surjective ((Subfield.topEquiv (K := ResidueField _)).symm.toRingHom.comp
        (ResidueField.map (algebraMap P (AdicCompletion (maximalIdeal P) P))))
      ((Subfield.topEquiv (K := ResidueField _)).symm.surjective.comp
        (AdicCompletion.residueField_map_bijective P).2)
  exact ⟨AdicCompletion (maximalIdeal P) P, inferInstance, hDB, hRB, hHB, tB, j, hjloc, htm,
    ht2, RegularLocalFactorial.isRegularLocalRing_quotient_span_singleton htm ht2, hjt ▸ ht,
    ⟨⊤, hres, isPurelyInseparable_top _⟩, jAway,
    (Localization.awayMap (algebraMap P _) t).comp g₀, hjAway,
    by rw [← RingHom.comp_assoc, hcomp, hg₀]⟩

end Langlands.CommutativeAlgebra.ArithmeticRegularLocalApproximation
