import Langlands.ClassField.Global.GlobalReciprocityProof
import Langlands.ClassField.Global.H1VanishingProof
import Langlands.ClassField.Global.CompletionTower
import Langlands.ClassFieldTheory.Local.ClassFormationAbsoluteCorestrictionProof
import Mathlib.NumberTheory.NumberField.CMField

/-! # Finite local norms and signs in CM extensions -/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Algebra
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local
open Langlands.ClassField.Global Langlands.ClassField.Global.Reciprocity
open Langlands.ClassField.Global.LocalSymbolIdentity

namespace Langlands.Global.CMHalfWeight

universe u

section Local

variable {F E : Type u} [Field F] [Field E] [NumberField F] [NumberField E]
  [Algebra F E] [IsGalois F E]
  (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
  [w.asIdeal.LiesOver v.asIdeal]

/-- At each finite place, `a` is a norm from one completion of `E` above it. -/
def IsFiniteLocalNorm (a : Fˣ) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), ∃ w : FinitePlacesAbove E v,
    ∃ b : (w.1.adicCompletion E)ˣ,
      Units.map (FiniteExtension.localNorm v w.1) b =
        Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a

/-- A finite local norm has zero local carry-class invariant. -/
theorem finiteLocalInvariant_cyclicClass_eq_zero_of_norm
    (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
    {n : ℕ} [NeZero n]
    (χ : (E ≃ₐ[F] E) →* Multiplicative (ZMod n)) (hχ : Function.Injective χ)
    (a : Fˣ) (b : (w.adicCompletion E)ˣ)
    (hb : Units.map (FiniteExtension.localNorm v w) b =
      Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a) :
    finiteLocalInvariant v w I (cyclicClass F E χ a) = 0 := by
  let : IsGalois (padicField v).Carrier (w.adicCompletion E) :=
    isGalois_adicCompletion v w
  let : FiniteDimensional (padicField v).Carrier (w.adicCompletion E) :=
    FiniteExtension.local_finite v w
  have hlocal :
      (unitsLocalMap v w 2).hom (cyclicClass F E χ a) = 0 := by
    rw [CompletionTower.unitsLocalMap_cyclicClass]
    apply (CyclicClassAlgebra.cyclicClass_eq_zero_iff_of_injective
      (χ.comp (FundamentalClass.decompositionHom v w))
      (hχ.comp (decompositionHom_injective v w)) _).2
    exact ⟨b, hb⟩
  change (I (residuePrime v)).relative (padicField v) (w.adicCompletion E)
    ((unitsLocalMap v w 2).hom (cyclicClass F E χ a)) = 0
  rw [hlocal, map_zero]

end Local

section Signs

/-- On the real line, the sign class is zero precisely for nonnegative real parts. -/
theorem signClass_eq_zero_iff {z : ℂ} :
    signClass z = 0 ↔ 0 ≤ z.re := by
  unfold signClass
  split_ifs with hz
  · simp only [rationalClass_half_ne_zero, false_iff]
    exact not_le.mpr hz
  · simp only [true_iff]
    exact le_of_not_gt hz

/-- The sign class converts finite products of nonzero real numbers into sums. -/
theorem signClass_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    signClass ((∏ i ∈ s, f i : ℝ) : ℂ) =
      ∑ i ∈ s, signClass (f i : ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [signClass]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Complex.ofReal_mul, Finset.sum_insert hi]
    rw [signClass_mul (Complex.ofReal_im _) (Complex.ofReal_im _)
      (by exact_mod_cast hf i (Finset.mem_insert_self i s))
      (by exact_mod_cast (Finset.prod_ne_zero_iff.mpr
        (fun j hj => hf j (Finset.mem_insert_of_mem hj))))]
    rw [ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

end Signs

section CM

variable (K : Type u) [Field K] [NumberField K] [IsCMField K]

local notation "F" => maximalRealSubfield K

/-- A cyclic coordinate on the quadratic CM Galois group. -/
def quadraticCoordinate : (K ≃ₐ[F] K) ≃* Multiplicative (ZMod 2) := by
  have hcard : Nat.card (K ≃ₐ[F] K) = 2 := by
    rw [IsGalois.card_aut_eq_finrank,
      IsQuadraticExtension.finrank_eq_two]
  exact (zmodMulEquivOfGenerator
    (g := IsCMField.complexConj K)
    (fun g => by rw [IsCMField.zpowers_complexConj_eq_top K]; exact Subgroup.mem_top g)
    hcard).symm

theorem quadraticCoordinate_complexConj :
    (quadraticCoordinate K (IsCMField.complexConj K)).toAdd = 1 := by
  unfold quadraticCoordinate
  rw [zmodMulEquivOfGenerator_symm_apply_generator]
  rfl

/-- A real element that is a norm at every finite place of the CM extension has
positive rational norm. -/
theorem norm_pos_of_finiteLocalNorm (a : Fˣ) (ha : IsFiniteLocalNorm (E := K) a) :
    0 < Algebra.norm ℚ (a : F) := by
  classical
  let I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p :=
    fun p _ => (localAbsoluteCorestrictionCompatibleClassFormation p).choose
  have hI : ∀ (p : ℕ) [Fact p.Prime],
      (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization := by
    intro p hp
    have h := (localAbsoluteCorestrictionCompatibleClassFormation.{u} p).choose_spec
    exact ⟨h.2.2.1, h.1⟩
  let wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove K v :=
    fun v => (ha v).choose
  let wi : ∀ v : InfinitePlace F, InfinitePlacesAbove K v := fun v =>
    ⟨(IsCMField.equivInfinitePlace K).symm v, ⟨by
      change ((InfinitePlace.comap _ _).val) = v.val
      exact congrArg Subtype.val ((IsCMField.equivInfinitePlace K).apply_symm_apply v)⟩⟩
  let χ := (quadraticCoordinate K).toMonoidHom
  have hfin : ∀ v, (haveI := (wf v).2;
      finiteLocalInvariant v (wf v).1 I (cyclicClass F K χ a)) = 0 := by
    intro v
    have := (wf v).2
    obtain ⟨b, hb⟩ := (ha v).choose_spec
    exact finiteLocalInvariant_cyclicClass_eq_zero_of_norm v (wf v).1 I χ
      (quadraticCoordinate K).injective a b hb
  have harch : ∀ v, archimedeanInvariant (wi v).1 (cyclicClass F K χ a) =
      signClass (v.embedding (a : F)) := by
    intro v
    have := (wi v).2
    rw [CyclicReciprocity.archimedeanInvariant_cyclicClass_of_isConj χ
      (quadraticCoordinate K).injective a (wi v).1 (IsCMField.complexConj K)
      (IsCMField.isConj_complexConj K _),
      CyclicReciprocity.re_embedding_algebraMap (wi v).1 v]
    change (if (v.embedding (a : F)).re < 0 then
      zmodClass 2 (quadraticCoordinate K (IsCMField.complexConj K)).toAdd else 0) = _
    rw [quadraticCoordinate_complexConj]
    norm_num [signClass, zmodClass_apply, ZMod.val_one_eq_one_mod]
  have hsum := (globalReciprocity_of ideleClassH1Vanishing I hI F K
    (cyclicClass F K χ a) wf wi).2
  simp only [hfin, finsum_zero, zero_add, harch] at hsum
  have hnormSign :
      signClass ((Algebra.norm ℚ (a : F) : ℚ) : ℂ) =
        ∑ v : InfinitePlace F, signClass (v.embedding (a : F)) := by
    rw [← Complex.ofReal_ratCast, CyclicReciprocity.algebraMap_norm_eq_prod]
    rw [signClass_prod _ _ (fun v _ => CyclicReciprocity.placeFactor_ne_zero v a.ne_zero)]
    apply Finset.sum_congr rfl
    intro v _
    rw [CyclicReciprocity.placeFactor, ite_eq_left (IsTotallyReal.isReal v)]
    simp [signClass]
  have hnnonneg : 0 ≤ Algebra.norm ℚ (a : F) := by
    have h := signClass_eq_zero_iff.mp (hnormSign.trans hsum)
    simp only [Complex.ratCast_re] at h
    exact_mod_cast h
  have hnzero : Algebra.norm ℚ (a : F) ≠ 0 :=
    (Units.map (Algebra.norm ℚ : F →* ℚ) a).ne_zero
  exact lt_of_le_of_ne hnnonneg hnzero.symm

end CM

end Langlands.Global.CMHalfWeight
