import Langlands.ClassFieldTheory.Global.CyclicHasseNormStatement
import Langlands.ClassFieldTheory.Global.IdeleDivisor
import Langlands.Global.AdelicFunctoriality.IdeleClassNormIndexReduction
import Langlands.Global.AdelicFunctoriality.IdeleNormLift
import Langlands.Global.Arithmetic.CyclicNonsplitPrimeProof
import Langlands.Global.Arithmetic.KummerRadical
import Langlands.LinearAlgebra.QuadraticNormEquation

/-! # Local norm equations for quadratic extensions of number fields -/

noncomputable section

namespace Langlands

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter
open scoped NumberField NumberField.LiesOver
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension
open scoped Langlands.Global.AdelicFunctoriality.InfiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.ClassFieldTheory.Global
open Langlands.Global.Arithmetic.KummerRadical QuadraticNormEquation

universe u

/-- The equation `x² - a y² = b` for nonzero `a,b` satisfies the local-to-global principle. -/
def QuadraticNormLocalGlobalStatement : Prop :=
  ∀ {F : Type u} [Field F] [NumberField F] {a b : F}, a ≠ 0 → b ≠ 0 →
    (∀ v : HeightOneSpectrum (𝓞 F), ∃ x y : v.adicCompletion F,
      x ^ 2 - algebraMap F (v.adicCompletion F) a * y ^ 2 = algebraMap F (v.adicCompletion F) b) →
    (∀ v : InfinitePlace F, ∃ x y : v.Completion,
      x ^ 2 - algebraMap F v.Completion a * y ^ 2 = algebraMap F v.Completion b) →
      ∃ x y : F, x ^ 2 - a * y ^ 2 = b

namespace QuadraticNormLocalGlobal

section NormComparison

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] {a : K} {r : L}

private theorem isSquare_of_root_finrank_eq_one
    (hL : Module.finrank K L = 1) (hr : r ^ 2 = algebraMap K L a) : IsSquare a := by
  have hbot := (Subalgebra.bot_eq_top_iff_finrank_eq_one).2 hL
  obtain ⟨s, hs⟩ := Algebra.mem_bot.1 (hbot ▸ (Algebra.mem_top : r ∈ (⊤ : Subalgebra K L)))
  refine (isSquare_iff_exists_sq a).2 ⟨s, (algebraMap K L).injective ?_⟩
  rw [map_pow, hs, hr]

private theorem exists_eq_iff_exists_norm_of_finrank_two
    (hL : Module.finrank K L = 2) (ha : ¬ IsSquare a) (hr : r ^ 2 = algebraMap K L a)
    (b : Kˣ) : (∃ x y : K, x ^ 2 - a * y ^ 2 = (b : K)) ↔
      ∃ c : Lˣ, Algebra.norm K (c : L) = (b : K) := by
  let : Fact (¬ IsSquare a) := ⟨ha⟩
  let e := algEquivOfRoot hL hr
  have hnorm (z : QuadraticAlgebra K a 0) : Algebra.norm K (e z) = z.re ^ 2 - a * z.im ^ 2 :=
    (Algebra.norm_eq_of_algEquiv e z).trans (algebraNorm a z)
  constructor
  · rintro ⟨x, y, h⟩
    let z : QuadraticAlgebra K a 0 := ⟨x, y⟩
    have hn : Algebra.norm K (e z) = (b : K) := (hnorm z).trans h
    have hz : e z ≠ 0 := by
      intro hz
      rw [hz, Algebra.norm_zero] at hn
      exact b.ne_zero hn.symm
    exact ⟨Units.mk0 (e z) hz, hn⟩
  · rintro ⟨c, hc⟩
    let z := e.symm (c : L)
    refine ⟨z.re, z.im, (hnorm z).symm.trans ?_⟩
    rw [show e z = (c : L) from e.apply_symm_apply c]
    exact hc

private theorem exists_eq_iff_exists_norm [CharZero K]
    (ha : a ≠ 0) (hr : r ^ 2 = algebraMap K L a)
    (hL : Module.finrank K L = 1 ∨ Module.finrank K L = 2)
    (hsplit : IsSquare a → Module.finrank K L = 1) (b : Kˣ) :
    (∃ x y : K, x ^ 2 - a * y ^ 2 = (b : K)) ↔ ∃ c : Lˣ, Algebra.norm K (c : L) = (b : K) := by
  rcases hL with hL | hL
  · constructor
    · intro _
      refine ⟨Units.map (algebraMap K L).toMonoidHom b, ?_⟩
      change Algebra.norm K (algebraMap K L (b : K)) = _
      rw [Algebra.norm_algebraMap, hL, pow_one]
    · intro _
      exact exists_eq_of_isSquare ha (isSquare_of_root_finrank_eq_one hL hr)
  · exact exists_eq_iff_exists_norm_of_finrank_two hL
      (fun hs => (by decide : 1 ≠ 2) ((hsplit hs).symm.trans hL)) hr b

end NormComparison

section Completions

variable {F E : Type u} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  {a : F} {r : E}

private theorem finite_finrank_eq_one_of_isSquare (hgen : Algebra.adjoin F {r} = ⊤)
    (hr : r ^ 2 = algebraMap F E a)
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]
    (hs : IsSquare (algebraMap F (v.adicCompletion F) a)) :
    Module.finrank (v.adicCompletion F) (w.adicCompletion E) = 1 := by
  obtain ⟨s, hs⟩ := hs.exists_sq
  exact finrank_adicCompletion_eq_one (IsPrimitiveRoot.neg_one (R := F) 0 (by decide))
    hgen hr v w hs.symm

private theorem finite_exists_eq_iff_exists_localNorm [Algebra.IsQuadraticExtension F E]
    (ha : a ≠ 0) (hgen : Algebra.adjoin F {r} = ⊤) (hr : r ^ 2 = algebraMap F E a)
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]
    (b : (v.adicCompletion F)ˣ) :
    (∃ x y : v.adicCompletion F, x ^ 2 - algebraMap F (v.adicCompletion F) a * y ^ 2 = b) ↔
      ∃ c : (w.adicCompletion E)ˣ, FiniteExtension.localNorm v w (c : w.adicCompletion E) = b := by
  have hdeg := localDegree_dvd v w
  rw [Algebra.IsQuadraticExtension.finrank_eq_two F E] at hdeg
  have hr' : (algebraMap E (w.adicCompletion E) r) ^ 2 =
      algebraMap (v.adicCompletion F) (w.adicCompletion E) (algebraMap F (v.adicCompletion F) a) := by
    rw [← map_pow, hr, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  let : CharZero (v.adicCompletion F) := Algebra.charZero_of_charZero F _
  exact exists_eq_iff_exists_norm ((map_ne_zero_iff (algebraMap F (v.adicCompletion F))
    (algebraMap F (v.adicCompletion F)).injective).2 ha) hr' ((Nat.dvd_prime Nat.prime_two).mp hdeg)
    (finite_finrank_eq_one_of_isSquare hgen hr v w) b

omit [NumberField E] in
private theorem infinite_exists_eq_iff_exists_localNorm
    (ha : a ≠ 0) (hgen : Algebra.adjoin F {r} = ⊤) (hr : r ^ 2 = algebraMap F E a)
    (v : InfinitePlace F) (w : InfinitePlace E) [w.LiesOver v] (b : v.Completionˣ) :
    (∃ x y : v.Completion, x ^ 2 - algebraMap F v.Completion a * y ^ 2 = b) ↔
      ∃ c : w.Completionˣ, InfiniteExtension.localNorm v w (c : w.Completion) = b := by
  have hdeg : Module.finrank v.Completion w.Completion = 1 ∨
      Module.finrank v.Completion w.Completion = 2 := by
    rcases w.isUnramified_or_isRamified F with hw | hw
    · exact Or.inl (hw.finrank_eq_one v)
    · exact Or.inr (hw.finrank_eq_two v)
  have hr' : (algebraMap E w.Completion r) ^ 2 =
      algebraMap v.Completion w.Completion (algebraMap F v.Completion a) := by
    rw [← map_pow, hr]
    exact (NumberField.LiesOver.completionMap_coe (v := v) (w := w)
      (WithAbs.toAbs v.1 a)).symm
  let : CharZero v.Completion := Algebra.charZero_of_charZero F _
  refine exists_eq_iff_exists_norm ((map_ne_zero_iff (algebraMap F v.Completion)
    (algebraMap F v.Completion).injective).2 ha) hr' hdeg (fun hs => ?_) b
  obtain ⟨s, hs⟩ := hs.exists_sq
  exact (isUnramified_of_pow_eq (IsPrimitiveRoot.neg_one (R := F) 0 (by decide))
    v w hgen hr hs.symm).finrank_eq_one v

end Completions

/-- A scalar that is a square in every finite completion is a square in the number field. -/
theorem isSquare_of_all_finite {F : Type u} [Field F] [NumberField F] {a : F}
    (h : ∀ v : HeightOneSpectrum (𝓞 F), IsSquare (algebraMap F (v.adicCompletion F) a)) :
    IsSquare a := by
  by_contra hns
  let : Fact (¬ IsSquare a) := ⟨hns⟩
  let E := QuadraticAlgebra F a 0
  let : Algebra.IsQuadraticExtension F E := ⟨finrank_quadraticAlgebra a⟩
  let : NumberField E := NumberField.of_module_finite F E
  have hd : 1 < Module.finrank F E := by
    rw [Algebra.IsQuadraticExtension.finrank_eq_two F E]
    decide
  obtain ⟨v, _, w, hw, hne⟩ := Global.cyclicNonsplitPrimeStatement F E hd ∅
  let := hw
  exact hne (finite_finrank_eq_one_of_isSquare QuadraticAlgebra.adjoin_omega_eq_top (omega_sq a)
    v w (h v))

private theorem eventually_exists_localNorm_unit {F E : Type u} [Field F] [Field E]
    [NumberField F] [NumberField E] [Algebra F E] (b : Fˣ) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      ∃ c : ((placeAbove E v).1.adicCompletion E)ˣ,
        Valued.v (c : (placeAbove E v).1.adicCompletion E) = 1 ∧
        FiniteExtension.localNorm v (placeAbove E v).1 (c : (placeAbove E v).1.adicCompletion E) =
          algebraMap F (v.adicCompletion F) (b : F) := by
  let y := IdeleGroup.unitEmbedding (𝓞 F) F b
  have hval : ∀ᶠ v in cofinite, Valued.v (ideleCoordinate v y : v.adicCompletion F) = 1 := by
    filter_upwards [(ideleOrder_finite_support y).eventually_cofinite_notMem] with v hv
    exact (ideleOrder_eq_zero_iff v y).1 (by simpa only [Function.mem_support, not_ne_iff] using hv)
  filter_upwards [eventually_ramificationIdx_eq_one F E, hval] with v hv hval
  exact FiniteExtension.exists_localNorm_eq_of_ramificationIdx_eq_one v (placeAbove E v).1
    (hv _ (placeAbove E v).2) (ideleCoordinate v y) hval

/-- The equation `x² - a y² = b` is solvable at all but finitely many finite places. -/
theorem eventually_exists_eq {F : Type u} [Field F] [NumberField F] {a b : F}
    (ha : a ≠ 0) (hb : b ≠ 0) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      ∃ x y : v.adicCompletion F,
        x ^ 2 - algebraMap F (v.adicCompletion F) a * y ^ 2 = algebraMap F (v.adicCompletion F) b := by
  by_cases hs : IsSquare a
  · exact Eventually.of_forall fun v => by
      let : CharZero (v.adicCompletion F) := Algebra.charZero_of_charZero F _
      exact exists_eq_of_isSquare ((map_ne_zero (algebraMap F (v.adicCompletion F))).2 ha)
        (hs.map (algebraMap F (v.adicCompletion F)))
  let : Fact (¬ IsSquare a) := ⟨hs⟩
  let E := QuadraticAlgebra F a 0
  let : Algebra.IsQuadraticExtension F E := ⟨finrank_quadraticAlgebra a⟩
  let : NumberField E := NumberField.of_module_finite F E
  let b₀ := Units.mk0 b hb
  filter_upwards [eventually_exists_localNorm_unit (E := E) b₀] with v hv
  obtain ⟨c, _, hc⟩ := hv
  exact (finite_exists_eq_iff_exists_localNorm ha QuadraticAlgebra.adjoin_omega_eq_top (omega_sq a)
    v (placeAbove E v).1 (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom b₀)).2 ⟨c, hc⟩

/-- Cyclic Hasse norm proves the local-to-global principle for `x² - a y² = b`. -/
theorem exists_eq_of_local (hasseNorm : CyclicHasseNormStatement.{u}) :
    QuadraticNormLocalGlobalStatement.{u} := by
  intro F _ _ a b ha hb hfin hinf
  classical
  by_cases hs : IsSquare a
  · exact exists_eq_of_isSquare ha hs
  let : Fact (¬ IsSquare a) := ⟨hs⟩
  let E := QuadraticAlgebra F a 0
  let : Algebra.IsQuadraticExtension F E := ⟨finrank_quadraticAlgebra a⟩
  let : NumberField E := NumberField.of_module_finite F E
  let wf := placeAbove E (K := F)
  let wi := infinitePlaceAbove E (K := F)
  let b₀ := Units.mk0 b hb
  let y := IdeleGroup.unitEmbedding (𝓞 F) F b₀
  let good (v : HeightOneSpectrum (𝓞 F)) :=
    ∃ c : ((wf v).1.adicCompletion E)ˣ, Valued.v (c : (wf v).1.adicCompletion E) = 1 ∧
      FiniteExtension.localNorm v (wf v).1 (c : (wf v).1.adicCompletion E) =
        (y : AdeleRing (𝓞 F) F).2 v
  have hgood : ∀ᶠ v in cofinite, good v := eventually_exists_localNorm_unit (E := E) b₀
  have hfinite (v : HeightOneSpectrum (𝓞 F)) : ∃ c : ((wf v).1.adicCompletion E)ˣ,
      (good v → Valued.v (c : (wf v).1.adicCompletion E) = 1) ∧
      FiniteExtension.localNorm v (wf v).1 (c : (wf v).1.adicCompletion E) =
        (y : AdeleRing (𝓞 F) F).2 v := by
    by_cases hv : good v
    · obtain ⟨c, hc, hn⟩ := hv
      exact ⟨c, fun _ => hc, hn⟩
    · let bᵥ := Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom b₀
      obtain ⟨c, hc⟩ := (finite_exists_eq_iff_exists_localNorm ha
        QuadraticAlgebra.adjoin_omega_eq_top (omega_sq a) v (wf v).1 bᵥ).1 (hfin v)
      exact ⟨c, fun H => (hv H).elim, hc⟩
  choose c hc hcn using hfinite
  have hinfinite (v : InfinitePlace F) : ∃ d : (wi v).1.Completionˣ,
      InfiniteExtension.localNorm v (wi v).1 (d : (wi v).1.Completion) =
        (y : AdeleRing (𝓞 F) F).1 v := by
    let bᵥ := Units.map (algebraMap F v.Completion).toMonoidHom b₀
    exact (infinite_exists_eq_iff_exists_localNorm ha QuadraticAlgebra.adjoin_omega_eq_top
      (omega_sq a) v (wi v).1 bᵥ).1 (hinf v)
  choose d hdn using hinfinite
  have hci : ∀ᶠ v in cofinite,
      (c v : (wf v).1.adicCompletion E) ∈ (wf v).1.adicCompletionIntegers E ∧
        (((c v)⁻¹ : ((wf v).1.adicCompletion E)ˣ) : (wf v).1.adicCompletion E) ∈
          (wf v).1.adicCompletionIntegers E := by
    filter_upwards [hgood] with v hv
    have hval := hc v hv
    refine ⟨(mem_adicCompletionIntegers (𝓞 E) E (wf v).1).2 (le_of_eq hval), ?_⟩
    rw [mem_adicCompletionIntegers (𝓞 E) E (wf v).1, Units.val_inv_eq_inv_val, map_inv₀, hval,
      inv_one]
  obtain ⟨d₀, hd₀⟩ := mem_range_ideleNorm_of_local wf wi y c hci hcn d hdn
  obtain ⟨z, hz⟩ := hasseNorm F E b₀ d₀ hd₀
  refine ⟨(z : E).re, (z : E).im, ?_⟩
  rw [← algebraNorm]
  exact congrArg Units.val hz

end QuadraticNormLocalGlobal

end Langlands
