import Langlands.Global.Arithmetic.HarrisParityAuxiliaryFieldsStatement
import Langlands.Global.Arithmetic.SplitQuadraticAssembly
import Langlands.Global.Arithmetic.KummerRadical
import Langlands.Global.AdelicFunctoriality.UnramifiedUnitNorm
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.RingTheory.Frobenius

/-! # Split quadratic CM auxiliaries for Harris's parity argument -/

noncomputable section

universe u

namespace Langlands.Global.Harris

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IntermediateField
open AdelicFunctoriality AdelicFunctoriality.FiniteExtension
open scoped NumberField AdelicFunctoriality.FiniteExtension

section Radicands

set_option maxHeartbeats 1000000 in
private lemma prime_nonsquare_of_unramified {M : Type u} [Field M] [NumberField M]
    (q : Nat.Primes) (P : FinitePlace ℚ)
    (hq : Rat.HeightOneSpectrum.natGenerator P = q.val)
    (h : ∀ Q : FinitePlace M, Q.asIdeal.LiesOver P.asIdeal →
      Q.asIdeal.ramificationIdx (𝓞 ℚ) = 1) : ¬ IsSquare (q.val : M) := by
  let Q := placeAbove M P
  let : Q.1.asIdeal.LiesOver P.asIdeal := Q.2
  have hspan : P.asIdeal = Ideal.span {(q.val : 𝓞 ℚ)} := by
    let e := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)
    have heq := Rat.HeightOneSpectrum.span_natGenerator P
    rw [hq] at heq
    have hmap : (Ideal.span {(q.val : 𝓞 ℚ)}).map e = Ideal.span {(q.val : ℤ)} := by
      rw [Ideal.map_span, Set.image_singleton, map_natCast]
    apply e.idealComapOrderIso.symm.injective
    simpa only [RingEquiv.idealComapOrderIso_symm_apply] using heq.symm.trans hmap.symm
  have hv : P.valuation ℚ (q.val : ℚ) = WithZero.exp (-1) := by
    rw [← map_natCast (algebraMap (𝓞 ℚ) ℚ), valuation_of_algebraMap]
    exact P.intValuation_singleton (Nat.cast_ne_zero.mpr q.2.ne_zero) hspan
  have hQ : Q.1.valuation M (q.val : M) = WithZero.exp (-1) := by
    have he := valuation_liesOver M P Q.1 (q.val : ℚ)
    rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ P.ne_bot, h _ Q.2,
      pow_one, hv, map_natCast] at he
    exact he.symm
  intro hs
  obtain ⟨x, hx⟩ := hs.exists_sq
  have hval := (congrArg (Q.1.valuation M) hx).trans (map_pow _ _ _)
  have he := congrArg WithZero.log (hQ.symm.trans hval)
  simp only [WithZero.log_exp, WithZero.log_pow, two_nsmul] at he
  omega

private lemma padicSquare_of_dvd_sub (p : ℕ) [Fact p.Prime] (q : ℤ)
    (hq : (4 * p : ℤ) ∣ 1 - q) : IsSquare (algebraMap ℚ (Padic p) (q : ℚ)) := by
  obtain ⟨k, hk⟩ := hq
  have hh := congrArg (fun z : ℤ => (z : ℤ_[p])) hk
  push_cast at hh
  have hnorm : ‖(1 : ℤ_[p]) - q‖ < ‖(2 : ℤ_[p])‖ ^ 2 := by
    have h4 : ‖(4 : ℤ_[p])‖ = ‖(2 : ℤ_[p])‖ ^ 2 := by rw [← norm_pow]; norm_num
    rw [hh, norm_mul, norm_mul, h4, mul_assoc]
    apply mul_lt_of_lt_one_right (sq_pos_of_pos (norm_pos_iff.mpr (by norm_num)))
    exact (mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)).trans_lt
      (by simpa only [PadicInt.norm_p, Padic.norm_p] using (Padic.norm_p_lt_one (p := p)))
  open Polynomial in
  obtain ⟨z, hz, _⟩ := hensels_lemma
    (F := (X ^ 2 - C q : ℤ[X])) (a := (1 : ℤ_[p])) (by simpa [map_ofNat] using hnorm)
  have hz2 : z ^ 2 = (q : ℤ_[p]) := by simpa [sub_eq_zero] using hz
  refine (isSquare_iff_exists_sq _).mpr ⟨(z : Padic p), ?_⟩
  simpa using (congrArg (fun z : ℤ_[p] => (z : Padic p)) hz2).symm

/-- A single arithmetic progression enforces the Hensel bounds at every prescribed place. -/
private theorem exists_positive_radicand {E M : Type u} [Field E] [NumberField E]
    [Field M] [NumberField M] (V : Finset (FinitePlace E)) :
    ∃ d : ℚ, 0 < d ∧ ¬ IsSquare (algebraMap ℚ M d) ∧
      ∀ v ∈ V, IsSquare (algebraMap ℚ (FiniteCompletion E v) d) := by
  classical
  let m := 4 * ∏ v ∈ V, CompletionPadic.residuePrime v
  let : NeZero m := ⟨(Nat.mul_pos (by decide) (Finset.prod_pos fun v _ =>
    (CompletionPadic.residuePrime_fact v).out.pos)).ne'⟩
  let good (P : FinitePlace ℚ) := ∀ Q : FinitePlace M, Q.asIdeal.LiesOver P.asIdeal →
    Q.asIdeal.ramificationIdx (𝓞 ℚ) = 1
  have hfinite : {P | ¬ good P}.Finite :=
    Filter.eventually_cofinite.1 (eventually_ramificationIdx_eq_one ℚ M)
  let primeOf (P : FinitePlace ℚ) := (Rat.HeightOneSpectrum.primesEquiv P).val
  have hinf := Nat.infinite_setOfPred_prime_and_eq_mod (q := m) (a := 1) isUnit_one
  obtain ⟨q, ⟨⟨hq, hres⟩, hbad⟩⟩ := (hinf.sdiff (hfinite.image primeOf)).nonempty
  let P : FinitePlace ℚ := Rat.HeightOneSpectrum.primesEquiv.symm ⟨q, hq⟩
  have hgood : good P := by
    by_contra hP
    exact hbad ⟨P, hP, congrArg Subtype.val (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply _)⟩
  refine ⟨(q : ℚ), Nat.cast_pos.mpr hq.pos, ?_, ?_⟩
  · have hgen : Rat.HeightOneSpectrum.natGenerator P = q :=
      congrArg Subtype.val (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply ⟨q, hq⟩)
    simpa using (prime_nonsquare_of_unramified (M := M) ⟨q, hq⟩ P hgen hgood)
  · intro v hv
    have hcong : ((q : ℤ) : ZMod m) = (1 : ℤ) := by simpa using hres
    have hdiv : (m : ℤ) ∣ 1 - (q : ℤ) :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub (q : ℤ) 1 m).mp hcong
    have hpdiv : 4 * CompletionPadic.residuePrime v ∣ m :=
      Nat.mul_dvd_mul_left 4 (Finset.dvd_prod_of_mem _ hv)
    have hd : (4 * (CompletionPadic.residuePrime v : ℤ)) ∣ 1 - (q : ℤ) := by
      exact (by exact_mod_cast hpdiv : (4 * (CompletionPadic.residuePrime v : ℤ)) ∣ (m : ℤ)).trans hdiv
    have hsq := (padicSquare_of_dvd_sub _ (q : ℤ) hd).map (CompletionPadic.padicMap v)
    simpa only [map_natCast, Int.cast_natCast] using hsq

end Radicands

section QuadraticField

variable {E : Type u} [Field E] [NumberField E]

private def rootField {d : ℚ} {x : AlgebraicClosure E}
    (hx : x ^ 2 = algebraMap ℚ (AlgebraicClosure E) d)
    (hd : ¬ IsSquare (algebraMap ℚ E d)) : FiniteGaloisIntermediateField E (AlgebraicClosure E) := by
  have hxE : x ^ 2 = algebraMap E (AlgebraicClosure E) (algebraMap ℚ E d) := by
    rwa [← IsScalarTower.algebraMap_apply]
  haveI := adjoin.finiteDimensional (squareRoot_isIntegral hxE)
  haveI : Algebra.IsQuadraticExtension E E⟮x⟯ := ⟨squareRoot_finrank hd hxE⟩
  exact ⟨E⟮x⟯⟩

private lemma rootField_degree {d : ℚ} {x : AlgebraicClosure E}
    (hx : x ^ 2 = algebraMap ℚ (AlgebraicClosure E) d)
    (hd : ¬ IsSquare (algebraMap ℚ E d)) : Module.finrank E (rootField hx hd) = 2 :=
  squareRoot_finrank hd (by rwa [← IsScalarTower.algebraMap_apply])

private lemma rootField_le_iff {d : ℚ} {x : AlgebraicClosure E}
    (hx : x ^ 2 = algebraMap ℚ (AlgebraicClosure E) d)
    (hd : ¬ IsSquare (algebraMap ℚ E d))
    (L : FiniteGaloisIntermediateField E (AlgebraicClosure E)) :
    rootField hx hd ≤ L ↔ x ∈ L.toIntermediateField := by
  change E⟮x⟯ ≤ L.toIntermediateField ↔ _
  exact adjoin_simple_le_iff

private lemma rootField_mem {d : ℚ} {x : AlgebraicClosure E}
    (hx : x ^ 2 = algebraMap ℚ (AlgebraicClosure E) d)
    (hd : ¬ IsSquare (algebraMap ℚ E d)) : x ∈ (rootField hx hd).toIntermediateField :=
  mem_adjoin_simple_self E x

private lemma rootField_gen_sq {d : ℚ} {x : AlgebraicClosure E}
    (hx : x ^ 2 = algebraMap ℚ (AlgebraicClosure E) d)
    (hd : ¬ IsSquare (algebraMap ℚ E d)) :
    (AdjoinSimple.gen E x : rootField hx hd) ^ 2 = algebraMap ℚ (rootField hx hd) d := by
  apply Subtype.ext
  change x ^ 2 = algebraMap ℚ (AlgebraicClosure E) d
  exact hx

private lemma rootField_adjoin {d : ℚ} {x : AlgebraicClosure E}
    (hx : x ^ 2 = algebraMap ℚ (AlgebraicClosure E) d)
    (hd : ¬ IsSquare (algebraMap ℚ E d)) :
    Algebra.adjoin E ({AdjoinSimple.gen E x} : Set (rootField hx hd)) = ⊤ := by
  change Algebra.adjoin E ({AdjoinSimple.gen E x} : Set E⟮x⟯) = ⊤
  have hxE : x ^ 2 = algebraMap E (AlgebraicClosure E) (algebraMap ℚ E d) := by
    rwa [← IsScalarTower.algebraMap_apply]
  simpa only [adjoin.powerBasis_gen] using (adjoin.powerBasis (squareRoot_isIntegral hxE)).adjoin_gen_eq_top

private lemma not_mem_of_nonsquare {d : ℚ} {x : AlgebraicClosure E}
    (hx : x ^ 2 = algebraMap ℚ (AlgebraicClosure E) d)
    (M : FiniteGaloisIntermediateField E (AlgebraicClosure E))
    (hd : ¬ IsSquare (algebraMap ℚ M d)) : x ∉ M.toIntermediateField := by
  intro hxM
  apply hd
  refine (isSquare_iff_exists_sq _).mpr ⟨⟨x, hxM⟩, ?_⟩
  exact Subtype.ext (by simpa using hx.symm)

private lemma rootField_inf_eq_bot {d : ℚ} {x : AlgebraicClosure E}
    (hx : x ^ 2 = algebraMap ℚ (AlgebraicClosure E) d)
    (hd : ¬ IsSquare (algebraMap ℚ E d))
    (M : FiniteGaloisIntermediateField E (AlgebraicClosure E))
    (hM : ¬ IsSquare (algebraMap ℚ M d)) : rootField hx hd ⊓ M = ⊥ := by
  let N := rootField hx hd
  have hle : (N ⊓ M).toIntermediateField ≤ N.toIntermediateField := inf_le_left
  have hsimple := isSimpleOrder_of_finrank_prime E N ((rootField_degree hx hd).symm ▸ Nat.prime_two)
  rcases hsimple.eq_bot_or_eq_top (restrict hle) with hb | ht
  · apply FiniteGaloisIntermediateField.val_injective
    change (N ⊓ M).toIntermediateField = (⊥ : IntermediateField E (AlgebraicClosure E))
    simpa only [lift_restrict, lift_bot] using congrArg lift hb
  · exfalso
    apply not_mem_of_nonsquare hx M hM
    have heq : (N ⊓ M).toIntermediateField = N.toIntermediateField := by
      simpa only [lift_restrict, lift_top] using congrArg lift ht
    have hxN : x ∈ N.toIntermediateField := mem_adjoin_simple_self E x
    have hxInf : x ∈ (N ⊓ M).toIntermediateField := heq.symm ▸ hxN
    exact (inf_le_right : (N ⊓ M).toIntermediateField ≤ M.toIntermediateField) hxInf

private lemma rootField_splits {d : ℚ} {x : AlgebraicClosure E}
    (hx : x ^ 2 = algebraMap ℚ (AlgebraicClosure E) d)
    (hd : ¬ IsSquare (algebraMap ℚ E d))
    (v : FinitePlace E) (hv : IsSquare (algebraMap ℚ (FiniteCompletion E v) d)) :
    letI : NumberField (rootField hx hd) := NumberField.of_module_finite E (rootField hx hd)
    SplitsCompletelyAt (N := rootField hx hd) v := by
  let N := rootField hx hd
  let : NumberField N := NumberField.of_module_finite E N
  intro w hw
  obtain ⟨s, hs⟩ := hv.exists_sq
  exact Arithmetic.KummerRadical.finrank_adicCompletion_eq_one
    (a := algebraMap ℚ E d) (IsPrimitiveRoot.neg_one (R := E) 0 (by decide))
    (rootField_adjoin hx hd)
    (by rw [← IsScalarTower.algebraMap_apply ℚ E N]; exact rootField_gen_sq hx hd)
    v w (by rw [← IsScalarTower.algebraMap_apply ℚ E (v.adicCompletion E)]; exact hs.symm)

private lemma rootField_isParityAuxiliary [IsCMField E] (E₀ K₀ : IntermediateField ℚ E)
    [IsTotallyReal E₀] (hK₀ : Module.finrank ℚ K₀ = 2) (hjoin : E₀ ⊔ K₀ = ⊤)
    {d : ℚ} {x : AlgebraicClosure E} (hdpos : 0 < d)
    (hx : x ^ 2 = algebraMap ℚ (AlgebraicClosure E) d)
    (hd : ¬ IsSquare (algebraMap ℚ E d)) : IsParityAuxiliary E₀ K₀ (rootField hx hd) := by
  let N := rootField hx hd
  let : NumberField N := NumberField.of_module_finite E N
  let f := IsScalarTower.toAlgHom ℚ E N
  let r : N := AdjoinSimple.gen E x
  let R := rationalRootField r
  let B := E₀.map f
  let N₀ : IntermediateField ℚ N := B ⊔ R
  let : IsTotallyReal B := IsTotallyReal.ofRingEquiv (E₀.equivMap f).toRingEquiv
  let : IsTotallyReal R := rationalRootField_totallyReal hdpos (rootField_gen_sq hx hd)
  have hreal : IsTotallyReal N₀ := by
    change IsTotallyReal N₀.toSubfield
    rw [isTotallyReal_iff_le_maximalRealSubfield]
    let F : IntermediateField ℚ N := (maximalRealSubfield N).toIntermediateField
      (fun a => by simp)
    exact (sup_le (show B ≤ F from IsTotallyReal.le_maximalRealSubfield B.toSubfield)
      (show R ≤ F from IsTotallyReal.le_maximalRealSubfield R.toSubfield) : N₀ ≤ F)
  have hdB : ¬ IsSquare (algebraMap ℚ B d) := by
    intro hs
    let g : B →ₐ[ℚ] E := E₀.val.comp (E₀.equivMap f).symm.toAlgHom
    have h := hs.map g
    rw [g.commutes] at h
    exact hd h
  have hrealDegree : Module.finrank ℚ N₀ = 2 * Module.finrank ℚ E₀ := by
    rw [show Module.finrank ℚ N₀ = Module.finrank ℚ B * 2 from
      squareRoot_sup_finrank B hdB (rootField_gen_sq hx hd),
      ← (E₀.equivMap f).toLinearEquiv.finrank_eq, mul_comm]
  have hNtop : N₀ ⊔ K₀.map f = ⊤ := by
    apply top_unique
    intro y htop
    clear htop
    have hy : y ∈ Algebra.adjoin E {r} := (rootField_adjoin hx hd).symm ▸ Algebra.mem_top
    have hbase : ∀ a : E, f a ∈ N₀ ⊔ K₀.map f := by
      intro a
      apply sup_le_sup_right (le_sup_left : B ≤ N₀) (K₀.map f)
      rw [show B = E₀.map f from rfl, ← IntermediateField.map_sup, hjoin]
      exact ⟨a, trivial, rfl⟩
    induction hy using Algebra.adjoin_induction with
    | mem z hz =>
      obtain rfl := Set.mem_singleton_iff.mp hz
      have hle : R ≤ N₀ ⊔ K₀.map f := (le_sup_right : R ≤ N₀).trans le_sup_left
      exact hle (mem_adjoin_simple_self ℚ r)
    | algebraMap a => exact hbase a
    | add a b _ _ ha hb => exact IntermediateField.add_mem _ ha hb
    | mul a b _ _ ha hb => exact IntermediateField.mul_mem _ ha hb
  have hEbound : Module.finrank ℚ E ≤ Module.finrank ℚ E₀ * 2 := by
    let e := (IntermediateField.equivOfEq hjoin).trans IntermediateField.topEquiv
    have heq := e.toLinearEquiv.finrank_eq
    rw [← heq, ← hK₀]
    exact finrank_sup_le E₀ K₀
  have hNtower := Module.finrank_mul_finrank ℚ E N
  have hNrealTower := Module.finrank_mul_finrank ℚ N₀ N
  have hrealpos : 0 < Module.finrank ℚ E₀ := Module.finrank_pos
  let : IsTotallyComplex N := isTotallyComplex_of_algebra E N
  have hnotOne : Module.finrank N₀ N ≠ 1 := by
    intro h
    have ht := IntermediateField.finrank_eq_one_iff_eq_top.mp h
    let : IsTotallyReal N := IsTotallyReal.ofRingEquiv
      ((IntermediateField.equivOfEq ht).trans IntermediateField.topEquiv).toRingEquiv
    let w : InfinitePlace N := Classical.choice inferInstance
    exact (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w))
      (IsTotallyReal.isReal w)
  have hreldeg : Module.finrank N₀ N = 2 := by
    have hpos : 0 < Module.finrank N₀ N := Module.finrank_pos
    rw [show Module.finrank E N = 2 from rootField_degree hx hd] at hNtower
    rw [hrealDegree] at hNrealTower
    by_contra h
    have h3 : 3 ≤ Module.finrank N₀ N := by omega
    nlinarith
  let : IsTotallyReal N₀ := hreal
  let : Algebra.IsQuadraticExtension N₀ N := ⟨hreldeg⟩
  exact ⟨rootField_degree hx hd, IsCMField.ofCMExtension N₀ N, N₀, le_sup_left,
    hreal, hrealDegree, hNtop⟩

end QuadraticField

section FrobeniusCover

variable {E : Type u} [Field E] [NumberField E]

/-- At an unramified place, a Frobenius fixing the embedded field gives local degree one. -/
private lemma splits_of_frobenius_fixes {N L : Type u} [Field N] [NumberField N]
    [Field L] [NumberField L] [Algebra E N] [Algebra E L] [Algebra N L]
    [IsScalarTower E N L] [IsGalois E N] [IsGalois E L] (v : FinitePlace E) (Q : FinitePlace L)
    [Q.asIdeal.LiesOver v.asIdeal] (σ : Gal(L/E))
    (hσ : IsArithFrobAt (𝓞 E) σ Q.asIdeal)
    (hunram : Q.asIdeal.ramificationIdx (𝓞 E) = 1)
    (hfix : ∀ a : N, σ (algebraMap N L a) = algebraMap N L a) :
    SplitsCompletelyAt (N := N) v := by
  let w := Q.under (𝓞 N)
  have : Q.asIdeal.LiesOver w.asIdeal := Ideal.over_under Q.asIdeal
  have : w.asIdeal.LiesOver v.asIdeal :=
    Ideal.under_liesOver_of_liesOver (𝓞 N) Q.asIdeal v.asIdeal
  have he : w.asIdeal.ramificationIdx (𝓞 E) = 1 := by
    have hd := Ideal.ramificationIdx_below_dvd (R := 𝓞 E) w.asIdeal Q.asIdeal
    exact Nat.dvd_one.mp (hunram ▸ hd)
  have hpow : ∀ y : (𝓞 N ⧸ w.asIdeal), y = y ^ Nat.card (𝓞 E ⧸ v.asIdeal) := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_pow, Ideal.Quotient.eq]
    change _ ∈ Q.asIdeal.comap (algebraMap (𝓞 N) (𝓞 L))
    rw [Ideal.mem_comap, map_sub, map_pow]
    have hf := hσ (algebraMap (𝓞 N) (𝓞 L) a)
    change σ • (algebraMap (𝓞 N) (𝓞 L) a) -
      (algebraMap (𝓞 N) (𝓞 L) a) ^ Nat.card (𝓞 E ⧸ Q.asIdeal.under (𝓞 E)) ∈ Q.asIdeal at hf
    have hfixed : σ • (algebraMap (𝓞 N) (𝓞 L) a) = algebraMap (𝓞 N) (𝓞 L) a :=
      RingOfIntegers.ext (hfix (a : N))
    rwa [← Ideal.over_def Q.asIdeal v.asIdeal, hfixed] at hf
  let k := 𝓞 E ⧸ v.asIdeal
  let l := 𝓞 N ⧸ w.asIdeal
  let : Field k := Ideal.Quotient.field v.asIdeal
  let : Field l := Ideal.Quotient.field w.asIdeal
  have : Finite k := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  have : Finite l := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  let : Fintype k := Fintype.ofFinite k
  have hFrob : FiniteField.frobeniusAlgHom k l = 1 := by
    ext y
    change y ^ Fintype.card k = y
    rw [← Nat.card_eq_fintype_card]
    exact (hpow y).symm
  have hf : w.asIdeal.inertiaDeg (𝓞 E) = 1 := by
    rw [Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal w.asIdeal]
    change Module.finrank k l = 1
    rw [← FiniteField.orderOf_frobeniusAlgHom, hFrob, orderOf_one]
  intro w' hw'
  rw [localDegree_eq v w',
    Ideal.ramificationIdx_eq_of_isGaloisGroup v.asIdeal w'.asIdeal w.asIdeal Gal(N/E),
    Ideal.inertiaDeg_eq_of_isGaloisGroup v.asIdeal w'.asIdeal w.asIdeal Gal(N/E), he, hf,
    Nat.mul_one]

/-- Fixing the image of the square root fixes the image of its entire simple extension. -/
private lemma rootField_splits_of_frobenius_fixes {d : ℚ} {x : AlgebraicClosure E}
    (hx : x ^ 2 = algebraMap ℚ (AlgebraicClosure E) d) (hd : ¬ IsSquare (algebraMap ℚ E d))
    (L : FiniteGaloisIntermediateField E (AlgebraicClosure E)) (hle : rootField hx hd ≤ L)
    [NumberField L] (v : FinitePlace E) (Q : FinitePlace L) [Q.asIdeal.LiesOver v.asIdeal]
    (σ : Gal(L/E)) (hσ : IsArithFrobAt (𝓞 E) σ Q.asIdeal)
    (hunram : Q.asIdeal.ramificationIdx (𝓞 E) = 1)
    (hfix : σ ⟨x, (rootField_le_iff hx hd L).mp hle⟩ = ⟨x, (rootField_le_iff hx hd L).mp hle⟩) :
    letI : NumberField (rootField hx hd) := NumberField.of_module_finite E (rootField hx hd)
    SplitsCompletelyAt (N := rootField hx hd) v := by
  let N := rootField hx hd
  let : NumberField N := NumberField.of_module_finite E N
  let i : N →ₐ[E] L := inclusion hle
  let : Algebra N L := i.toAlgebra
  have : IsScalarTower E N L := IsScalarTower.of_algebraMap_eq' i.comp_algebraMap.symm
  apply splits_of_frobenius_fixes v Q σ hσ hunram
  have h : σ.toAlgHom.comp i = i := by
    apply AlgHom.ext_of_adjoin_eq_top (rootField_adjoin hx hd)
    intro y hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    exact hfix
  exact fun a => AlgHom.congr_fun h a

/-- Frobenius in the compositum has a positive sign on one of the two roots or their product. -/
private lemma rootFields_cover {d₁ d₂ : ℚ} {x₁ x₂ : AlgebraicClosure E}
    (hx₁ : x₁ ^ 2 = algebraMap ℚ (AlgebraicClosure E) d₁)
    (hx₂ : x₂ ^ 2 = algebraMap ℚ (AlgebraicClosure E) d₂)
    (hx₃ : (x₁ * x₂) ^ 2 = algebraMap ℚ (AlgebraicClosure E) (d₁ * d₂))
    (hd₁ : ¬ IsSquare (algebraMap ℚ E d₁)) (hd₂ : ¬ IsSquare (algebraMap ℚ E d₂))
    (hd₃ : ¬ IsSquare (algebraMap ℚ E (d₁ * d₂))) :
    ∃ T : Finset (FinitePlace E), ∀ v ∉ T, ∃ i : Fin 3,
      let N := ![rootField hx₁ hd₁, rootField hx₂ hd₂, rootField hx₃ hd₃] i
      letI : NumberField N := NumberField.of_module_finite E N
      SplitsCompletelyAt (N := N) v := by
  classical
  let N₁ := rootField hx₁ hd₁
  let N₂ := rootField hx₂ hd₂
  let L := N₁ ⊔ N₂
  let : NumberField L := NumberField.of_module_finite E L
  have hle₁ : N₁ ≤ L := le_sup_left
  have hle₂ : N₂ ≤ L := le_sup_right
  let r₁ : L := ⟨x₁, (rootField_le_iff hx₁ hd₁ L).mp hle₁⟩
  let r₂ : L := ⟨x₂, (rootField_le_iff hx₂ hd₂ L).mp hle₂⟩
  have hle₃ : rootField hx₃ hd₃ ≤ L := (rootField_le_iff hx₃ hd₃ L).mpr (r₁ * r₂).2
  let good (v : FinitePlace E) := ∀ Q : FinitePlace L, Q.asIdeal.LiesOver v.asIdeal →
    Q.asIdeal.ramificationIdx (𝓞 E) = 1
  have hfinite : {v | ¬ good v}.Finite :=
    Filter.eventually_cofinite.1 (eventually_ramificationIdx_eq_one E L)
  refine ⟨hfinite.toFinset, fun v hv => ?_⟩
  have hgood : good v := by
    by_contra h
    exact hv (hfinite.mem_toFinset.mpr h)
  let Q := placeAbove L v
  let : Q.1.asIdeal.LiesOver v.asIdeal := Q.2
  have : Finite (𝓞 L ⧸ Q.1.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ Q.1.ne_bot
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 E) Gal(L/E) Q.1.asIdeal
  have hunram := hgood Q.1 Q.2
  have sign {d : ℚ} {r : L} (hr : r ^ 2 = algebraMap ℚ L d) :
      σ r = r ∨ σ r = -r := by
    apply sq_eq_sq_iff_eq_or_eq_neg.mp
    rw [← map_pow, hr]
    exact σ.toRingEquiv.toRingHom.toRatAlgHom.commutes d
  rcases sign (show r₁ ^ 2 = algebraMap ℚ L d₁ from Subtype.ext hx₁) with h₁ | h₁
  · exact ⟨0, rootField_splits_of_frobenius_fixes hx₁ hd₁ L hle₁ v Q.1 σ hσ hunram h₁⟩
  rcases sign (show r₂ ^ 2 = algebraMap ℚ L d₂ from Subtype.ext hx₂) with h₂ | h₂
  · exact ⟨1, rootField_splits_of_frobenius_fixes hx₂ hd₂ L hle₂ v Q.1 σ hσ hunram h₂⟩
  have h₃ : σ (r₁ * r₂) = r₁ * r₂ := by rw [map_mul, h₁, h₂, neg_mul_neg]
  exact ⟨2, rootField_splits_of_frobenius_fixes hx₃ hd₃ L hle₃ v Q.1 σ hσ hunram h₃⟩

end FrobeniusCover

private lemma nonsquare_base {E M : Type u} [Field E] [Field M] [CharZero E] [CharZero M]
    [Algebra E M] {d : ℚ} (hd : ¬ IsSquare (algebraMap ℚ M d)) :
    ¬ IsSquare (algebraMap ℚ E d) := by
  intro h
  let f := IsScalarTower.toAlgHom ℚ E M
  have hs := h.map f
  rw [f.commutes] at hs
  exact hd hs

/-- The disjoint supply and the three-field cover of split quadratic CM auxiliaries. -/
theorem harrisParityAuxiliaryFields : HarrisParityAuxiliaryFieldsStatement := by
  classical
  intro E _ _ _ E₀ K₀ hE₀ hK₀ _ hjoin V
  let : IsTotallyReal E₀ := hE₀
  constructor
  · intro M
    let : NumberField M := NumberField.of_module_finite E M
    obtain ⟨d, hdpos, hdM, hdV⟩ := exists_positive_radicand (M := M) V
    have hd : ¬ IsSquare (algebraMap ℚ E d) := nonsquare_base hdM
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap ℚ (AlgebraicClosure E) d) zero_lt_two
    exact ⟨rootField hx hd, rootField_inf_eq_bot hx hd M hdM,
      rootField_isParityAuxiliary E₀ K₀ hK₀ hjoin hdpos hx hd,
      fun v hv => rootField_splits hx hd v (hdV v hv)⟩
  obtain ⟨d₁, hd₁pos, hd₁, hd₁V⟩ := exists_positive_radicand (M := E) V
  obtain ⟨x₁, hx₁⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap ℚ (AlgebraicClosure E) d₁) zero_lt_two
  let N₁ := rootField hx₁ hd₁
  let : NumberField N₁ := NumberField.of_module_finite E N₁
  obtain ⟨d₂, hd₂pos, hd₂N₁, hd₂V⟩ := exists_positive_radicand (M := N₁) V
  have hd₂ : ¬ IsSquare (algebraMap ℚ E d₂) := nonsquare_base hd₂N₁
  obtain ⟨x₂, hx₂⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap ℚ (AlgebraicClosure E) d₂) zero_lt_two
  let N₂ := rootField hx₂ hd₂
  have hx₃ : (x₁ * x₂) ^ 2 = algebraMap ℚ (AlgebraicClosure E) (d₁ * d₂) := by
    rw [mul_pow, hx₁, hx₂, map_mul]
  have hd₃ : ¬ IsSquare (algebraMap ℚ E (d₁ * d₂)) := by
    intro h
    let f := IsScalarTower.toAlgHom ℚ E N₁
    have hs := h.map f
    rw [f.commutes] at hs
    have h₁ : IsSquare (algebraMap ℚ N₁ d₁) := (isSquare_iff_exists_sq _).mpr
      ⟨AdjoinSimple.gen E x₁, (rootField_gen_sq hx₁ hd₁).symm⟩
    have h₂ := hs.div h₁
    rw [← map_div₀, mul_div_cancel_left₀ _ hd₁pos.ne'] at h₂
    exact hd₂N₁ h₂
  let N₃ := rootField hx₃ hd₃
  have hx₁ne : x₁ ≠ 0 := by
    intro h
    apply hd₁pos.ne'
    apply (algebraMap ℚ (AlgebraicClosure E)).injective
    simpa [h] using hx₁.symm
  have hx₂ne : x₂ ≠ 0 := by
    intro h
    apply hd₂pos.ne'
    apply (algebraMap ℚ (AlgebraicClosure E)).injective
    simpa [h] using hx₂.symm
  have hx₂not : x₂ ∉ N₁.toIntermediateField := not_mem_of_nonsquare hx₂ N₁ hd₂N₁
  have hne₁₂ : N₁ ≠ N₂ := by
    intro h
    exact hx₂not (h.symm ▸ rootField_mem hx₂ hd₂)
  have hne₃₁ : N₃ ≠ N₁ := by
    intro h
    have hm : x₁ * x₂ ∈ N₁.toIntermediateField := h ▸ rootField_mem hx₃ hd₃
    have hdiv := IntermediateField.div_mem N₁.toIntermediateField hm (rootField_mem hx₁ hd₁)
    rw [mul_div_cancel_left₀ _ hx₁ne] at hdiv
    exact hx₂not hdiv
  have hne₃₂ : N₃ ≠ N₂ := by
    intro h
    have hm : x₁ * x₂ ∈ N₂.toIntermediateField := h ▸ rootField_mem hx₃ hd₃
    have hdiv := IntermediateField.div_mem N₂.toIntermediateField hm (rootField_mem hx₂ hd₂)
    rw [mul_div_cancel_right₀ _ hx₂ne] at hdiv
    have hle : N₁ ≤ N₂ := (rootField_le_iff hx₁ hd₁ N₂).mpr hdiv
    apply hne₁₂
    apply FiniteGaloisIntermediateField.val_injective
    exact IntermediateField.eq_of_le_of_finrank_eq hle
      ((rootField_degree hx₁ hd₁).trans (rootField_degree hx₂ hd₂).symm)
  obtain ⟨T, hcover⟩ := rootFields_cover hx₁ hx₂ hx₃ hd₁ hd₂ hd₃
  refine ⟨![N₁, N₂, N₃], T, ?_, ?_, hcover⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> intro h
    all_goals first
      | rfl
      | exact (hne₁₂ h).elim
      | exact (hne₁₂ h.symm).elim
      | exact (hne₃₁ h).elim
      | exact (hne₃₁ h.symm).elim
      | exact (hne₃₂ h).elim
      | exact (hne₃₂ h.symm).elim
  · intro i
    fin_cases i
    · exact ⟨rootField_isParityAuxiliary E₀ K₀ hK₀ hjoin hd₁pos hx₁ hd₁,
        fun v hv => rootField_splits hx₁ hd₁ v (hd₁V v hv)⟩
    · exact ⟨rootField_isParityAuxiliary E₀ K₀ hK₀ hjoin hd₂pos hx₂ hd₂,
        fun v hv => rootField_splits hx₂ hd₂ v (hd₂V v hv)⟩
    · exact ⟨rootField_isParityAuxiliary E₀ K₀ hK₀ hjoin (mul_pos hd₁pos hd₂pos) hx₃ hd₃,
        fun v hv => rootField_splits hx₃ hd₃ v (by rw [map_mul]; exact (hd₁V v hv).mul (hd₂V v hv))⟩

end Langlands.Global.Harris
