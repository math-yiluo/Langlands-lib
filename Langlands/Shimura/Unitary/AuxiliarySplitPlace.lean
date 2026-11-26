import Langlands.Global.Arithmetic.ChebotarevPrimeRealizationProof
import Langlands.Shimura.Unitary.NonsplitCompletionChart
import Mathlib.NumberTheory.RamificationInertia.Unramified

/-! # A split CM place outside a finite set -/

noncomputable section

namespace Langlands.Shimura.FiniteUnitary

open NumberField _root_.Algebra Langlands.Global Langlands.Global.AdelicFunctoriality
open scoped NumberField FiniteExtension

universe u v

variable {E : Type u} {K : Type v}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K] [Algebra E K] [IsQuadraticExtension E K]

omit [IsTotallyReal E] [IsTotallyComplex K] [IsQuadraticExtension E K] in
private theorem inertiaDeg_of_identityFrobenius
    (p : Langlands.Global.FinitePlace E) (q : Langlands.Global.FinitePlace K)
    [q.asIdeal.LiesOver p.asIdeal]
    (h : (RingOfIntegers.mapAlgHom (1 : K ≃ₐ[E] K)).IsArithFrobAt q.asIdeal) :
    q.asIdeal.inertiaDeg (𝓞 E) = 1 := by
  let k := 𝓞 E ⧸ p.asIdeal
  let l := 𝓞 K ⧸ q.asIdeal
  let : Field k := Ideal.Quotient.field p.asIdeal
  let : Field l := Ideal.Quotient.field q.asIdeal
  have : Finite k := Ideal.finiteQuotientOfFreeOfNeBot p.asIdeal p.ne_bot
  have : Finite l := Ideal.finiteQuotientOfFreeOfNeBot q.asIdeal q.ne_bot
  let : Fintype k := Fintype.ofFinite k
  have hf : FiniteField.frobeniusAlgHom k l = 1 := by
    ext y
    have hpow : y = y ^ Nat.card k := by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [← map_pow, Ideal.Quotient.eq]
      have ha := h a
      have hid : (RingOfIntegers.mapAlgHom (1 : K ≃ₐ[E] K)) a = a := by
        apply RingOfIntegers.ext
        rfl
      rwa [hid, ← Ideal.over_def q.asIdeal p.asIdeal] at ha
    change y ^ Fintype.card k = y
    rw [← Nat.card_eq_fintype_card]
    exact hpow.symm
  rw [Ideal.inertiaDeg_eq_of_isMaximal p.asIdeal q.asIdeal]
  change Module.finrank k l = 1
  rw [← FiniteField.orderOf_frobeniusAlgHom, hf, orderOf_one]

private theorem exists_splitPlace_not_mem (s : Finset (Langlands.Global.FinitePlace E)) :
    ∃ p, p ∉ s ∧ IsSplitPlace E K p := by
  obtain ⟨p, hp, q, hq, hu, hf⟩ := chebotarevPrimeRealizationStatement E K 1 s
  have : q.asIdeal.LiesOver p.asIdeal := hq
  have : Algebra.IsUnramifiedAt (𝓞 E) q.asIdeal := hu
  have hd : Module.finrank (FiniteCompletion E p) (FiniteCompletion K q) = 1 := by
    rw [localDegree_eq p q, Ideal.ramificationIdx_eq_one_of_isUnramifiedAt,
      inertiaDeg_of_identityFrobenius p q hf, Nat.mul_one]
  refine ⟨p, hp, ?_⟩
  by_contra! hn
  let w : FinitePlacesAbove K p := ⟨q, hq⟩
  have hw : w = placeAbove K p := eq_placeAbove_of_nonsplit p hn w
  let d (r : FinitePlacesAbove K p) :=
    Module.finrank (FiniteCompletion E p) (FiniteCompletion K r.val)
  have hd' : d w = 2 := (congrArg d hw).trans (nonsplitCompletion_finrank p hn)
  exact (by decide : (1 : ℕ) ≠ 2) (hd.symm.trans hd')

/-- A finite place outside the given support whose actual CM center splits. -/
def splitPlaceOutside (s : Finset (Langlands.Global.FinitePlace E)) :
    {p // p ∉ s ∧ IsSplitPlace E K p} :=
  ⟨(exists_splitPlace_not_mem (K := K) s).choose, (exists_splitPlace_not_mem (K := K) s).choose_spec⟩

end Langlands.Shimura.FiniteUnitary
