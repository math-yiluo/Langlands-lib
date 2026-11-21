import Langlands.Automorphic.Unramified.IsobaricWeakTransfer
import Langlands.Global.AdelicFunctoriality.UnramifiedUnitNorm

/-! # Weak base change of sums of isobaric data -/

noncomputable section

open scoped BigOperators NumberField

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.IsobaricData

open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Unramified

private def emptySpectrum {I : Type*} : SpectralSystem I 0 :=
  ⟨∅, fun _ _ => Sym.nil⟩

private def addSpectrum {I : Type*} {n m : ℕ}
    (s : SpectralSystem I n) (t : SpectralSystem I m) : SpectralSystem I (n + m) := by
  classical
  exact {
    exceptional := s.exceptional ∪ t.exceptional
    eigenvalues := fun v hv =>
      (s.eigenvalues v (fun h => hv (Finset.mem_union_left _ h))).directSum
        (t.eigenvalues v (fun h => hv (Finset.mem_union_right _ h))) }

private theorem addSpectrum_eulerPolynomial {I : Type*} {n m : ℕ}
    (s : SpectralSystem I n) (t : SpectralSystem I m) (v : I)
    (hv : v ∉ (addSpectrum s t).exceptional)
    (hs : v ∉ s.exceptional) (ht : v ∉ t.exceptional) :
    (addSpectrum s t).eulerPolynomial v hv = s.eulerPolynomial v hs * t.eulerPolynomial v ht :=
  Eigenvalues.eulerPolynomial_directSum _ _

private theorem sameEulerPolynomials_transport {I : Type*} {n m : ℕ}
    (h : n = m) (s : SpectralSystem I n) :
    s.SameEulerPolynomials (h ▸ s : SpectralSystem I m) := by
  subst m
  exact SpectralSystem.sameEulerPolynomials_refl s

section Datum

variable {F : Type uF} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

private theorem hasSpectralSystem_zero :
    HasSpectralSystem.{uF, uV} (0 : IsobaricData F) (emptySpectrum (I := FinitePlace F)) := by
  let a (i : Fin 0) : SpectralSystem (FinitePlace F)
      (Fin.elim0 i : PositiveRankCuspidalClass F).rank := i.elim0
  refine ⟨0, Fin.elim0, by simp, a, fun i => i.elim0, ?_⟩
  exact Filter.Eventually.of_forall fun v hv hw => by
    change (SpectralSystem.finiteSum a).eulerPolynomial v hv =
      (emptySpectrum (I := FinitePlace F)).eulerPolynomial v hw
    rw [SpectralSystem.finiteSum_eulerPolynomial a v hv]
    simp [emptySpectrum, SpectralSystem.eulerPolynomial, Eigenvalues.eulerPolynomial, Sym.nil]

private theorem hasSpectralSystem_add
    {D D' : IsobaricData F}
    {s : SpectralSystem (FinitePlace F) D.rank} {t : SpectralSystem (FinitePlace F) D'.rank}
    (hs : HasSpectralSystem.{uF, uV} D s) (ht : HasSpectralSystem.{uF, uV} D' t) :
    HasSpectralSystem.{uF, uV} (D + D') ((rank_add D D').symm ▸ addSpectrum s t) := by
  classical
  obtain ⟨p, c, hc, a, ha, has⟩ := hs
  obtain ⟨q, d, hd, b, hb, hbt⟩ := ht
  let Attached := Σ x : PositiveRankCuspidalClass F,
    {z : SpectralSystem (FinitePlace F) x.rank // x.HasSpectralSystem.{uF, uV} z}
  let left (i : Fin p) : Attached := ⟨c i, a i, ha i⟩
  let right (i : Fin q) : Attached := ⟨d i, b i, hb i⟩
  let combined := Fin.append left right
  let ab (i : Fin (p + q)) := (combined i).2.1
  refine ⟨p + q, fun i => (combined i).1, ?_, ab, fun i => (combined i).2.2, ?_⟩
  · rw [← hc, ← hd]
    simp only [Fin.univ_val_map, List.ofFn_add, combined, Fin.append_left', Fin.append_right,
      left, right, Multiset.coe_add]
  refine (show (SpectralSystem.finiteSum ab).SameEulerPolynomials (addSpectrum s t) from ?_).trans
    (sameEulerPolynomials_transport (rank_add D D').symm (addSpectrum s t))
  filter_upwards [has, hbt, (SpectralSystem.finiteSum a).exceptional.eventually_cofinite_notMem,
    (SpectralSystem.finiteSum b).exceptional.eventually_cofinite_notMem] with v h₁ h₂ hv₁ hv₂
  intro hv hst
  have hs' : v ∉ s.exceptional := fun h => hst (Finset.mem_union_left _ h)
  have ht' : v ∉ t.exceptional := fun h => hst (Finset.mem_union_right _ h)
  have euler_eq {x y : Attached} (h : x = y)
      (hx : v ∉ x.2.1.exceptional) (hy : v ∉ y.2.1.exceptional) :
      x.2.1.eulerPolynomial v hx = y.2.1.eulerPolynomial v hy := by
    subst y
    rfl
  rw [SpectralSystem.finiteSum_eulerPolynomial ab v hv, Fin.prod_univ_add,
    addSpectrum_eulerPolynomial s t v hst hs' ht', ← h₁ hv₁ hs', ← h₂ hv₂ ht',
    SpectralSystem.finiteSum_eulerPolynomial a v hv₁,
    SpectralSystem.finiteSum_eulerPolynomial b v hv₂]
  congr 1
  · exact Finset.prod_congr rfl fun i _ => euler_eq (Fin.append_left left right i) _ _
  · exact Finset.prod_congr rfl fun i _ => euler_eq (Fin.append_right left right i) _ _

end Datum

section Transfer

/-- Unitary weak base change for each singleton gives unitary weak base change
for all isobaric data over the same extension. -/
def UnitaryWeakBaseChangeSumStatement (F : Type uF) (E : Type uE)
    [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)] : Prop :=
  (∀ c : PositiveRankCuspidalClass F, (ofCuspidal c).IsUnitary →
    ∃ A : IsobaricData E, A.IsUnitary ∧
      IsWeakBaseChangeOf.{uF, uE, uV, uW} A (ofCuspidal c)) →
  ∀ D : IsobaricData F, D.IsUnitary →
    ∃ A : IsobaricData E, A.IsUnitary ∧ IsWeakBaseChangeOf.{uF, uE, uV, uW} A D

variable {F : Type uF} {E : Type uE} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E]

omit [NumberField F] in
private theorem arithmeticWeakBaseChange_add {n₁ n₂ m₁ m₂ n m : ℕ}
    {s₁ : SpectralSystem (FinitePlace F) n₁} {s₂ : SpectralSystem (FinitePlace F) n₂}
    {t₁ : SpectralSystem (FinitePlace E) m₁} {t₂ : SpectralSystem (FinitePlace E) m₂}
    (hf : n₁ + n₂ = n) (he : m₁ + m₂ = m) (h₁ : m₁ = n₁) (h₂ : m₂ = n₂)
    (hbc₁ : SpectralSystem.IsArithmeticWeakBaseChangeOf (h₁ ▸ t₁) s₁)
    (hbc₂ : SpectralSystem.IsArithmeticWeakBaseChangeOf (h₂ ▸ t₂) s₂) :
    SpectralSystem.IsArithmeticWeakBaseChangeOf
      (he.symm.trans ((congrArg₂ Nat.add h₁ h₂).trans hf) ▸ (he ▸ addSpectrum t₁ t₂))
      (hf ▸ addSpectrum s₁ s₂) := by
  classical
  subst m₁ m₂ n m
  filter_upwards [hbc₁, hbc₂] with v hv₁ hv₂
  obtain ⟨hs₁, ht₁, hram, hst₁⟩ := hv₁
  obtain ⟨hs₂, ht₂, -, hst₂⟩ := hv₂
  refine ⟨Finset.notMem_union.mpr ⟨hs₁, hs₂⟩,
    fun w => Finset.notMem_union.mpr ⟨ht₁ w, ht₂ w⟩, hram, ?_⟩
  intro w
  change (t₁.eigenvalues w.1 (ht₁ w)).directSum (t₂.eigenvalues w.1 (ht₂ w)) =
    ((s₁.eigenvalues v hs₁).directSum (s₂.eigenvalues v hs₂)).power _
  rw [Eigenvalues.power_directSum]
  exact congrArg₂ Eigenvalues.directSum (hst₁ w) (hst₂ w)

variable [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)]

/-- The empty isobaric data transfer to the empty data along any number-field extension. -/
theorem isWeakBaseChangeOf_zero :
    IsWeakBaseChangeOf.{uF, uE, uV, uW} (0 : IsobaricData E) (0 : IsobaricData F) := by
  refine ⟨rfl, emptySpectrum, emptySpectrum, hasSpectralSystem_zero, hasSpectralSystem_zero, ?_⟩
  filter_upwards [eventually_ramificationIdx_eq_one F E] with v hv
  refine ⟨by simp [emptySpectrum], fun _ => by simp [emptySpectrum], fun w => hv w.1 w.2, ?_⟩
  intro w
  exact (Sym.eq_nil_of_card_zero _).symm

/-- Weak base change is closed under addition of isobaric data. -/
theorem IsWeakBaseChangeOf.add {DF DF' : IsobaricData F} {DE DE' : IsobaricData E}
    (h₁ : IsWeakBaseChangeOf.{uF, uE, uV, uW} DE DF)
    (h₂ : IsWeakBaseChangeOf.{uF, uE, uV, uW} DE' DF') :
    IsWeakBaseChangeOf.{uF, uE, uV, uW} (DE + DE') (DF + DF') := by
  obtain ⟨hn, s, t, hs, ht, hst⟩ := h₁
  obtain ⟨hm, s', t', hs', ht', hst'⟩ := h₂
  let hf := (rank_add DF DF').symm
  let he := (rank_add DE DE').symm
  refine ⟨he.symm.trans ((congrArg₂ Nat.add hn hm).trans hf),
    hf ▸ addSpectrum s s', he ▸ addSpectrum t t',
    hasSpectralSystem_add hs hs', hasSpectralSystem_add ht ht', ?_⟩
  exact arithmeticWeakBaseChange_add hf he hn hm hst hst'

/-- Unitary weak base changes for the singleton data of unitary cuspidal classes
give a unitary weak base change for every unitary isobaric datum. -/
theorem exists_unitary_weakBaseChange_of_singletons :
    UnitaryWeakBaseChangeSumStatement.{uF, uE, uV, uW} F E := by
  intro lift D hD
  induction D using Multiset.induction_on with
  | empty => exact ⟨0, isUnitary_zero, isWeakBaseChangeOf_zero⟩
  | cons c D ih =>
      change IsUnitary (c ::ₘ D) at hD
      rw [← Multiset.singleton_add c D] at hD ⊢
      have hu : (ofCuspidal c).IsUnitary ∧ IsUnitary D := isUnitary_add.mp hD
      obtain ⟨A, hA, hbcA⟩ := lift c hu.1
      obtain ⟨B, hB, hbcB⟩ := ih hu.2
      exact ⟨A + B, isUnitary_add.mpr ⟨hA, hB⟩, hbcA.add hbcB⟩

end Transfer

end Langlands.Automorphic.IsobaricData
