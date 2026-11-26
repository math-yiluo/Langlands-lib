import Langlands.Algebra.NumberFieldBrauerProfileRealization
import Langlands.Shimura.Unitary.SplitCompletionChart
import Langlands.Shimura.Unitary.UnitaryLocalProfileRealizationStatement

/-! # The central simple algebra of a signed split-place profile -/

noncomputable section

universe u v

namespace Langlands.Shimura.FiniteUnitary

open NumberField _root_.Algebra Langlands.Global.AdelicFunctoriality
open Langlands.ClassFieldTheory.Local
open scoped NumberField

local notation "FinitePlace" => Langlands.Global.FinitePlace
local notation "FiniteCompletion" => Langlands.Global.FiniteCompletion

variable {E : Type u} {K : Type v}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K]
  {s : Finset (FinitePlace E)}

private def orientedUpperPlaces
    (h : ∀ p : s, SplitPlaceIdentification E K p.val)
    (positive : ∀ p : s, FinitePlacesAbove K p.val) :
    (s × Fin 2) ↪ FinitePlace K where
  toFun i := (((h i.1).orientedPlacesEquiv (positive i.1)).symm i.2).val
  inj' := by
    rintro ⟨p, i⟩ ⟨q, j⟩ he
    change
      (((h p).orientedPlacesEquiv (positive p)).symm i).val =
        (((h q).orientedPlacesEquiv (positive q)).symm j).val at he
    have hpq : p = q := Subtype.ext
      ((finitePlacesAbove_under p.val _).symm.trans
        ((congrArg (fun w : FinitePlace K => w.under (𝓞 E)) he).trans
          (finitePlacesAbove_under q.val _)))
    subst q
    exact Prod.ext rfl (((h p).orientedPlacesEquiv (positive p)).symm.injective
      (Subtype.ext he))

private def orientedInvariant {n : ℕ} (hn : 0 < n) (a : s → ZMod n)
    (i : s × Fin 2) : denominatorSubgroup n :=
  denominatorEquiv n hn (if i.2 = 0 then a i.1 else -a i.1)

/-- The signed, `n`-torsion invariant profile on the actual finite places of
the CM field, extended by zero outside the pairs of places. -/
def signedSplitBrauerProfile {n : ℕ} (hn : 0 < n)
    (hs : ∀ p : s, IsSplitPlace E K p.val)
    (positive : ∀ p : s, FinitePlacesAbove K p.val) (a : s → ZMod n) :
    FinitePlace K → denominatorSubgroup n :=
  Function.extend (orientedUpperPlaces (fun p => (hs p).some) positive)
    (orientedInvariant hn a) (fun _ => 0)

/-- The prescribed split-place values already determine a degree-`n` CSA
with zero invariant at every other finite place of the CM field. -/
theorem exists_csa_for_splitProfile {n : ℕ} (hn : 0 < n)
    (hs : ∀ p : s, IsSplitPlace E K p.val)
    (positive : ∀ p : s, FinitePlacesAbove K p.val) (a : s → ZMod n) :
    ∃ A : CSA.{v, v} K, Module.finrank K A = n * n ∧
      (∀ (p : s) (q : FinitePlacesAbove K p.val),
        HasCompletedBrauerInvariant K A q.val
          (denominatorEquiv n hn (by
            classical
            exact if q = positive p then a p else -a p))) ∧
      ∀ (p : FinitePlace E), p ∉ s → ∀ q : FinitePlacesAbove K p,
        HasCompletedBrauerInvariant K A q.val 0 := by
  classical
  let h (p : s) := (hs p).some
  let e := orientedUpperPlaces h positive
  let S : Finset (FinitePlace K) := Finset.univ.map e
  let f (q : FinitePlace K) : RationalModIntegers := signedSplitBrauerProfile hn hs positive a q
  have hf (i : s × Fin 2) : f (e i) = orientedInvariant hn a i :=
    congrArg Subtype.val (e.injective.extend_apply (orientedInvariant hn a) (fun _ => 0) i)
  have hsupport (q : FinitePlace K) (hq : q ∉ S) : f q = 0 := by
    change ((Function.extend e (orientedInvariant hn a) (fun _ => 0) q :
      denominatorSubgroup n) : RationalModIntegers) = 0
    rw [Function.extend_apply' _ _ _ (by
      rintro ⟨i, rfl⟩
      exact hq (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩))]
    rfl
  have hann (q : FinitePlace K) (hq : q ∈ S) : n • f q = 0 := by
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hq
    rw [hf]
    exact (orientedInvariant hn a i).property
  have hsum : ∑ q ∈ S, f q = 0 := by
    simp only [S, Finset.sum_map, hf]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [Fin.sum_univ_two]
    simp [orientedInvariant]
  obtain ⟨A, hdim, hA⟩ :=
    Brauer.numberFieldBrauerProfileRealization K S f hsupport n hn hann hsum
  have hcompleted (q : FinitePlace K) : HasCompletedBrauerInvariant K A q (f q) :=
    ⟨Brauer.baseChange (FiniteCompletion K q) A, ⟨AlgEquiv.refl⟩, hA q⟩
  refine ⟨A, hdim, ?_, ?_⟩
  · intro p q
    let b := (h p).orientedPlacesEquiv (positive p)
    let i : s × Fin 2 := (p, b q)
    have he : e i = q.val := congrArg Subtype.val (b.symm_apply_apply q)
    have hzero : b q = 0 ↔ q = positive p :=
      ⟨fun hq => b.injective (hq.trans ((h p).orientedPlacesEquiv_apply_self (positive p)).symm),
        fun hq => hq ▸ (h p).orientedPlacesEquiv_apply_self (positive p)⟩
    have hval : HasCompletedBrauerInvariant K A (e i) (orientedInvariant hn a i) :=
      hf i ▸ hcompleted (e i)
    simpa only [he, orientedInvariant, i, hzero] using hval
  · intro p hp q
    have hq : q.val ∉ S := by
      rintro hm
      obtain ⟨i, -, hi⟩ := Finset.mem_map.mp hm
      have hi' : (e i).under (𝓞 E) = i.1.val := finitePlacesAbove_under i.1.val _
      rw [hi, finitePlacesAbove_under p q] at hi'
      exact hp (hi'.symm ▸ i.1.property)
    exact hsupport q.val hq ▸ hcompleted q.val

end Langlands.Shimura.FiniteUnitary
