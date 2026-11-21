import Langlands.Global.RankinSelberg.ComplexGapColumnFourier
import Langlands.Global.RankinSelberg.ComplexJacquetUnipotentMeasure

/-! # Independent column coordinates for triangular Fourier inversion -/

noncomputable section

open MeasureTheory Set

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapColumnFourier

open Langlands.GeneralLinear (upperEntryCoordinates upperEntryProductMeasure)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open Langlands.RankinSelberg (rectangularMeasure)
open ComplexGodementFourier (piMeasure measurePreserving_uncurry)
open ComplexJacquetUnipotentMeasure (entryHaar entryHaar_sigmaFinite)
open ArchimedeanLocal (complexSelfDualMeasure)

variable (k q : ℕ)

local notation "I" => Fin (k + q + 1)
local notation "J" => Fin q
local notation "Z" => Langlands.GeneralLinear.upperUnipotent (q + 1) ℂ
local notation "Rect" => Matrix (Fin k) J ℂ
local notation "Upper" => {ij : Fin (q + 1) × Fin (q + 1) // Prod.fst ij < Prod.snd ij}

/-- Coordinates before the pivot in a column after the first tail column. -/
def beforePivot (j : J) (i : I) : Prop := i.val < k + j.val + 1

instance prefix_decidable (j : J) : DecidablePred (beforePivot k q j) :=
  fun i => Nat.decLt i.val (k + j.val + 1)

local notation "P" => fun j => {i : I // beforePivot k q j i}
local notation "S" => fun j => {i : I // ¬ beforePivot k q j i}

private theorem prefix_index_eq {a b : Σ j : J, P j}
    (hj : a.1 = b.1) (hi : a.2.val.val = b.2.val.val) : a = b := by
  rcases a with ⟨j, i⟩
  rcases b with ⟨j', i'⟩
  dsimp at hj hi
  subst j'
  exact congrArg (Sigma.mk j) (Subtype.ext (Fin.ext hi))

/-- Before each pivot, entries come from the leading rectangle or from the strict
upper triangle of the tail. -/
def prefixIndex : (Σ j : J, P j) ≃ (Fin k × J) ⊕ Upper where
  toFun u :=
    if h : u.2.val.val < k then
      Sum.inl (⟨u.2.val.val, h⟩, u.1)
    else
      have hu : u.2.val.val < k + u.1.val + 1 := u.2.2
      Sum.inr ⟨(⟨u.2.val.val - k, by omega⟩, u.1.succ),
        show u.2.val.val - k < u.1.val + 1 by omega⟩
  invFun
    | Sum.inl (i, j) => ⟨j, ⟨⟨i.val, by omega⟩, show i.val < k + j.val + 1 by omega⟩⟩
    | Sum.inr ⟨(i, j), hij⟩ =>
      have hi : i.val < j.val := hij
      ⟨⟨j.val - 1, by omega⟩,
        ⟨⟨k + i.val, by omega⟩, show k + i.val < k + (j.val - 1) + 1 by omega⟩⟩
  left_inv u := by
    rcases u with ⟨j, i⟩
    dsimp only
    split_ifs with hi
    · apply prefix_index_eq <;> rfl
    · apply prefix_index_eq
      · apply Fin.ext
        change j.val + 1 - 1 = j.val
        omega
      · change k + (i.val.val - k) = i.val.val
        omega
  right_inv u := by
    rcases u with ⟨i, j⟩ | ⟨⟨i, j⟩, hij⟩
    · dsimp only
      rw [dite_eq_left i.isLt]
    · have hi : i.val < j.val := hij
      dsimp only
      rw [dite_eq_right (by omega)]
      apply congrArg Sum.inr
      apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext <;> dsimp only [Fin.val_succ] <;> omega

/-- The complementary frequencies are the strict upper entries of the transposed
tail column at the preceding pivot. -/
def suffixIndex : (Σ j : J, S j) ≃ Upper where
  toFun u :=
    have hu : ¬ u.2.val.val < k + u.1.val + 1 := u.2.2
    ⟨(u.1.castSucc, ⟨u.2.val.val - k, by omega⟩), show u.1.val < u.2.val.val - k by omega⟩
  invFun u :=
    have hu : u.val.1.val < u.val.2.val := u.2
    ⟨⟨u.val.1.val, by omega⟩, ⟨⟨k + u.val.2.val, by omega⟩,
      show ¬ k + u.val.2.val < k + u.val.1.val + 1 by omega⟩⟩
  left_inv u := by
    rcases u with ⟨j, i⟩
    have hi := i.2
    change ¬ i.val.val < k + j.val + 1 at hi
    have h : k + (i.val.val - k) = i.val.val := by omega
    change @Sigma.mk J S (⟨j.val, _⟩ : J) _ = @Sigma.mk J S j i
    congr 1
    exact Subtype.ext (Fin.ext h)
  right_inv u := by
    apply Subtype.ext
    apply Prod.ext
    · exact Fin.ext rfl
    · apply Fin.ext
      change k + u.val.2.val - k = u.val.2.val
      omega

private theorem measurePreserving_dependentUncurry
    {A : Type*} [Fintype A] {B : A → Type*} [∀ i, Fintype (B i)]
    (ν : Measure ℂ) [SigmaFinite ν] :
    MeasurePreserving (MeasurableEquiv.piCurry (fun _ (_ : B _) => ℂ)).symm
      (Measure.pi fun i : A => Measure.pi fun _ : B i => ν)
      (Measure.pi fun _ : Σ i, B i => ν) := by
  let e := (MeasurableEquiv.piCurry (fun i (_ : B i) => ℂ)).symm
  refine ⟨e.measurable, (Measure.pi_eq fun s _ => ?_).symm⟩
  rw [show (⇑e) = _ from rfl, MeasurableEquiv.map_apply]
  have hpre : e ⁻¹' univ.pi s = univ.pi fun i => univ.pi fun j => s ⟨i, j⟩ := by
    ext f
    simp [e, MeasurableEquiv.coe_piCurry_symm, Sigma.forall, Sigma.uncurry]
  rw [hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  exact (Fintype.prod_sigma (fun i : Σ i, B i => ν (s i))).symm

local instance gapTailMeasurable : MeasurableSpace Z := borel _
local instance gapTailBorel : BorelSpace Z := ⟨rfl⟩

/-- Reindex the rectangular and strictly upper entries by independent column prefixes. -/
def prefixColumns : (Rect × Z) ≃ᵐ (∀ j : J, P j → ℂ) :=
  let eRect := (MeasurableEquiv.curry (Fin k) J ℂ).symm
  let eUpper := (upperEntryCoordinates (K := ℂ) (q + 1)).toMeasurableEquiv
  let eSum := (MeasurableEquiv.sumPiEquivProdPi (fun _ : (Fin k × J) ⊕ Upper => ℂ)).symm
  let eIndex := MeasurableEquiv.piCongrLeft (fun _ => ℂ) (prefixIndex k q).symm
  ((eRect.prodCongr eUpper).trans (eSum.trans eIndex)).trans (MeasurableEquiv.piCurry fun _ _ => ℂ)

/-- Reindex strict upper entries of the tail by independent complementary column blocks. -/
def suffixColumns : Z ≃ᵐ (∀ j : J, S j → ℂ) :=
  ((upperEntryCoordinates (K := ℂ) (q + 1)).toMeasurableEquiv.trans
    (MeasurableEquiv.piCongrLeft (fun _ => ℂ) (suffixIndex k q).symm)).trans
    (MeasurableEquiv.piCurry fun _ _ => ℂ)

/-- The reindexings of the two triangular column domains preserve their coordinate Haar measures. -/
def ComplexGapColumnCoordinatesStatement : Prop :=
  ∀ a : ℂˣ,
    let μ := complexSelfDualMeasure a
    MeasurePreserving (prefixColumns k q) ((rectangularMeasure μ k q).prod (entryHaar μ (q + 1)))
      (Measure.pi fun j : J => piMeasure (P j) a) ∧
    MeasurePreserving (suffixColumns k q) (entryHaar μ (q + 1))
      (Measure.pi fun j : J => piMeasure (S j) a)

set_option maxHeartbeats 600000 in
theorem complexGapColumnCoordinates : ComplexGapColumnCoordinatesStatement k q := by
  intro a
  let μ := complexSelfDualMeasure a
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let : SigmaFinite μ.measure := inferInstance
  let : SigmaFinite (entryHaar μ (q + 1)) := entryHaar_sigmaFinite μ (q + 1)
  let e := (upperEntryCoordinates (K := ℂ) (q + 1)).toMeasurableEquiv
  have hEntry : MeasurePreserving e (entryHaar μ (q + 1)) (upperEntryProductMeasure μ (q + 1)) :=
    (show MeasurePreserving e.symm (upperEntryProductMeasure μ (q + 1)) (entryHaar μ (q + 1)) from
      ⟨e.symm.measurable, rfl⟩).symm _
  constructor
  · unfold prefixColumns
    exact (((measurePreserving_uncurry μ.measure).prod hEntry).trans
      ((measurePreserving_sumPiEquivProdPi (fun _ : (Fin k × J) ⊕ Upper => μ.measure)).symm _)).trans
      ((measurePreserving_piCongrLeft (fun _ => μ.measure) (prefixIndex k q).symm).trans
        ((measurePreserving_dependentUncurry (B := P) μ.measure).symm _))
  · unfold suffixColumns
    exact (hEntry.trans (measurePreserving_piCongrLeft (fun _ => μ.measure) (suffixIndex k q).symm)).trans
      ((measurePreserving_dependentUncurry (B := S) μ.measure).symm _)

end Langlands.Global.RankinSelbergGlobal.ComplexGapColumnFourier
