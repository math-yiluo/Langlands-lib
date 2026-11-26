import Langlands.Global.RankinSelberg.RealGapColumnCoordinates
import Langlands.Group.GL.LeviCentralQuotientMeasure

/-! # Real triangular column Fourier exchange in the larger-gap unfolding -/

noncomputable section

open MeasureTheory
open scoped SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapColumnFourier

open ArchimedeanLocal (realFourierTransform realNormalizedAbs realSelfDualMeasure)
open Langlands.LocalFactor.Archimedean (realScaledCharacter)
open MeasureTheory.Measure (measurePreserving_inv)
open RealJacquetUnipotentMeasure (entryHaar entryHaar_isHaar measurePreserving_transposeReflection
  transposeReflection transposeReflection_eq)
open Langlands.GeneralLinear (upperEntryCoordinates upperEntryCoordinates_apply)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open Langlands.RankinSelberg (rectangularMeasure)

variable (k q : ℕ)

local notation "I" => Fin (k + q + 1)
local notation "J" => Fin q
local notation "G" => Langlands.GeneralLinear (k + q + 1) ℝ
local notation "N" => Langlands.GeneralLinear.upperUnipotent (q + 1) ℝ
local notation "Rect" => Matrix (Fin k) J ℝ
local notation "P" => fun j => {i : I // beforePivot k q j i}
local notation "S" => fun j => {i : I // ¬ beforePivot k q j i}
local notation "Upper" => {ij : Fin (q + 1) × Fin (q + 1) // Prod.fst ij < Prod.snd ij}

local instance triangularTailMeasurable : MeasurableSpace N := borel _
local instance triangularTailBorel : BorelSpace N := ⟨rfl⟩
local instance triangularTailMeasurableInv : MeasurableInv N := ⟨continuous_inv.measurable⟩

/-- The later columns of the right upper block with identity leading block. -/
def directColumn (X : Rect) (Z : N) (j : J) (i : I) : ℝ :=
  if h : i.val < k then X ⟨i.val, h⟩ j
  else Z.val.val ⟨i.val - k, by have := i.isLt; omega⟩ j.succ

/-- The columns in the transposed tail at the preceding pivots. -/
def transposeColumn (Z : N) (j : J) (i : I) : ℝ :=
  if i.val < k then 0
  else Z.val.val j.castSucc ⟨i.val - k, by have := i.isLt; omega⟩

private def previousPivot (j : J) : I := ⟨k + j.val, by have := j.isLt; omega⟩
private def pivot (j : J) : I := ⟨k + j.val + 1, by have := j.isLt; omega⟩

private def α (j : J) : P j → ℝ :=
  haveI := Classical.decEq (P j)
  Pi.single (M := fun _ : P j => ℝ) ⟨previousPivot k q j, Nat.lt_succ_self _⟩ 1

private def β (j : J) : S j → ℝ :=
  haveI := Classical.decEq (S j)
  Pi.single (M := fun _ : S j => ℝ) ⟨pivot k q j, Nat.lt_irrefl _⟩ 1

private theorem constPiCongrLeft_apply {A B : Type} (e : A ≃ B) (x : A → ℝ) (i : B) :
    MeasurableEquiv.piCongrLeft (fun _ => ℝ) e x i = x (e.symm i) := by
  simpa only [e.apply_symm_apply] using
    (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℝ) e x (e.symm i))

private theorem prefixColumns_apply (X : Rect) (Z : N) (j : J) (i : P j) :
    prefixColumns k q (X, Z) j i = directColumn k q X Z j i.val := by
  let f : (Fin k × J) ⊕ Upper → ℝ :=
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : (Fin k × J) ⊕ Upper => ℝ)).symm
      (Function.uncurry X, upperEntryCoordinates (q + 1) Z)
  change MeasurableEquiv.piCongrLeft (fun _ => ℝ) (prefixIndex k q).symm f ⟨j, i⟩ = _
  rw [constPiCongrLeft_apply]
  change f (prefixIndex k q ⟨j, i⟩) = _
  have hi : i.val.val < k + j.val + 1 := i.2
  by_cases h : i.val.val < k
  · rw [show prefixIndex k q ⟨j, i⟩ = Sum.inl (⟨i.val.val, h⟩, j) from dite_eq_left h]
    simp only [directColumn, dite_eq_left h]
    rfl
  · rw [show prefixIndex k q ⟨j, i⟩ = Sum.inr
      ⟨(⟨i.val.val - k, by have := i.val.isLt; omega⟩, j.succ),
        show i.val.val - k < j.val + 1 by omega⟩ from dite_eq_right h]
    simp only [directColumn, dite_eq_right h]
    exact upperEntryCoordinates_apply _ _

private theorem suffixColumns_apply (Z : N) (j : J) (i : S j) :
    suffixColumns k q Z j i = transposeColumn k q Z j i.val := by
  change MeasurableEquiv.piCongrLeft (fun _ => ℝ) (suffixIndex k q).symm
    (upperEntryCoordinates (q + 1) Z) ⟨j, i⟩ = _
  rw [constPiCongrLeft_apply]
  have hi : ¬ i.val.val < k + j.val + 1 := i.2
  have hk : ¬ i.val.val < k := by omega
  simp only [transposeColumn, ite_eq_right hk]
  exact upperEntryCoordinates_apply _ _

private theorem directColumn_suffix (X : Rect) (Z : N) (j : J) (i : S j) :
    directColumn k q X Z j i.val = β k q j i := by
  classical
  have hi : ¬ i.val.val < k + j.val + 1 := i.2
  have hk : ¬ i.val.val < k := by omega
  let p : S j := ⟨pivot k q j, Nat.lt_irrefl _⟩
  let := Classical.decEq (S j)
  change _ = Pi.single (M := fun _ : S j => ℝ) p (1 : ℝ) i
  rw [directColumn, dite_eq_right hk]
  by_cases he : i = p
  · subst i
    rw [Pi.single_eq_same]
    rw [show (⟨(p.val.val - k), _⟩ : Fin (q + 1)) = j.succ from Fin.ext (by
      change k + j.val + 1 - k = j.val + 1
      omega), Langlands.GeneralLinear.UpperUnipotent.entry_diag]
  · rw [Pi.single_eq_of_ne he]
    apply Langlands.GeneralLinear.UpperUnipotent.entry_eq_zero
    change j.val + 1 < i.val.val - k
    have hne : i.val.val ≠ k + j.val + 1 := fun h => he (Subtype.ext (Fin.ext h))
    omega

private theorem transposeColumn_prefix (Z : N) (j : J) (i : P j) :
    transposeColumn k q Z j i.val = α k q j i := by
  classical
  have hi : i.val.val < k + j.val + 1 := i.2
  let p : P j := ⟨previousPivot k q j, Nat.lt_succ_self _⟩
  let := Classical.decEq (P j)
  change _ = Pi.single (M := fun _ : P j => ℝ) p (1 : ℝ) i
  by_cases he : i = p
  · subst i
    have hp : ¬ p.val.val < k := by change ¬ k + j.val < k; omega
    rw [Pi.single_eq_same, transposeColumn, ite_eq_right hp]
    rw [show (⟨p.val.val - k, _⟩ : Fin (q + 1)) = j.castSucc from Fin.ext (by
      change k + j.val - k = j.val
      omega), Langlands.GeneralLinear.UpperUnipotent.entry_diag]
  · rw [Pi.single_eq_of_ne he, transposeColumn]
    split_ifs with hk
    · rfl
    · apply Langlands.GeneralLinear.UpperUnipotent.entry_eq_zero
      change i.val.val - k < j.val
      have hne : i.val.val ≠ k + j.val := fun h => he (Subtype.ext (Fin.ext h))
      omega

private theorem merge_prefix (X : Rect) (Z : N) (j : J) :
    merge (beforePivot k q j) (prefixColumns k q (X, Z) j) (β k q j) = directColumn k q X Z j := by
  funext i
  by_cases h : beforePivot k q j i
  · rw [merge_apply_left _ _ _ ⟨i, h⟩, prefixColumns_apply]
  · rw [merge_apply_right _ _ _ ⟨i, h⟩]
    exact (directColumn_suffix k q X Z j ⟨i, h⟩).symm

private theorem merge_suffix (Z : N) (j : J) :
    merge (beforePivot k q j) (α k q j) (suffixColumns k q Z j) = transposeColumn k q Z j := by
  funext i
  by_cases h : beforePivot k q j i
  · rw [merge_apply_left _ _ _ ⟨i, h⟩]
    exact (transposeColumn_prefix k q Z j ⟨i, h⟩).symm
  · rw [merge_apply_right _ _ _ ⟨i, h⟩, suffixColumns_apply]

private theorem sum_mul_single {A : Type*} [Fintype A] [DecidableEq A] (f : A → ℝ) (i : A) :
    (∑ j, f j * Pi.single (M := fun _ : A => ℝ) i (1 : ℝ) j) = f i := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ h
    rw [Pi.single_eq_of_ne h, mul_zero]
  · simp

private theorem prefix_pairing (X : Rect) (Z : N) (j : J) :
    (∑ i, prefixColumns k q (X, Z) j i * α k q j i) = Z.val.val j.castSucc j.succ := by
  let := Classical.decEq (P j)
  let p : P j := ⟨previousPivot k q j, Nat.lt_succ_self _⟩
  have hp : ¬ p.val.val < k := by change ¬ k + j.val < k; omega
  rw [show α k q j = Pi.single (M := fun _ : P j => ℝ) p (1 : ℝ) from rfl,
    sum_mul_single, prefixColumns_apply, directColumn, dite_eq_right hp]
  exact congrArg (fun i => Z.val.val i j.succ) (Fin.ext (by change k + j.val - k = j.val; omega))

private theorem suffix_pairing (Z : N) (j : J) :
    (∑ i, suffixColumns k q Z j i * β k q j i) = Z.val.val j.castSucc j.succ := by
  let := Classical.decEq (S j)
  let p : S j := ⟨pivot k q j, Nat.lt_irrefl _⟩
  have hp : ¬ p.val.val < k := by change ¬ k + j.val + 1 < k; omega
  rw [show β k q j = Pi.single (M := fun _ : S j => ℝ) p (1 : ℝ) from rfl,
    sum_mul_single, suffixColumns_apply, transposeColumn, ite_eq_right hp]
  exact congrArg (Z.val.val j.castSucc) (Fin.ext (by change k + j.val + 1 - k = j.val + 1; omega))

private theorem prod_psi (a : ℝˣ) (Z : N) :
    (∏ j : J, psi a (Z.val.val j.castSucc j.succ)) =
      (Whittaker.standardCharacter (realScaledCharacter a) q Z : ℂ) := by
  rw [Whittaker.standardCharacter_apply]
  change (∏ j : J, (realScaledCharacter a).complex (Z.val.val j.castSucc j.succ)) =
    (realScaledCharacter a).complex (∑ j : J, Z.val.val j.castSucc j.succ)
  classical
  induction (Finset.univ : Finset J) using Finset.induction_on with
  | empty => simp
  | @insert j s hj hs => rw [Finset.prod_insert hj, Finset.sum_insert hj, AddChar.map_add_eq_mul, hs]

/-- The ordinary triangular integrand with its standard tail character. -/
def triangularOrdinary (a : ℝˣ) (g : G) (Φ : J → 𝓢(I → ℝ, ℂ)) (x : Rect × N) : ℂ :=
  (∏ j, Φ j (g.val.mulVec (directColumn k q x.1 x.2 j))) *
    (Whittaker.standardCharacter (realScaledCharacter a) q x.2 : ℂ)

/-- The Fourier-side integrand after the tail inverse change of variables. -/
def triangularFourier (a : ℝˣ) (g : G) (Φ : J → 𝓢(I → ℝ, ℂ)) (Z : N) : ℂ :=
  (∏ j, realFourierTransform a (Φ j) (g⁻¹.val.transpose.mulVec (transposeColumn k q Z⁻¹ j))) *
    (Whittaker.standardCharacter (realScaledCharacter a) q Z : ℂ)

private theorem tailCharacter_inv (a : ℝˣ) (Z : N) :
    (Whittaker.standardCharacter (realScaledCharacter (-a)) q Z⁻¹ : ℂ) =
      (Whittaker.standardCharacter (realScaledCharacter a) q Z : ℂ) := by
  simp only [Whittaker.standardCharacter_apply, Langlands.GeneralLinear.UpperUnipotent.inv_adjacent_entry,
    Finset.sum_neg_distrib]
  change psi (-a) (-_) = psi a _
  rw [psi_neg, neg_neg]

private theorem reflectedUnipotent_mul (u v : N) :
    Whittaker.reflectedUnipotent (u * v) = Whittaker.reflectedUnipotent u * Whittaker.reflectedUnipotent v := by
  apply Subtype.ext
  simp only [Whittaker.reflectedUnipotent_val, Subgroup.coe_mul, map_mul]
  let w := Langlands.GeneralLinear.weylLong (q + 1) ℝ
  let A := Langlands.GeneralLinear.inverseTranspose (q + 1) ℝ u.val
  let B := Langlands.GeneralLinear.inverseTranspose (q + 1) ℝ v.val
  change w * (A * B) * w = (w * A * w) * (w * B * w)
  calc
    _ = w * A * (w * w) * B * w := by
      rw [Langlands.GeneralLinear.weylLong_mul_self, mul_one, mul_assoc w A B]
    _ = _ := by simp only [mul_assoc]

/-- The entry-product Haar on the upper triangular group is inversion invariant. -/
theorem measurePreserving_entryHaar_inv (μ : AdditiveHaarMeasure ℝ) :
    MeasurePreserving (MeasurableEquiv.inv N) (entryHaar μ (q + 1)) (entryHaar μ (q + 1)) := by
  let ν := entryHaar μ (q + 1)
  let : ν.IsHaarMeasure := entryHaar_isHaar μ _
  let e := upperEntryCoordinates (K := ℝ) (q + 1)
  let : LocallyCompactSpace N := e.isClosedEmbedding.locallyCompactSpace
  let : SecondCountableTopology N := e.secondCountableTopology
  let : ν.Regular := inferInstance
  let f := transposeReflection (q + 1)
  have hf : MeasurePreserving f ν ν := measurePreserving_transposeReflection μ _
  let : ν.IsMulRightInvariant := ⟨fun g => by
    let h := ⇑f.symm ∘ (fun z : N => f g * f z)
    have ht : (fun z : N => z * g) = h := by
      funext z
      apply f.injective
      change f (z * g) = f (f.symm (f g * f z))
      rw [f.apply_symm_apply]
      simp only [f, transposeReflection_eq, mul_inv_rev, reflectedUnipotent_mul]
    rw [ht]
    exact ((hf.symm _).comp ((measurePreserving_mul_left ν (f g)).comp hf)).map_eq⟩
  let : ν.IsInvInvariant := Langlands.isInvInvariant_of_isMulRightInvariant ν
  exact measurePreserving_inv ν

/-- The triangular exchange of Jacquet's Lemma 10.2, with absolute integrability
on both column domains. -/
def RealGapTriangularFourierStatement : Prop :=
  ∀ (a : ℝˣ) (g : G) (Φ : J → 𝓢(I → ℝ, ℂ)),
    let μ := realSelfDualMeasure a
    let ν := entryHaar μ (q + 1)
    let ξ := (rectangularMeasure μ k q).prod ν
    Integrable (triangularOrdinary k q a g Φ) ξ ∧
    Integrable (triangularFourier k q a g Φ) ν ∧
    (∫ x, triangularOrdinary k q a g Φ x ∂ξ) =
      (((realNormalizedAbs g.val.det)⁻¹ : ℝ) : ℂ) ^ q *
        ∫ z, triangularFourier k q a g Φ z ∂ν

set_option maxHeartbeats 1000000 in
theorem realGapTriangularFourier : RealGapTriangularFourierStatement k q := by
  intro a g Φ μ ν ξ
  let F (x : ∀ j : J, P j → ℝ) :=
    ∏ j, Φ j (g.val.mulVec (merge (beforePivot k q j) (x j) (β k q j))) *
      psi a (∑ i, x j i * α k q j i)
  let H (y : ∀ j : J, S j → ℝ) :=
    ∏ j, realFourierTransform a (Φ j) (g⁻¹.val.transpose.mulVec (merge (beforePivot k q j) (α k q j) (y j))) *
      psi (-a) (∑ i, y j i * β k q j i)
  obtain ⟨hF, hH, hIntegral⟩ := realGapColumnFourierProduct (r := k + q)
    (beforePivot k q) a g Φ (α k q) (β k q)
  let e := prefixColumns k q
  let f := (MeasurableEquiv.inv N).trans (suffixColumns k q)
  have he := (realGapColumnCoordinates k q a).1
  have hf := (realGapColumnCoordinates k q a).2.comp (measurePreserving_entryHaar_inv q μ)
  have hOrd : F ∘ e = triangularOrdinary k q a g Φ := by
    funext x
    rcases x with ⟨X, Z⟩
    simp only [Function.comp_apply, e, F, merge_prefix, prefix_pairing, Finset.prod_mul_distrib,
      prod_psi, triangularOrdinary]
  have hFourier : H ∘ f = triangularFourier k q a g Φ := by
    funext Z
    simp only [Function.comp_apply, f, MeasurableEquiv.trans_apply, MeasurableEquiv.inv_apply, H,
      merge_suffix, suffix_pairing, Finset.prod_mul_distrib, prod_psi, tailCharacter_inv, triangularFourier]
  change Integrable F _ at hF
  change Integrable H _ at hH
  refine ⟨hOrd ▸ (he.integrable_comp_emb e.measurableEmbedding).mpr hF,
    hFourier ▸ (hf.integrable_comp_emb f.measurableEmbedding).mpr hH, ?_⟩
  rw [← hOrd, ← hFourier]
  change (∫ x, F (e x) ∂ξ) = _ * ∫ z, H (f z) ∂ν
  rw [he.integral_comp' F, hf.integral_comp' H]
  simpa only [Fintype.card_fin] using hIntegral

end Langlands.Global.RankinSelbergGlobal.RealGapColumnFourier
