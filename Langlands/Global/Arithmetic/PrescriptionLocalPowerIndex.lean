import Langlands.Global.Arithmetic.PrescriptionFiniteQuotientStatement
import Langlands.ClassField.Global.LocalPowerIndex
import Langlands.Global.Arithmetic.SUnitIdelePowerQuotient
import Mathlib.Algebra.Group.Pi.Units

/-! # Finite power index in the whole prescription local product -/

noncomputable section

universe u v

namespace Langlands.Global

open Langlands.ClassField.Global

set_option maxHeartbeats 800000 in
/-- A finite product of abelian groups with finite power quotients has a finite
power quotient. The factor universes are independent of the indexing universe. -/
theorem finiteIndex_power_range_pi
    {ι : Type v} [Finite ι] (A : ι → Type u) [∀ i, CommGroup (A i)]
    (d : ℕ) (h : ∀ i, (powMonoidHom (α := A i) d).range.FiniteIndex) :
    (powMonoidHom (α := (i : ι) → A i) d).range.FiniteIndex := by
  let (i : ι) : (powMonoidHom (α := A i) d).range.FiniteIndex := h i
  let (i : ι) : Finite (A i ⧸ (powMonoidHom (α := A i) d).range) :=
    Subgroup.finite_quotient_of_finiteIndex
  let e : (((i : ι) → A i) ⧸ (powMonoidHom (α := (i : ι) → A i) d).range) ≃*
      ((i : ι) → A i ⧸ (powMonoidHom (α := A i) d).range) :=
    QuotientGroup.mulEquivPiModRangePowMonoidHom A d
  let : Finite (((i : ι) → A i) ⧸
      (powMonoidHom (α := (i : ι) → A i) d).range) :=
    Finite.of_injective e e.injective
  exact Subgroup.finiteIndex_of_finite_quotient

/-- Binary products also preserve finite power index. -/
theorem finiteIndex_power_range_prod
    {A : Type u} [CommGroup A] {B : Type v} [CommGroup B]
    (d : ℕ)
    [hA : (powMonoidHom (α := A) d).range.FiniteIndex]
    [hB : (powMonoidHom (α := B) d).range.FiniteIndex] :
    (powMonoidHom (α := A × B) d).range.FiniteIndex := by
  have heq : (powMonoidHom (α := A × B) d).range =
      (powMonoidHom (α := A) d).range.prod (powMonoidHom (α := B) d).range := by
    ext x
    constructor
    · rintro ⟨⟨a, b⟩, rfl⟩
      exact ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      exact ⟨(a, b), Prod.ext ha hb⟩
  rw [heq]
  refine ⟨?_⟩
  rw [Subgroup.index_prod]
  exact mul_ne_zero hA.index_ne_zero hB.index_ne_zero

/-- Every positive power subgroup in an infinite completion has finite index,
including the sign component at a real place. -/
theorem infiniteCompletion_power_finiteIndex
    {K : Type u} [Field K] (w : NumberField.InfinitePlace K)
    (d : ℕ) (hd : d ≠ 0) :
    (powMonoidHom (α := w.Completionˣ) d).range.FiniteIndex :=
  Arithmetic.SUnitIdelePowerQuotient.infinite_power_finiteIndex w d hd

/-- The units of the whole infinite adele factor have a finite positive-power
quotient. This retains every real sign coordinate. -/
theorem infiniteAdeles_power_finiteIndex
    (K : Type u) [Field K] [NumberField K] (d : ℕ) (hd : d ≠ 0) :
    (powMonoidHom (α := (InfiniteAdeles K)ˣ) d).range.FiniteIndex := by
  let e : (InfiniteAdeles K)ˣ ≃*
      ((w : NumberField.InfinitePlace K) → w.Completionˣ) := MulEquiv.piUnits
  let := finiteIndex_power_range_pi
    (fun w : NumberField.InfinitePlace K => w.Completionˣ) d
    (fun w => infiniteCompletion_power_finiteIndex w d hd)
  have h := Subgroup.FiniteIndex.map_of_surjective
    (H := (powMonoidHom (α := (w : NumberField.InfinitePlace K) → w.Completionˣ) d).range)
    (f := e.symm.toMonoidHom)
    e.symm.surjective
  rw [MulEquiv.toMonoidHom_eq_coe, e.symm.map_range_powMonoidHom] at h
  exact h

/-- The actual prescription product, with the whole infinite factor, has finite
index for every positive power subgroup. -/
theorem prescriptionLocalProduct_power_finiteIndex
    (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    (d : ℕ) (hd : d ≠ 0) :
    (powMonoidHom (α := PrescriptionLocalProduct K S) d).range.FiniteIndex := by
  let := infiniteAdeles_power_finiteIndex K d hd
  let := finiteIndex_power_range_pi
    (fun v : {v // v ∈ S} => (FiniteCompletion K v.1)ˣ) d
    (fun v => localPowers_finiteIndex v.1 d hd)
  exact finiteIndex_power_range_prod d

end Langlands.Global
