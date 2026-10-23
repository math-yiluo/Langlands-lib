import Langlands.Automorphic.TensorPresentation

/-! # Local components attached to nonzero tensor presentations -/

noncomputable section
open scoped Classical TensorProduct
universe uF uV

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)
variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

local instance presentedComponentRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance presentedComponentContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance presentedComponentSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance presentedComponentFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _

/-- Ordinary nonzeroness of the actual invariant subspace. -/
abbrev FiniteRealization.IsNonzero (S : FiniteRealization F n) : Prop := S ≠ ⊥

variable {F n}
variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v}
variable {S : FiniteRealization F n}

namespace FiniteTensorPresentation

variable (P : FiniteTensorPresentation F n ρ E e he S)

include P in
/-- A nonzero presented space forces its entire separated tensor space nonzero. -/
theorem exists_nonzero_localTensor (hS : S.IsNonzero F n) (v : FinitePlace F) :
    ∃ z : V v ⊗[ℂ] LocalTensorTail (K := ℂ) F E v e, z ≠ 0 := by
  by_contra! hz
  apply hS
  apply le_antisymm ?_ bot_le
  intro f hf
  obtain ⟨z, hzf⟩ := (P.localEquiv v).surjective (⟨f, hf⟩ : S.Space)
  have hf0 : (⟨f, hf⟩ : S.Space) = 0 := by
    rw [← hzf, hz z]
    exact (P.localEquiv v).toLinearEquiv.map_zero
  exact congrArg S.inclusion hf0

include P in
/-- Every specified local factor has a nonzero vector, including exceptional places. -/
theorem exists_nonzero_localFactor (hS : S.IsNonzero F n) (v : FinitePlace F) :
    ∃ x : V v, x ≠ 0 := by
  by_contra! hx
  obtain ⟨z, hz⟩ := P.exists_nonzero_localTensor hS v
  apply hz
  clear hz
  induction z using TensorProduct.inductionOn with
  | tmul x y => rw [hx x, TensorProduct.zero_tmul]
  | add x y hx hy => rw [hx, hy, add_zero]

include P in
/-- Nonzero complementary vectors are derived from the global presentation. -/
theorem exists_nonzero_tail (hS : S.IsNonzero F n) (v : FinitePlace F) :
    ∃ y, FiniteTensorRealization.TailNonzero F E e v y := by
  by_contra! hy
  obtain ⟨z, hz⟩ := P.exists_nonzero_localTensor hS v
  apply hz
  clear hz
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
      have hy0 : y = 0 := by
        simpa only [FiniteTensorRealization.TailNonzero, not_not] using hy y
      rw [hy0, TensorProduct.tmul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

include P in
/-- Smoothness of the factor follows from its faithful occurrence in actual forms. -/
theorem localFactor_isSmooth (hS : S.IsNonzero F n) (v : FinitePlace F) :
    Langlands.IsSmooth (ρ v) := by
  obtain ⟨y, hy⟩ := P.exists_nonzero_tail hS v
  exact FiniteTensorRealization.localFactor_isSmooth F n ρ E e he
    P.reference_nonzero P.toMap P.toMap_injective v y hy

/-- The chosen complementary vector is auxiliary; its slice class is independent
of this choice. -/
def chosenTail (hS : S.IsNonzero F n) (v : FinitePlace F) :
    LocalTensorTail (K := ℂ) F E v e :=
  Classical.choose (P.exists_nonzero_tail hS v)

theorem chosenTail_nonzero (hS : S.IsNonzero F n) (v : FinitePlace F) :
    FiniteTensorRealization.TailNonzero F E e v (P.chosenTail hS v) :=
  Classical.choose_spec (P.exists_nonzero_tail hS v)

/-- An actual embedded local copy of the factor of this presentation. -/
def localComponent (hS : S.IsNonzero F n) (v : FinitePlace F) :
    LocalRealization F n v :=
  P.slice v (P.chosenTail hS v)

theorem localComponent_le (hS : S.IsNonzero F n) (v : FinitePlace F) :
    P.localComponent hS v ≤ S.toLocal F n v :=
  P.slice_le v (P.chosenTail hS v)

/-- A genuine equivariant linear equivalence with the specified local factor. -/
def localComponentEquiv (hS : S.IsNonzero F n) (v : FinitePlace F) :
    (P.localComponent hS v).Equivalence F n (ρ v) :=
  P.sliceEquiv v (P.chosenTail hS v) (P.chosenTail_nonzero hS v)

theorem localComponent_ne_bot (hS : S.IsNonzero F n) (v : FinitePlace F) :
    P.localComponent hS v ≠ ⊥ := by
  obtain ⟨x, hx⟩ := P.exists_nonzero_localFactor hS v
  let q := P.localComponentEquiv hS v
  intro hbot
  have hm : (q x : AutomorphicForms F n) ∈ (⊥ : LocalRealization F n v) :=
    hbot.le (q x).property
  have hq : q x = 0 := Subtype.ext hm
  exact hx (q.injective (hq.trans q.toLinearEquiv.map_zero.symm))

/-- The smooth local class is represented in the universe of actual forms. -/
def localComponentClass (hS : S.IsNonzero F n) (v : FinitePlace F) :
    Langlands.SmoothRep.IsoClass.{0, uF, uF} ℂ (FiniteLocalGL F n v) :=
  (P.localComponent hS v).isoClass

/-- Every nonzero complementary vector gives the same class. -/
theorem localComponentClass_eq_slice (hS : S.IsNonzero F n) (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y) :
    P.localComponentClass hS v = (P.slice v y).isoClass :=
  P.slice_isoClass_eq P v (P.chosenTail hS v) y (P.chosenTail_nonzero hS v) hy

/-- Presentations of the same tensor data give the same factor class, even in
different nonzero embedded realizations. -/
theorem localComponentClass_eq {S' : FiniteRealization F n}
    (Q : FiniteTensorPresentation F n ρ E e he S')
    (hS : S.IsNonzero F n) (hS' : S'.IsNonzero F n) (v : FinitePlace F) :
    P.localComponentClass hS v = Q.localComponentClass hS' v :=
  P.slice_isoClass_eq Q v (P.chosenTail hS v) (Q.chosenTail hS' v)
    (P.chosenTail_nonzero hS v) (Q.chosenTail_nonzero hS' v)

/-- The embedded local copy inherits the global character condition on forms. -/
theorem localComponent_hasCentralCharacter (hS : S.IsNonzero F n)
    (v : FinitePlace F)
    (χ : NumberField.IdeleClassGroup (NumberField.RingOfIntegers F) F →ₜ* ℂˣ)
    (hχ : S.HasCentralCharacter χ) :
    (P.localComponent hS v).HasCentralCharacter χ :=
  fun _ hf => hχ (P.localComponent_le hS v hf)

/-- Cuspidality is inherited as an embedded constant-term condition. -/
theorem localComponent_isCuspidal [CompactSpace (AdeleQuotient F)]
    (hS : S.IsNonzero F n) (v : FinitePlace F) (hC : S.IsCuspidal) :
    (P.localComponent hS v).IsCuspidal :=
  fun _ hf => hC (P.localComponent_le hS v hf)

/-- Outside the finite exceptional set, the embedded component has a nonzero
vector fixed by the actual local integral subgroup. -/
theorem localComponent_exists_integral_fixed
    (hS : S.IsNonzero F n) (v : FinitePlace F) (hv : v ∉ E) :
    ∃ f : (P.localComponent hS v).Space,
      f ≠ 0 ∧ ∀ g ∈ localIntegral F n v,
        (P.localComponent hS v).representation g f = f :=
  FiniteTensorRealization.slice_exists_integral_fixed F n ρ E e he
    P.reference_nonzero P.toMap P.toMap_injective v hv
    (P.chosenTail hS v) (P.chosenTail_nonzero hS v)

end FiniteTensorPresentation
end Langlands.Automorphic
