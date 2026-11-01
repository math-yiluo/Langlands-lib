import Langlands.Automorphic.OperatorSubquotient
import Langlands.Global.FiniteAdelicGL.LocalTensorSeparation

/-! # Tensor presentations and actual local slices of automorphic quotients -/

noncomputable section
open scoped Classical TensorProduct
universe uF uV
set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)

local instance quotientTensorRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance quotientTensorContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance quotientTensorSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance quotientTensorFormGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance quotientTensorStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance quotientTensorRealizationGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance quotientTensorQuotientGroup (Q : OperatorSubquotient F n) :
    AddCommGroup Q.Space := Submodule.Quotient.addCommGroup _
local instance quotientTensorLocalSubspaceGroup (Q : OperatorSubquotient F n)
    (v : FinitePlace F) (L : Subrepresentation (Q.localRepresentation v)) :
    AddCommGroup L := Submodule.addCommGroup _

variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
variable (ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v))
variable (E : Finset (FinitePlace F)) (e : ∀ v, V v)
variable (he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v)

/-- Supplied genuine tensor equivalence onto an actual automorphic quotient.
Existence of such an equivalence is a separate obligation. -/
structure OperatorQuotientTensorPresentation (Q : OperatorSubquotient F n) where
  reference_nonzero : ∀ v ∉ E, e v ≠ 0
  equiv : (tensorRepresentation F n ρ E e he).Equiv Q.finiteRepresentation

namespace OperatorQuotientTensorPresentation

variable {F n ρ E e he} {Q : OperatorSubquotient F n}
variable (P : OperatorQuotientTensorPresentation F n ρ E e he Q)

/-- Restrict along the actual completed-local insertion, retaining the carrier. -/
def restrictedEquiv (v : FinitePlace F) :
    (tensorLocalRepresentation F n ρ E e he v).Equiv (Q.localRepresentation v) :=
  Representation.Equiv.mk P.equiv.toLinearEquiv
    (fun g => P.equiv.isIntertwining' (localInclusion F n v g))

/-- Expose one factor while retaining the entire complementary tensor space. -/
def localEquiv (v : FinitePlace F) :
    (separatedLocalRepresentation F n ρ E v e).Equiv (Q.localRepresentation v) :=
  (localTensorSeparation F n ρ E e he P.reference_nonzero v).symm.trans
    (P.restrictedEquiv v)

@[simp] theorem localEquiv_apply (v : FinitePlace F)
    (z : V v ⊗[ℂ] LocalTensorTail (K := ℂ) F E v e) :
    P.localEquiv v z =
      P.equiv ((localTensorSeparation F n ρ E e he P.reference_nonzero v).symm z) := rfl

/-- Fixing a complementary vector gives an actual map into the quotient carrier. -/
def localSlice (v : FinitePlace F) (y : LocalTensorTail (K := ℂ) F E v e) :
    (ρ v).IntertwiningMap (Q.localRepresentation v) :=
  (P.localEquiv v).toIntertwiningMap.comp
    { toLinearMap := (TensorProduct.mk ℂ (V v) (LocalTensorTail (K := ℂ) F E v e)).flip y
      isIntertwining' _ := by ext; rfl }

@[simp] theorem localSlice_apply (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) (x : V v) :
    P.localSlice v y x = P.localEquiv v (x ⊗ₜ[ℂ] y) := rfl

/-- The slice is the genuine invariant range inside the actual quotient. -/
def slice (v : FinitePlace F) (y : LocalTensorTail (K := ℂ) F E v e) :
    Subrepresentation (Q.localRepresentation v) :=
  (P.localSlice v y).range

theorem localSlice_injective (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) (hy : y ≠ 0) :
    Function.Injective (P.localSlice v y) := by
  intro x x' h
  have hz : x ⊗ₜ[ℂ] y = x' ⊗ₜ[ℂ] y := (P.localEquiv v).injective h
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one ℂ hy
  have hc := congrArg (fun z => TensorProduct.rid ℂ (V v)
    (TensorProduct.map (LinearMap.id : V v →ₗ[ℂ] V v) φ z)) hz
  simpa only [TensorProduct.map_tmul, LinearMap.id_apply,
    TensorProduct.rid_tmul, hφ, one_smul] using hc

/-- A nonzero tail identifies the specified factor with its actual invariant range. -/
def sliceEquiv (v : FinitePlace F) (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : y ≠ 0) : (ρ v).Equiv (P.slice v y).toRepresentation :=
  Representation.Equiv.mk
    (LinearEquiv.ofInjective (P.localSlice v y).toLinearMap (P.localSlice_injective v y hy))
    (by
      intro g
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact Representation.IntertwiningMap.isIntertwining _ _ (P.localSlice v y) g x)

@[simp] theorem coe_sliceEquiv (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) (hy : y ≠ 0) (x : V v) :
    (P.sliceEquiv v y hy x : Q.Space) = P.localSlice v y x := rfl

/-- The family of all actual slices generates the whole local restriction. -/
theorem top_le_iff_slices_le (v : FinitePlace F)
    (L : Subrepresentation (Q.localRepresentation v)) :
    ⊤ ≤ L ↔ ∀ y, P.slice v y ≤ L := by
  constructor
  · intro h y
    exact le_top.trans h
  · intro h f _
    obtain ⟨z, hz⟩ := (P.localEquiv v).surjective f
    have hm : P.localEquiv v z ∈ L := by
      clear hz
      induction z using TensorProduct.inductionOn with
      | tmul x y => exact h y ⟨x, rfl⟩
      | add x y hx hy =>
          change P.localEquiv v (x + y) ∈ L.toSubmodule
          simpa only [map_add] using L.toSubmodule.add_mem hx hy
    change (P.localEquiv v) z = f at hz
    exact hz ▸ hm

/-- Smoothness is inherited from the actual locally restricted quotient. -/
theorem slice_isSmooth (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) :
    Langlands.IsSmooth (P.slice v y).toRepresentation :=
  Langlands.isSmooth_of_injective
    { toLinearMap := (P.slice v y).toSubmodule.subtype
      isIntertwining' _ := by ext; rfl }
    Subtype.val_injective (Q.localRepresentation_isSmooth v)

def sliceSmoothRepresentation (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) :
    Langlands.SmoothRep.{0, uF, uF} ℂ (FiniteLocalGL F n v) :=
  Langlands.SmoothRep.of (P.slice v y).toRepresentation (P.slice_isSmooth v y)

/-- The representative carrier is a subspace of the actual quotient, in universe uF. -/
def sliceClass (v : FinitePlace F) (y : LocalTensorTail (K := ℂ) F E v e) :
    Langlands.SmoothRep.IsoClass.{0, uF, uF} ℂ (FiniteLocalGL F n v) :=
  Langlands.SmoothRep.isoClass (P.sliceSmoothRepresentation v y)

/-- Nonzero tails in presentations of the same tensor model have equal local classes. -/
theorem sliceClass_eq {Q' : OperatorSubquotient F n}
    (P' : OperatorQuotientTensorPresentation F n ρ E e he Q') (v : FinitePlace F)
    (y y' : LocalTensorTail (K := ℂ) F E v e) (hy : y ≠ 0) (hy' : y' ≠ 0) :
    P.sliceClass v y = P'.sliceClass v y' :=
  (Langlands.SmoothRep.isoClass_eq_iff _ _).mpr
    ⟨Langlands.SmoothRep.mkIso ((P.sliceEquiv v y hy).symm.trans
      (P'.sliceEquiv v y' hy'))⟩

/-- Outside the exceptional set, each nonzero-tail slice has an integral-fixed vector. -/
theorem slice_exists_integral_fixed (v : FinitePlace F) (hv : v ∉ E)
    (y : LocalTensorTail (K := ℂ) F E v e) (hy : y ≠ 0) :
    ∃ f : P.slice v y, f ≠ 0 ∧ ∀ g ∈ localIntegral F n v,
      (P.slice v y).toRepresentation g f = f := by
  let q := P.sliceEquiv v y hy
  refine ⟨q (e v), ?_, ?_⟩
  · intro h
    exact P.reference_nonzero v hv (q.injective (h.trans q.toLinearEquiv.map_zero.symm))
  · intro g hg
    have h := LinearMap.congr_fun (q.isIntertwining' g) (e v)
    change q (ρ v g (e v)) = _ at h
    exact h.symm.trans (congrArg (fun x : V v => q x) (he v hv g hg))

section Nonzero

variable [Nontrivial Q.Space]

include P in
/-- Nontriviality of the quotient forces the whole separated tensor to be nonzero. -/
theorem exists_nonzero_localTensor (v : FinitePlace F) :
    ∃ z : V v ⊗[ℂ] LocalTensorTail (K := ℂ) F E v e, z ≠ 0 := by
  obtain ⟨f, hf⟩ := exists_ne (0 : Q.Space)
  obtain ⟨z, hz⟩ := (P.localEquiv v).surjective f
  refine ⟨z, ?_⟩
  intro h
  apply hf
  rw [← hz, h]
  exact (P.localEquiv v).toLinearEquiv.map_zero

include P in
/-- This applies to every factor, including those at exceptional places. -/
theorem exists_nonzero_localFactor (v : FinitePlace F) : ∃ x : V v, x ≠ 0 := by
  by_contra! hx
  obtain ⟨z, hz⟩ := P.exists_nonzero_localTensor v
  apply hz
  clear hz
  induction z using TensorProduct.inductionOn with
  | tmul x y => rw [hx x, TensorProduct.zero_tmul]
  | add x y hx hy => rw [hx, hy, add_zero]

include P in
/-- Nonzero complementary vectors follow from the supplied presentation. -/
theorem exists_nonzero_tail (v : FinitePlace F) :
    ∃ y : LocalTensorTail (K := ℂ) F E v e, y ≠ 0 := by
  by_contra! hy
  obtain ⟨z, hz⟩ := P.exists_nonzero_localTensor v
  apply hz
  clear hz
  induction z using TensorProduct.inductionOn with
  | tmul x y => rw [hy y, TensorProduct.tmul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

include P in
/-- Faithful occurrence in the smooth quotient proves smoothness of the factor. -/
theorem localFactor_isSmooth (v : FinitePlace F) : Langlands.IsSmooth (ρ v) := by
  obtain ⟨y, hy⟩ := P.exists_nonzero_tail v
  exact Langlands.isSmooth_of_injective (P.localSlice v y) (P.localSlice_injective v y hy)
    (Q.localRepresentation_isSmooth v)

def chosenTail (v : FinitePlace F) : LocalTensorTail (K := ℂ) F E v e :=
  Classical.choose (P.exists_nonzero_tail v)

theorem chosenTail_nonzero (v : FinitePlace F) : P.chosenTail v ≠ 0 :=
  Classical.choose_spec (P.exists_nonzero_tail v)

/-- An actual local copy inside the quotient carrier. -/
def localComponent (v : FinitePlace F) : Subrepresentation (Q.localRepresentation v) :=
  P.slice v (P.chosenTail v)

def localComponentEquiv (v : FinitePlace F) :
    (ρ v).Equiv (P.localComponent v).toRepresentation :=
  P.sliceEquiv v (P.chosenTail v) (P.chosenTail_nonzero v)

theorem localComponent_ne_bot (v : FinitePlace F) : P.localComponent v ≠ ⊥ := by
  have hn : ∃ x : V v, x ≠ 0 := P.exists_nonzero_localFactor v
  obtain ⟨x, hx⟩ := hn
  let q := P.localComponentEquiv v
  intro hbot
  have hm : (q x : Q.Space) ∈ (⊥ : Subrepresentation (Q.localRepresentation v)) :=
    hbot.le (q x).property
  have hq : q x = 0 := Subtype.ext hm
  exact hx (q.injective (hq.trans q.toLinearEquiv.map_zero.symm))

def localComponentClass (v : FinitePlace F) :
    Langlands.SmoothRep.IsoClass.{0, uF, uF} ℂ (FiniteLocalGL F n v) :=
  P.sliceClass v (P.chosenTail v)

theorem localComponentClass_eq_slice (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) (hy : y ≠ 0) :
    P.localComponentClass v = P.sliceClass v y :=
  P.sliceClass_eq P v (P.chosenTail v) y (P.chosenTail_nonzero v) hy

theorem localComponentClass_eq {Q' : OperatorSubquotient F n} [Nontrivial Q'.Space]
    (P' : OperatorQuotientTensorPresentation F n ρ E e he Q') (v : FinitePlace F) :
    P.localComponentClass v = P'.localComponentClass v :=
  P.sliceClass_eq P' v (P.chosenTail v) (P'.chosenTail v)
    (P.chosenTail_nonzero v) (P'.chosenTail_nonzero v)

theorem localComponent_exists_integral_fixed (v : FinitePlace F) (hv : v ∉ E) :
    ∃ f : P.localComponent v, f ≠ 0 ∧ ∀ g ∈ localIntegral F n v,
      (P.localComponent v).toRepresentation g f = f :=
  P.slice_exists_integral_fixed v hv (P.chosenTail v) (P.chosenTail_nonzero v)

end Nonzero
end OperatorQuotientTensorPresentation
end Langlands.Automorphic
