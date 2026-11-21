import Langlands.Global.AdelicBlockHalfModulusTwistDifferential
import Langlands.Global.Factors.CuspidalSupportCompactCoefficient

/-! # Normalization of compact cuspidal block evaluations -/

noncomputable section

open scoped BigOperators TensorProduct Matrix.Norms.Operator

namespace Langlands.Global.FiniteParametrizedBlockInduction

open Langlands.GeneralLinear Langlands.Automorphic Langlands.Archimedean
open AdelicBlockDeterminantCharacter

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 120000

attribute [local instance 100] LieRing.ofAssociativeRing

universe u uR uW uV uV'

section TensorOperations

variable {ι : Type*} {V : ι → Type uV} {V' : ι → Type uV'}
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, AddCommGroup (V' i)] [∀ i, Module ℂ (V' i)]

set_option maxHeartbeats 500000 in
private theorem map_equiv_intertwines (e : ∀ i, V i ≃ₗ[ℂ] V' i)
    (A : ∀ i, Module.End ℂ (V i)) (A' : ∀ i, Module.End ℂ (V' i))
    (h : ∀ i x, e i (A i x) = A' i (e i x)) (z : ⨂[ℂ] i, V i) :
    PiTensorProduct.congr e (PiTensorProduct.map A z) =
      PiTensorProduct.map A' (PiTensorProduct.congr e z) := by
  have he : (PiTensorProduct.congr e).toLinearMap.comp (PiTensorProduct.map A) =
      (PiTensorProduct.map A').comp (PiTensorProduct.congr e).toLinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    change PiTensorProduct.congr e (PiTensorProduct.map A (PiTensorProduct.tprod ℂ x)) =
      PiTensorProduct.map A' (PiTensorProduct.congr e (PiTensorProduct.tprod ℂ x))
    rw [PiTensorProduct.map_tprod, PiTensorProduct.congr_tprod, PiTensorProduct.congr_tprod,
      PiTensorProduct.map_tprod]
    exact congrArg (PiTensorProduct.tprod ℂ) (funext fun i => h i (x i))
  exact LinearMap.congr_fun he z

private theorem map_equiv_slot_shift [DecidableEq ι] (e : ∀ i, V i ≃ₗ[ℂ] V' i) (i : ι)
    (A : Module.End ℂ (V i)) (A' : Module.End ℂ (V' i)) (a : ℂ)
    (h : ∀ x, e i (A x) = A' (e i x) + a • e i x) (z : ⨂[ℂ] j, V j) :
    PiTensorProduct.congr e (PiTensorProduct.map (Function.update (fun _ => LinearMap.id) i A) z) =
      PiTensorProduct.map (Function.update (fun _ => LinearMap.id) i A')
        (PiTensorProduct.congr e z) + a • PiTensorProduct.congr e z := by
  let L := fun j => (e j).toLinearMap
  let A₁ := Function.update (fun _ => LinearMap.id) i A
  let A₂ := Function.update (fun _ => LinearMap.id) i A'
  have h₁ : (fun j => (L j).comp (A₁ j)) =
      Function.update L i ((A'.comp (L i)) + a • L i) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp only [A₁, Function.update_self]
      exact LinearMap.ext h
    · simp [A₁, Function.update_of_ne hj]
  have h₂ : (fun j => (A₂ j).comp (L j)) = Function.update L i (A'.comp (L i)) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp [A₂]
    · simp [A₂, Function.update_of_ne hj]
  have hL : Function.update L i (L i) = L := by
    funext j
    by_cases hj : j = i <;> simp [hj]
  change (PiTensorProduct.map L ∘ₗ PiTensorProduct.map A₁) z =
    (PiTensorProduct.map A₂ ∘ₗ PiTensorProduct.map L) z + a • PiTensorProduct.map L z
  rw [← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp, h₁, h₂,
    PiTensorProduct.map_update_add, PiTensorProduct.map_update_smul, hL]
  rfl

end TensorOperations

private theorem equiv_add_of_shift {V V' : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (e : V ≃ₗ[ℂ] V') {x z : V} {y : V'} (a : ℂ) (h : y = e (x - a • z)) :
    e x = y + a • e z := by
  rw [h, map_sub, map_smul, sub_add_cancel]

section Evaluations

variable {n : ℕ} (B : BlockShape n) {R : Type uR} [RCLike R]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  {V' : Fin B.length → Type uV'} [∀ i, AddCommGroup (V' i)] [∀ i, Module ℂ (V' i)]

local notation "L" => Matrix (Fin n) (Fin n) R

/-- Before the inverse half-modulus twists, an upper triangular derivative of a
block evaluation is the sum of the diagonal block actions. -/
def IsUnnormalizedBlockLieEvaluation (π : (ℂ ⊗[ℝ] L) →ₗ⁅ℂ⁆ Module.End ℂ W)
    (A : ∀ i : Fin B.length, Matrix (Fin (B.size i)) (Fin (B.size i)) R → Module.End ℂ (V i))
    (ev : W →ₗ[ℂ] (⨂[ℂ] i, V i)) : Prop :=
  ∀ X : L, X.IsUpperTriangular → ∀ w : W,
    ev (π (1 ⊗ₜ X) w) = ∑ i, PiTensorProduct.map (Function.update (fun _ => LinearMap.id) i
      (A i (X.submatrix (B.index i) (B.index i)))) (ev w)

private theorem isNormalizedBlockLieEvaluation_of_slot_shifts
    {π : (ℂ ⊗[ℝ] L) →ₗ⁅ℂ⁆ Module.End ℂ W}
    (A : ∀ i : Fin B.length, Matrix (Fin (B.size i)) (Fin (B.size i)) R → Module.End ℂ (V i))
    (A' : ∀ i : Fin B.length, Matrix (Fin (B.size i)) (Fin (B.size i)) R → Module.End ℂ (V' i))
    (s : ∀ i : Fin B.length, Matrix (Fin (B.size i)) (Fin (B.size i)) R → ℂ)
    (e : ∀ i : Fin B.length, V i ≃ₗ[ℂ] V' i)
    (hslot : ∀ i X x, e i (A i X x) = A' i X (e i x) + s i X • e i x)
    (htrace : ∀ X : L, (∑ i, s i (X.submatrix (B.index i) (B.index i))) = blockHalfDifferential B X)
    (ev : W →ₗ[ℂ] (⨂[ℂ] i, V i)) (heval : IsUnnormalizedBlockLieEvaluation B π A ev) :
    IsNormalizedBlockLieEvaluation B π
      (fun i X => PiTensorProduct.map (Function.update (fun _ => LinearMap.id) i (A' i X)))
      ((PiTensorProduct.congr e).toLinearMap.comp ev) := by
  intro X hX w
  change PiTensorProduct.congr e (ev (π (1 ⊗ₜ X) w)) = _
  rw [heval X hX w, map_sum]
  simp_rw [map_equiv_slot_shift e _ _ _ _ (hslot _ _)]
  rw [Finset.sum_add_distrib, ← Finset.sum_smul, htrace]
  rfl

end Evaluations

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r c : ℕ} {m : Fin c → ℕ} (hm : ∑ i, (m i + 1) = r + 1)
  (T : ∀ i, CuspidalOperatorRealization F (m i))
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

local instance (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance {n : ℕ} (S : OperatorRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

private abbrev normalizationBlockShape : BlockShape (r + 1) :=
  ⟨c, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩

private abbrev rawCoefficientSpace := PiTensorProduct ℂ (fun i => ↥((T i).Space))

local notation "PShape" => normalizationBlockShape hm
local notation "E" => rawCoefficientSpace T
local notation "T₁" => normalizedCuspidalBlocks hm T
local notation "N" => r + 1
private abbrev normalizationEquiv := (normalizedCuspidalCoefficientEquiv hm T).toLinearEquiv
local notation "E₁" => normalizationEquiv hm T
local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}
local notation "RM" => Matrix (Fin N) (Fin N) ℝ
local notation "CM" => Matrix (Fin N) (Fin N) ℂ

private abbrev blockTwistEquiv (i : Fin c) :=
  ((T i).realization.heckeDeterminantTwistEquiv (inverseHalfBlockHeckeCharacter F PShape i)).toLinearEquiv

set_option maxHeartbeats 1200000 in
/-- Normalizing the restored real cuspidal blocks adds exactly the real
half-modulus differential to the evaluation identity. -/
theorem normalizedCuspidalBlocks_realLieEvaluation (v : RP)
    (π : (ℂ ⊗[ℝ] RM) →ₗ⁅ℂ⁆ Module.End ℂ W) (ev : W →ₗ[ℂ] E)
    (heval : IsUnnormalizedBlockLieEvaluation PShape π
      (fun i X => (T i).realization.realPlaceLieAction v (1 ⊗ₜ X)) ev) :
    IsNormalizedBlockLieEvaluation PShape π (realCuspidalBlockLie T₁ v)
      ((E₁).toLinearMap.comp ev) := by
  refine isNormalizedBlockLieEvaluation_of_slot_shifts PShape
    (fun i X => (T i).realization.realPlaceLieAction v (1 ⊗ₜ X))
    (fun i X => (T₁ i).realization.realPlaceLieAction v (1 ⊗ₜ X))
    (fun i X => (↑(blockHalfExponent (fun j => m j + 1) i * X.trace) : ℂ))
    (blockTwistEquiv hm T) ?_ ?_ ev heval
  · intro i X x
    exact equiv_add_of_shift (blockTwistEquiv hm T i) _
      (realPlaceLieAction_inverseHalfBlockTwist PShape F i (T i).realization v X x)
  · intro X
    rw [blockHalfDifferential_real, Complex.ofReal_sum]
    rfl

set_option maxHeartbeats 1200000 in
/-- Normalizing the restored complex cuspidal blocks adds exactly the complex
half-modulus differential to the evaluation identity. -/
theorem normalizedCuspidalBlocks_complexLieEvaluation (v : CP)
    (π : (ℂ ⊗[ℝ] CM) →ₗ⁅ℂ⁆ Module.End ℂ W) (ev : W →ₗ[ℂ] E)
    (heval : IsUnnormalizedBlockLieEvaluation PShape π
      (fun i X => (T i).realization.complexPlaceLieAction v (1 ⊗ₜ X)) ev) :
    IsNormalizedBlockLieEvaluation PShape π (complexCuspidalBlockLie T₁ v)
      ((E₁).toLinearMap.comp ev) := by
  refine isNormalizedBlockLieEvaluation_of_slot_shifts PShape
    (fun i X => (T i).realization.complexPlaceLieAction v (1 ⊗ₜ X))
    (fun i X => (T₁ i).realization.complexPlaceLieAction v (1 ⊗ₜ X))
    (fun i X => (↑(blockHalfExponent (fun j => m j + 1) i * (2 * X.trace.re)) : ℂ))
    (blockTwistEquiv hm T) ?_ ?_ ev heval
  · intro i X x
    exact equiv_add_of_shift (blockTwistEquiv hm T i) _
      (complexPlaceLieAction_inverseHalfBlockTwist PShape F i (T i).realization v X x)
  · intro X
    rw [blockHalfDifferential_complex, Complex.ofReal_sum]
    rfl

set_option maxHeartbeats 800000 in
/-- Normalization preserves the compact covariance of the evaluation at a real place. -/
theorem normalizedCuspidalBlocks_realCompactEvaluation (v : RP)
    (κ : Representation ℂ (Matrix.unitaryGroup (Fin N) ℝ) W) (ev : W →ₗ[ℂ] E)
    (heval : IsBlockCompactEvaluation (B := PShape) κ
      (fun i => (T i).realization.realPlaceCompactRepresentation v) ev) :
    IsBlockCompactEvaluation (B := PShape) κ
      (fun i => (T₁ i).realization.realPlaceCompactRepresentation v) ((E₁).toLinearMap.comp ev) := by
  intro k w
  have h := congrArg (E₁) (heval k w)
  exact h.trans (map_equiv_intertwines (blockTwistEquiv hm T)
    (fun i => (T i).realization.realPlaceCompactRepresentation v (k i))
    (fun i => (T₁ i).realization.realPlaceCompactRepresentation v (k i))
    (fun i x => (realPlaceCompactRepresentation_inverseHalfBlockTwist PShape F i
      (T i).realization v (k i) x).symm) (ev w))

set_option maxHeartbeats 800000 in
/-- Normalization preserves the compact covariance of the evaluation at a complex place. -/
theorem normalizedCuspidalBlocks_complexCompactEvaluation (v : CP)
    (κ : Representation ℂ (Matrix.unitaryGroup (Fin N) ℂ) W) (ev : W →ₗ[ℂ] E)
    (heval : IsBlockCompactEvaluation (B := PShape) κ
      (fun i => (T i).realization.complexPlaceCompactRepresentation v) ev) :
    IsBlockCompactEvaluation (B := PShape) κ
      (fun i => (T₁ i).realization.complexPlaceCompactRepresentation v) ((E₁).toLinearMap.comp ev) := by
  intro k w
  have h := congrArg (E₁) (heval k w)
  exact h.trans (map_equiv_intertwines (blockTwistEquiv hm T)
    (fun i => (T i).realization.complexPlaceCompactRepresentation v (k i))
    (fun i => (T₁ i).realization.complexPlaceCompactRepresentation v (k i))
    (fun i x => (complexPlaceCompactRepresentation_inverseHalfBlockTwist PShape F i
      (T i).realization v (k i) x).symm) (ev w))

end Langlands.Global.FiniteParametrizedBlockInduction
