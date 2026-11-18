import Langlands.Automorphic.FiniteFamilyGKPairing
import Mathlib.LinearAlgebra.PiTensorProduct.Basic

/-! # Tensor decomposition for a finite family of commuting compact and Lie actions -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace Langlands.Archimedean.FiniteFamilyTensor

open scoped TensorProduct
open GKTensorEvaluation FiniteFamilyPairing
open Langlands.Automorphic

attribute [local instance 100] LieRing.ofAssociativeRing

universe uI uK uL uA uV

/-- Separate the `none` factor from an option-indexed dependent tensor product. -/
def optionEquiv {ι : Type uI} (A : Option ι → Type uA)
    [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)] :
    (⨂[ℂ] i, A i) ≃ₗ[ℂ] A none ⊗[ℂ] (⨂[ℂ] i, A (some i)) := by
  let e : Option ι ≃ ι ⊕ PUnit.{1} := Equiv.optionEquivSumPUnit ι
  exact (PiTensorProduct.reindex ℂ A e).trans
    ((PiTensorProduct.tmulEquivDep ℂ (fun i => A (e.symm i))).symm.trans
      ((TensorProduct.congr (LinearEquiv.refl ℂ _)
        (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : PUnit.{1} => A none) PUnit.unit)).trans
        (TensorProduct.comm ℂ _ _)))

@[simp] theorem optionEquiv_tprod {ι : Type uI} (A : Option ι → Type uA)
    [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)] (a : ∀ i, A i) :
    optionEquiv A (PiTensorProduct.tprod ℂ a) =
      a none ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (fun i => a (some i)) := by
  dsimp only [optionEquiv, LinearEquiv.trans_apply]
  rw [PiTensorProduct.reindex_tprod, PiTensorProduct.tmulEquivDep_symm_apply]
  simp

section Covariance

variable {I : Type uI} {K : I → Type uK} [∀ i, Group (K i)]
    {L : I → Type uL} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℂ (L i)]
    {A : I → Type uA} [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Pure tensors intertwine each local action while every other component is fixed. -/
def IsTensorEquivalence
    (σ : ∀ i, Representation ℂ (K i) (A i))
    (p : ∀ i, L i →ₗ⁅ℂ⁆ Module.End ℂ (A i))
    (κ : ∀ i, Representation ℂ (K i) V)
    (ψ : ∀ i, L i →ₗ⁅ℂ⁆ Module.End ℂ V)
    (e : (⨂[ℂ] i, A i) ≃ₗ[ℂ] V) : Prop :=
  (∀ i k (a b : ∀ j, A j), (∀ j, j ≠ i → b j = a j) → b i = σ i k (a i) →
    e (PiTensorProduct.tprod ℂ b) = κ i k (e (PiTensorProduct.tprod ℂ a))) ∧
  ∀ i X (a b : ∀ j, A j), (∀ j, j ≠ i → b j = a j) → b i = p i X (a i) →
    e (PiTensorProduct.tprod ℂ b) = ψ i X (e (PiTensorProduct.tprod ℂ a))

end Covariance

/-- Simultaneous source occurrences in a jointly irreducible target yield its
finite dependent tensor decomposition. -/
def TensorDecompositionStatement (I : Type uI) : Prop :=
  ∀ (K : I → Type uK) [∀ i, Group (K i)] [∀ i, TopologicalSpace (K i)]
    (L : I → Type uL) [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℂ (L i)]
    (A : I → Type uA) [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]
    (σ : ∀ i, Representation ℂ (K i) (A i))
    (p : ∀ i, L i →ₗ⁅ℂ⁆ Module.End ℂ (A i)),
    (∀ i, GKModuleDensity.Hyp (σ i) (p i)) →
    ∀ (V : Type (max uA uV)) [AddCommGroup V] [Module ℂ V]
      (κ : ∀ i, Representation ℂ (K i) V) (ψ : ∀ i, L i →ₗ⁅ℂ⁆ Module.End ℂ V),
      FamilyCommutes κ ψ → FamilyIrreducible κ ψ →
      (∀ i, ∃ f : gkHoms (σ i) (p i) (κ i) (ψ i), f ≠ 0) →
      ∃ e : (⨂[ℂ] i, A i) ≃ₗ[ℂ] V, IsTensorEquivalence σ p κ ψ e

/-- Every finite jointly irreducible commuting family is the tensor product of
its occurring source models. -/
theorem tensorDecomposition (I : Type uI) [Finite I] :
    TensorDecompositionStatement.{uI, uK, uL, uA, uV} I := by
  classical
  refine Finite.induction_empty_option
    (P := fun J => TensorDecompositionStatement.{uI, uK, uL, uA, uV} J) ?_ ?_ ?_ I
  · intro α β e ih K _ _ L _ _ A _ _ σ p hD V _ _ κ ψ hComm hI hE
    have hComm' : FamilyCommutes (fun i => κ (e i)) (fun i => ψ (e i)) :=
      ⟨fun i j hij => hComm.1 _ _ (fun h => hij (e.injective h)),
        fun i j hij => hComm.2.1 _ _ (fun h => hij (e.injective h)),
        fun i j hij => hComm.2.2 _ _ (fun h => hij (e.injective h))⟩
    have hI' : FamilyIrreducible (fun i => κ (e i)) (fun i => ψ (e i)) := by
      refine ⟨hI.1, fun N hk hl => hI.2 N ?_ ?_⟩
      · intro i k x hx
        obtain ⟨j, rfl⟩ := e.surjective i
        exact hk j k x hx
      · intro i X x hx
        obtain ⟨j, rfl⟩ := e.surjective i
        exact hl j X x hx
    obtain ⟨E, hEcov⟩ := ih (fun i => K (e i)) (fun i => L (e i))
      (fun i => A (e i)) (fun i => σ (e i)) (fun i => p (e i)) (fun i => hD (e i))
      V (fun i => κ (e i)) (fun i => ψ (e i)) hComm' hI' (fun i => hE (e i))
    refine ⟨(PiTensorProduct.reindex ℂ A e.symm).trans E, ?_, ?_⟩
    · intro i k a b hother hlocal
      obtain ⟨j, rfl⟩ := e.surjective i
      dsimp only [LinearEquiv.trans_apply]
      rw [PiTensorProduct.reindex_tprod, PiTensorProduct.reindex_tprod]
      exact hEcov.1 j k (fun j => a (e j)) (fun j => b (e j))
          (fun l hl => hother (e l) (fun h => hl (e.injective h))) hlocal
    · intro i X a b hother hlocal
      obtain ⟨j, rfl⟩ := e.surjective i
      dsimp only [LinearEquiv.trans_apply]
      rw [PiTensorProduct.reindex_tprod, PiTensorProduct.reindex_tprod]
      exact hEcov.2 j X (fun j => a (e j)) (fun j => b (e j))
          (fun l hl => hother (e l) (fun h => hl (e.injective h))) hlocal
  · intro K _ _ L _ _ A _ _ σ p hD V _ _ κ ψ hComm hI hE
    let := hI.1
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one ℂ hv
    have hker : LinearMap.ker φ = ⊥ := by
      rcases hI.2 (LinearMap.ker φ) (fun i => PEmpty.elim i)
          (fun i => PEmpty.elim i) with hbot | htop
      · exact hbot
      · have hz : φ v = 0 := LinearMap.mem_ker.mp (htop ▸ Submodule.mem_top)
        exact (one_ne_zero (hφ.symm.trans hz)).elim
    let g : V ≃ₗ[ℂ] ℂ := LinearEquiv.ofBijective φ
      ⟨LinearMap.ker_eq_bot.mp hker, fun c => ⟨c • v, by simp [hφ]⟩⟩
    exact ⟨(PiTensorProduct.isEmptyEquiv (R := ℂ) (s := A) PEmpty).trans g.symm,
      ⟨fun i => PEmpty.elim i, fun i => PEmpty.elim i⟩⟩
  · intro α _ ih K _ _ L _ _ A _ _ σ p hD V _ _ κ ψ hComm hI hE
    let M := GKTensorEvaluation.Multiplicity (σ none) (p none) (κ none) (ψ none)
    let : AddCommGroup M := (gkHoms (σ none) (p none) (κ none) (ψ none)).addCommGroup
    obtain ⟨f₀, hf₀⟩ := hE none
    have hM : Nontrivial M := ⟨f₀, 0, hf₀⟩
    let τ : ((Σ j : α, K (some j)) ⊕ (Σ j : α, L (some j))) → Module.End ℂ V :=
      Sum.elim (fun z => κ (some z.1) z.2) (fun z => ψ (some z.1) z.2)
    have hτk : ∀ i k x, τ i (κ none k x) = κ none k (τ i x) := by
      intro i k x
      cases i with
      | inl z => exact hComm.1 (some z.1) none (by simp) z.2 k x
      | inr z => exact (hComm.2.1 none (some z.1) (by simp) k z.2 x).symm
    have hτl : ∀ i X x, τ i (ψ none X x) = ψ none X (τ i x) := by
      intro i X x
      cases i with
      | inl z => exact hComm.2.1 (some z.1) none (by simp) z.2 X x
      | inr z => exact hComm.2.2 (some z.1) none (by simp) z.2 X x
    have hjoint : GKTensorEvaluation.IsIrreducibleWith (κ none) (ψ none) τ := by
      refine ⟨hI.1, fun N hk hl ht => hI.2 N ?_ ?_⟩
      · intro i k x hx
        cases i with
        | none => exact hk k x hx
        | some j => exact ht (Sum.inl ⟨j, k⟩) x hx
      · intro i X x hx
        cases i with
        | none => exact hl X x hx
        | some j => exact ht (Sum.inr ⟨j, X⟩) x hx
    let e := GKTensorEvaluation.evaluationEquiv (σ none) (p none) (κ none) (ψ none)
      τ hτk hτl (hD none) hjoint hM
    let κM : ∀ j : α, Representation ℂ (K (some j)) M := fun j =>
      postcomposeRepresentation (σ none) (p none) (κ none) (ψ none) (κ (some j))
        (fun k l x => hComm.1 (some j) none (by simp) k l x)
        (fun k X x => hComm.2.1 (some j) none (by simp) k X x)
    let ψM : ∀ j : α, L (some j) →ₗ⁅ℂ⁆ Module.End ℂ M := fun j =>
      postcomposeLie (σ none) (p none) (κ none) (ψ none) (ψ (some j))
        (fun X k x => (hComm.2.1 none (some j) (by simp) k X x).symm)
        (fun X Y x => hComm.2.2 (some j) none (by simp) X Y x)
    have heκ : ∀ j k t, e (TensorProduct.map LinearMap.id (κM j k) t) = κ (some j) k (e t) :=
      fun j k t => evaluation_postcomposeRepresentation (σ none) (p none) (κ none) (ψ none)
        (κ (some j)) _ _ k t
    have heψ : ∀ j X t, e (TensorProduct.map LinearMap.id (ψM j X) t) = ψ (some j) X (e t) :=
      fun j X t => evaluation_postcomposeLie (σ none) (p none) (κ none) (ψ none)
        (ψ (some j)) _ _ X t
    have hCommM : FamilyCommutes κM ψM := by
      refine ⟨?_, ?_, ?_⟩
      · intro i j hij k l f
        apply Subtype.ext
        apply LinearMap.ext
        intro a
        exact hComm.1 (some i) (some j) (by simpa using hij) k l (f.val a)
      · intro i j hij k X f
        apply Subtype.ext
        apply LinearMap.ext
        intro a
        exact hComm.2.1 (some i) (some j) (by simpa using hij) k X (f.val a)
      · intro i j hij X Y f
        apply Subtype.ext
        apply LinearMap.ext
        intro a
        exact hComm.2.2 (some i) (some j) (by simpa using hij) X Y (f.val a)
    have hIM : FamilyIrreducible κM ψM := by
      refine ⟨hM, fun N hk hl => ?_⟩
      apply (residual_irreducible (σ none) (p none) (κ none) (ψ none)
        τ hτk hτl (hD none) hjoint hM).2 N
      intro i f hf
      cases i with
      | inl z => exact hk z.1 z.2 f hf
      | inr z => exact hl z.1 z.2 f hf
    have hEM : ∀ j, ∃ f : gkHoms (σ (some j)) (p (some j)) (κM j) (ψM j), f ≠ 0 := by
      intro j
      obtain ⟨f, hf⟩ := hE (some j)
      obtain ⟨φ, hφ⟩ := TensorContraction.exists_nonzero_contractedGKHom
        (σ (some j)) (p (some j)) (κM j) (ψM j) (κ (some j)) (ψ (some j))
        e (heκ j) (heψ j) f hf
      exact ⟨_, hφ⟩
    obtain ⟨E, hEc⟩ := ih (fun j => K (some j)) (fun j => L (some j))
      (fun j => A (some j)) (fun j => σ (some j)) (fun j => p (some j))
      (fun j => hD (some j)) M κM ψM hCommM hIM hEM
    let F : (⨂[ℂ] i, A i) ≃ₗ[ℂ] V :=
      (optionEquiv A).trans ((TensorProduct.congr (LinearEquiv.refl ℂ _) E).trans e)
    have hF (a : ∀ i, A i) : F (PiTensorProduct.tprod ℂ a) =
        e (a none ⊗ₜ[ℂ] E (PiTensorProduct.tprod ℂ (fun j => a (some j)))) := by
      dsimp only [F, LinearEquiv.trans_apply]
      rw [optionEquiv_tprod, TensorProduct.congr_tmul]
      rfl
    refine ⟨F, ?_, ?_⟩
    · intro i k a b hother hlocal
      rw [hF, hF]
      cases i with
      | none =>
        have htail : (fun j => b (some j)) = (fun j => a (some j)) :=
          funext fun j => hother (some j) (by simp)
        rw [htail, hlocal]
        exact evaluation_compact (σ none) (p none) (κ none) (ψ none) k
          (a none ⊗ₜ[ℂ] E (PiTensorProduct.tprod ℂ (fun j => a (some j))))
      | some j =>
        rw [hother none (by simp)]
        have htail := hEc.1 j k (fun l => a (some l)) (fun l => b (some l))
          (fun l hl => hother (some l) (by simpa using hl)) hlocal
        rw [htail]
        exact heκ j k (a none ⊗ₜ[ℂ] E (PiTensorProduct.tprod ℂ (fun j => a (some j))))
    · intro i X a b hother hlocal
      rw [hF, hF]
      cases i with
      | none =>
        have htail : (fun j => b (some j)) = (fun j => a (some j)) :=
          funext fun j => hother (some j) (by simp)
        rw [htail, hlocal]
        exact evaluation_lie (σ none) (p none) (κ none) (ψ none) X
          (a none ⊗ₜ[ℂ] E (PiTensorProduct.tprod ℂ (fun j => a (some j))))
      | some j =>
        rw [hother none (by simp)]
        have htail := hEc.2 j X (fun l => a (some l)) (fun l => b (some l))
          (fun l hl => hother (some l) (by simpa using hl)) hlocal
        rw [htail]
        exact heψ j X (a none ⊗ₜ[ℂ] E (PiTensorProduct.tprod ℂ (fun j => a (some j))))

/-- The decomposition property for every finite index type, including the empty one. -/
def FiniteTensorDecompositionStatement : Prop :=
  ∀ (I : Type uI) [Finite I], TensorDecompositionStatement.{uI, uK, uL, uA, uV} I

/-- Simultaneous finite tensor decomposition with all universes free. -/
theorem finiteTensorDecomposition :
    FiniteTensorDecompositionStatement.{uI, uK, uL, uA, uV} := tensorDecomposition

end Langlands.Archimedean.FiniteFamilyTensor
