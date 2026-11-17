import Langlands.Automorphic.ArchimedeanResidualStructures
import Langlands.Automorphic.ArchimedeanMultiplicityContraction
import Langlands.Automorphic.TensorPairingTransport
import Mathlib.Data.Fintype.Option

/-! # Assembly of pairings for a finite family of commuting compact and Lie actions -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Langlands.Archimedean.FiniteFamilyPairing

open scoped TensorProduct
open GKTensorEvaluation
open Langlands.Automorphic

attribute [local instance 100] LieRing.ofAssociativeRing

universe uI uK uL uA uV

section Definitions

variable {I : Type uI} {K : I → Type uK} [∀ i, Group (K i)]
  {L : I → Type uL} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℂ (L i)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Different local compact and Lie operator families commute on the same carrier. -/
def FamilyCommutes (κ : ∀ i, Representation ℂ (K i) V)
    (ψ : ∀ i, L i →ₗ⁅ℂ⁆ Module.End ℂ V) : Prop :=
  (∀ i j, i ≠ j → ∀ k l x, κ i k (κ j l x) = κ j l (κ i k x)) ∧
  (∀ i j, i ≠ j → ∀ k X x, κ i k (ψ j X x) = ψ j X (κ i k x)) ∧
  ∀ i j, i ≠ j → ∀ X Y x, ψ i X (ψ j Y x) = ψ j Y (ψ i X x)

/-- Nonzeroness and irreducibility for all local action families together. -/
def FamilyIrreducible (κ : ∀ i, Representation ℂ (K i) V)
    (ψ : ∀ i, L i →ₗ⁅ℂ⁆ Module.End ℂ V) : Prop :=
  Nontrivial V ∧ ∀ N : Submodule ℂ V,
    (∀ i k x, x ∈ N → κ i k x ∈ N) →
    (∀ i X x, x ∈ N → ψ i X x ∈ N) → N = ⊥ ∨ N = ⊤

end Definitions

section SinglePairing

variable {K : Type uK} [Group K] {L : Type uL} [LieRing L] [LieAlgebra ℂ L]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A bilinear form invariant under a supplied compact twist and the corresponding
skew-invariant Lie twist. The maps need no extra laws for this algebraic condition. -/
def IsTwistedPairing (θK : K → K) (θL : L → L)
    (κ : Representation ℂ K V) (ψ : L →ₗ⁅ℂ⁆ Module.End ℂ V)
    (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) : Prop :=
  (∀ k x y, B (κ k x) (κ (θK k) y) = B x y) ∧
    ∀ X x y, B (ψ X x) y + B x (ψ (θL X) y) = 0

end SinglePairing

/-- The finite-family assembly property, allowing arbitrary target carriers in a universe
closed under taking the supplied source multiplicities. -/
def Assembly (I : Type uI) : Prop :=
  ∀ (K : I → Type uK) [∀ i, Group (K i)] [∀ i, TopologicalSpace (K i)]
    (L : I → Type uL) [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℂ (L i)]
    (A : I → Type uA) [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]
    (σ : ∀ i, Representation ℂ (K i) (A i))
    (p : ∀ i, L i →ₗ⁅ℂ⁆ Module.End ℂ (A i))
    (θK : ∀ i, K i → K i) (θL : ∀ i, L i → L i),
    (∀ i, GKModuleDensity.Hyp (σ i) (p i)) →
    (∀ i, ∃ B : A i →ₗ[ℂ] A i →ₗ[ℂ] ℂ,
      IsTwistedPairing (θK i) (θL i) (σ i) (p i) B ∧ B ≠ 0) →
    ∀ (V : Type (max uA uV)) [AddCommGroup V] [Module ℂ V]
      (κ : ∀ i, Representation ℂ (K i) V) (ψ : ∀ i, L i →ₗ⁅ℂ⁆ Module.End ℂ V),
      FamilyCommutes κ ψ → FamilyIrreducible κ ψ →
      (∀ i, ∃ f : gkHoms (σ i) (p i) (κ i) (ψ i), f ≠ 0) →
      ∃ B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ,
        (∀ i, IsTwistedPairing (θK i) (θL i) (κ i) (ψ i) B) ∧ B ≠ 0

/-- Nonzero local pairings assemble for every finite family of commuting actions. -/
theorem assembly (I : Type uI) [Finite I] : Assembly.{uI, uK, uL, uA, uV} I := by
  classical
  refine Finite.induction_empty_option
    (P := fun J => Assembly.{uI, uK, uL, uA, uV} J) ?_ ?_ ?_ I
  · intro α β e ih K _ _ L _ _ A _ _ σ p θK θL hD hB V _ _ κ ψ hComm hI hE
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
    obtain ⟨B, hpair, hB0⟩ := ih (fun i => K (e i)) (fun i => L (e i))
      (fun i => A (e i)) (fun i => σ (e i)) (fun i => p (e i))
      (fun i => θK (e i)) (fun i => θL (e i)) (fun i => hD (e i))
      (fun i => hB (e i)) V (fun i => κ (e i)) (fun i => ψ (e i))
      hComm' hI' (fun i => hE (e i))
    refine ⟨B, ?_, hB0⟩
    intro i
    obtain ⟨j, rfl⟩ := e.surjective i
    exact hpair j
  · intro K _ _ L _ _ A _ _ σ p θK θL hD hB V _ _ κ ψ hComm hI hE
    let := hI.1
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one ℂ hv
    let B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ := φ.smulRight φ
    refine ⟨B, fun i => PEmpty.elim i, ?_⟩
    intro hzero
    have hvv := congrArg (fun C : V →ₗ[ℂ] V →ₗ[ℂ] ℂ => C v v) hzero
    change φ v * φ v = 0 at hvv
    rw [hφ, one_mul] at hvv
    exact one_ne_zero hvv
  · intro α _ ih K _ _ L _ _ A _ _ σ p θK θL hD hB V _ _ κ ψ hComm hI hE
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
    obtain ⟨D, hDpair, hD0⟩ := ih (fun j => K (some j)) (fun j => L (some j))
      (fun j => A (some j)) (fun j => σ (some j)) (fun j => p (some j))
      (fun j => θK (some j)) (fun j => θL (some j))
      (fun j => hD (some j)) (fun j => hB (some j)) M κM ψM hCommM hIM hEM
    obtain ⟨C, hCpair, hC0⟩ := hB none
    refine ⟨TensorPairing.transport e C D, ?_, TensorPairing.transport_ne_zero e C D hC0 hD0⟩
    intro i
    cases i with
    | none =>
      refine ⟨fun k x y => ?_, fun X x y => ?_⟩
      · exact TensorPairing.transport_invariant e C D (σ none k) (σ none (θK none k))
          LinearMap.id LinearMap.id (κ none k) (κ none (θK none k)) (hCpair.1 k)
          (fun _ _ => rfl) (evaluation_compact _ _ _ _ k)
          (evaluation_compact _ _ _ _ (θK none k)) x y
      · exact TensorPairing.transport_lie_left e C D (p none X) (p none (θL none X))
          (ψ none X) (ψ none (θL none X)) (hCpair.2 X)
          (evaluation_lie _ _ _ _ X) (evaluation_lie _ _ _ _ (θL none X)) x y
    | some j =>
      refine ⟨fun k x y => ?_, fun X x y => ?_⟩
      · exact TensorPairing.transport_invariant e C D LinearMap.id LinearMap.id
          (κM j k) (κM j (θK (some j) k)) (κ (some j) k) (κ (some j) (θK (some j) k))
          (fun _ _ => rfl) ((hDpair j).1 k) (heκ j k) (heκ j (θK (some j) k)) x y
      · exact TensorPairing.transport_lie_right e C D (ψM j X) (ψM j (θL (some j) X))
          (ψ (some j) X) (ψ (some j) (θL (some j) X)) ((hDpair j).2 X)
          (heψ j X) (heψ j (θL (some j) X)) x y

/-- Choose the assembled nonzero pairing together with all its simultaneous local identities. -/
def assemblePairing (I : Type uI) [Finite I]
    (K : I → Type uK) [∀ i, Group (K i)] [∀ i, TopologicalSpace (K i)]
    (L : I → Type uL) [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℂ (L i)]
    (A : I → Type uA) [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]
    (σ : ∀ i, Representation ℂ (K i) (A i))
    (p : ∀ i, L i →ₗ⁅ℂ⁆ Module.End ℂ (A i))
    (θK : ∀ i, K i → K i) (θL : ∀ i, L i → L i)
    (hD : ∀ i, GKModuleDensity.Hyp (σ i) (p i))
    (hB : ∀ i, ∃ B : A i →ₗ[ℂ] A i →ₗ[ℂ] ℂ,
      IsTwistedPairing (θK i) (θL i) (σ i) (p i) B ∧ B ≠ 0)
    (V : Type (max uA uV)) [AddCommGroup V] [Module ℂ V]
    (κ : ∀ i, Representation ℂ (K i) V) (ψ : ∀ i, L i →ₗ⁅ℂ⁆ Module.End ℂ V)
    (hComm : FamilyCommutes κ ψ) (hI : FamilyIrreducible κ ψ)
    (hE : ∀ i, ∃ f : gkHoms (σ i) (p i) (κ i) (ψ i), f ≠ 0) :
    {B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ //
      (∀ i, IsTwistedPairing (θK i) (θL i) (κ i) (ψ i) B) ∧ B ≠ 0} := by
  let h := assembly I K L A σ p θK θL hD hB V κ ψ hComm hI hE
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

end Langlands.Archimedean.FiniteFamilyPairing
