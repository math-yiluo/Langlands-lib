import Langlands.Global.ArchimedeanCartanInvariantTensorAction
import Langlands.Global.ArchimedeanCartanFilteredCovariantAction

/-! # Finite central orbit coverings of actual compact fixed vectors -/

noncomputable section
universe u w
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

attribute [local instance 100] LieRing.ofAssociativeRing

local instance (τ : ContinuousCompactRep K n) :
    SMul (lieSymmetricGroupInvariants K n) (cartanSymmetricCovariants K n τ) :=
  (cartanSymmetricCovariants_groupInvariantModule K n τ).toSMul

section Module

variable {V : Type w} [AddCommGroup V] [Module ℂ V]
  [Module (EnvelopingAlgebra K n) V] [IsScalarTower ℂ (EnvelopingAlgebra K n) V]

/-- The sum of the full central orbits of the finitely many covariant images. -/
def cartanCovariantCentralSpan (τ : ContinuousCompactRep K n)
    (j : (Fin τ.dim → ℂ) →ₗ[ℂ] V) (G : HomogeneousCartanCovariantGenerators K n τ) :
    Submodule ℂ V :=
  ⨆ i : Fin G.size, Submodule.span ℂ
    (Set.range fun z : EnvelopingCenter K n =>
      (z : EnvelopingAlgebra K n) • cartanTensorAction K n τ j (G.generator i).val)

omit [NumberField K] in
theorem central_smul_mem_cartanCovariantCentralSpan (τ : ContinuousCompactRep K n)
    (j : (Fin τ.dim → ℂ) →ₗ[ℂ] V) (G : HomogeneousCartanCovariantGenerators K n τ)
    (i : Fin G.size) (z : EnvelopingCenter K n) :
    (z : EnvelopingAlgebra K n) • cartanTensorAction K n τ j (G.generator i).val ∈
      cartanCovariantCentralSpan K n τ j G :=
  Submodule.mem_iSup_of_mem i (Submodule.subset_span ⟨z, rfl⟩)

omit [IsScalarTower ℂ (EnvelopingAlgebra K n) V] in
/-- The central coefficients used in the degree comparison are fixed by the
whole compact group, even when other central elements need not be fixed. -/
theorem centralSymmetrize_smul_mem_compactInvariants
    (ρ : _root_.Representation ℂ (standardInfiniteCompact K n) V)
    (hρ : ∀ k a v, ρ k (a • v) = envelopingConjugation K n k.val a • ρ k v)
    (P : lieSymmetricGroupInvariants K n) (v : ρ.invariants) :
    (lieSymmetricGroupInvariantCentralSymmetrize K n P : EnvelopingAlgebra K n) •
        v.val ∈ ρ.invariants := by
  intro k
  rw [hρ, v.property k]
  exact congrArg (fun a : EnvelopingAlgebra K n => a • v.val)
    ((lieSymmetricGroupInvariantSymmetrize K n P).property k.val)

variable (τ : ContinuousCompactRep K n) (j : (Fin τ.dim → ℂ) →ₗ[ℂ] V)
  (ρ : _root_.Representation ℂ (standardInfiniteCompact K n) V)
  (hj : ∀ k v, j (τ.toRepresentation k v) = ρ k (j v))
  (hρ : ∀ k a v, ρ k (a • v) = envelopingConjugation K n k.val a • ρ k v)
  (hstable : ∀ X : CompactComplexLieAlgebra K n, ∀ v ∈ LinearMap.range j,
    compactEnvelopingGenerator K n X • v ∈ LinearMap.range j)
  (G : HomogeneousCartanCovariantGenerators K n τ)

include hj hρ hstable

private theorem homogeneous_cartanTensorAction_mem_centralSpan
    (d : ℕ)
    (hprev : ∀ e, e < d → ∀ y : ρ.invariants,
      y.val ∈ envelopingDegreeFiltration K n e • LinearMap.range j →
        y.val ∈ cartanCovariantCentralSpan K n τ j G)
    (x : cartanSymmetricCovariants K n τ)
    (hx : IsHomogeneousCartanCovariant K n τ d x) :
    cartanTensorAction K n τ j x.val ∈ cartanCovariantCentralSpan K n τ j G := by
  classical
  let Φ : cartanSymmetricCovariants K n τ →ₗ[ℂ] V :=
    (cartanTensorAction K n τ j).comp
      ((cartanSymmetricCovariants K n τ).restrictScalars ℂ).subtype
  change Φ x ∈ cartanCovariantCentralSpan K n τ j G
  obtain ⟨c, hc, hz, hs⟩ := G.exists_homogeneous_coefficients d x hx
  let m : Fin G.size → V := fun i =>
    (lieSymmetricGroupInvariantCentralSymmetrize K n (c i) : EnvelopingAlgebra K n) •
      Φ (G.generator i)
  have hm (i : Fin G.size) : m i ∈ cartanCovariantCentralSpan K n τ j G :=
    central_smul_mem_cartanCovariantCentralSpan K n τ j G i _
  have hmf (i : Fin G.size) : m i ∈ ρ.invariants :=
    centralSymmetrize_smul_mem_compactInvariants K n ρ hρ (c i)
      (cartanInvariantTensorAction K n τ j ρ hj hρ (G.generator i))
  have hsum : ∑ i, Φ (c i • G.generator i) = Φ x := by
    rw [← map_sum, hs]
  have hmain : ∑ i, m i ∈ cartanCovariantCentralSpan K n τ j G :=
    Submodule.sum_mem _ (fun i _ => hm i)
  by_cases hd : d = 0
  · subst d
    have heq (i : Fin G.size) : m i = Φ (c i • G.generator i) := by
      have hP : (c i).val ∈ lieSymmetricDegreeFiltration K n 0 := by
        rw [← hc i]
        simpa only [Nat.zero_sub] using
          lieSymmetricComponent_mem_degreeFiltration K n (0 - G.degree i) (c i).val
      exact centralSymmetrize_cartanCovariant_action_eq_of_degree_zero K n τ j
        (c i) hP (G.generator i)
    simpa only [heq, hsum] using hmain
  · have herr (i : Fin G.size) :
        m i - Φ (c i • G.generator i) ∈
          envelopingDegreeFiltration K n (d - 1) • LinearMap.range j := by
      by_cases hi : G.degree i ≤ d
      · have hP : (c i).val ∈ lieSymmetricDegreeFiltration K n (d - G.degree i) := by
          rw [← hc i]
          exact lieSymmetricComponent_mem_degreeFiltration K n _ _
        have h := centralSymmetrize_cartanCovariant_action_sub_mem K n τ j hstable
          (c i) hP ((G.homogeneous i).mem_degreeFiltration K n)
        change
          (lieSymmetricGroupInvariantCentralSymmetrize K n (c i) : EnvelopingAlgebra K n) •
              cartanTensorAction K n τ j (G.generator i).val -
            cartanTensorAction K n τ j (c i • G.generator i).val ∈ _
        simpa only [Nat.sub_add_cancel hi] using h
      · have hci : c i = 0 := hz i (by omega)
        simp only [m, hci, map_zero, ZeroMemClass.coe_zero, zero_smul, sub_self]
        exact Submodule.zero_mem _
    have herrsum : (∑ i, m i) - Φ x ∈
        envelopingDegreeFiltration K n (d - 1) • LinearMap.range j := by
      rw [← hsum, ← Finset.sum_sub_distrib]
      exact Submodule.sum_mem _ (fun i _ => herr i)
    have herrfixed : (∑ i, m i) - Φ x ∈ ρ.invariants :=
      ρ.invariants.sub_mem (Submodule.sum_mem _ (fun i _ => hmf i))
        (cartanInvariantTensorAction K n τ j ρ hj hρ x).property
    have hsmall := hprev (d - 1) (by omega) ⟨_, herrfixed⟩ herrsum
    have h := (cartanCovariantCentralSpan K n τ j G).sub_mem hmain hsmall
    simpa only [sub_sub_cancel] using h

/-- Every compact fixed vector in a filtered generated orbit belongs to finitely
many full central orbits, with a family independent of the filtration degree. -/
theorem fixed_mem_cartanCovariantCentralSpan_of_mem_envelopingDegree
    (d : ℕ) (y : ρ.invariants)
    (hy : y.val ∈ envelopingDegreeFiltration K n d • LinearMap.range j) :
    y.val ∈ cartanCovariantCentralSpan K n τ j G := by
  classical
  induction d using Nat.strong_induction_on generalizing y with
  | h d ih =>
    obtain ⟨x, hx, heq⟩ :=
      exists_cartanInvariantTensorAction_preimage_envelopingDegree K n τ j ρ hj hρ
        hstable d y hy
    let Φ := cartanInvariantTensorAction K n τ j ρ hj hρ
    have hsum := sum_cartanSymmetricCovariantComponents_of_mem_degreeFiltration
      K n τ (x := x) hx
    have hsumimage :
        ∑ e ∈ Finset.range (d + 1),
          (Φ (cartanSymmetricCovariantComponent K n τ e x) : V) = y.val := by
      calc
        _ = (Φ (∑ e ∈ Finset.range (d + 1),
            cartanSymmetricCovariantComponent K n τ e x) : V) := by
          simp only [map_sum, Submodule.coe_sum]
        _ = y.val := by rw [hsum, heq]
    rw [← hsumimage]
    apply Submodule.sum_mem
    intro e he
    apply homogeneous_cartanTensorAction_mem_centralSpan K n τ j ρ hj hρ hstable G e
    · intro a hae z hz
      exact ih a (by have := Finset.mem_range.mp he; omega) z hz
    · exact cartanSymmetricCovariantComponent_homogeneous K n τ e x

/-- Every fixed vector of the full enveloping orbit span has the same finite
central covering. No finiteness or topology on the target module is assumed. -/
theorem fixed_mem_cartanCovariantCentralSpan
    (y : ρ.invariants)
    (hy : y.val ∈ (⊤ : Submodule ℂ (EnvelopingAlgebra K n)) • LinearMap.range j) :
    y.val ∈ cartanCovariantCentralSpan K n τ j G := by
  have hmono : Monotone (fun d =>
      envelopingDegreeFiltration K n d • LinearMap.range j) :=
    fun d e h => Submodule.smul_mono_left (envelopingDegreeFiltration_mono K n h)
  rw [← iSup_envelopingDegreeFiltration K n, Submodule.iSup_smul] at hy
  obtain ⟨d, hd⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).mp hy
  exact fixed_mem_cartanCovariantCentralSpan_of_mem_envelopingDegree K n τ j ρ hj hρ
    hstable G d y hd

/-- Choosing the actual finite homogeneous covariant generators supplies a finite
full-center covering of the fixed part of the generated module. -/
theorem exists_finite_central_orbit_cover_of_compact_fixed :
    ∃ (m : ℕ) (v : Fin m → V),
      (∀ i, v i ∈ ρ.invariants) ∧
      ∀ y : ρ.invariants,
        y.val ∈ (⊤ : Submodule ℂ (EnvelopingAlgebra K n)) • LinearMap.range j →
        y.val ∈ ⨆ i : Fin m, Submodule.span ℂ
          (Set.range fun z : EnvelopingCenter K n => (z : EnvelopingAlgebra K n) • v i) := by
  let H := homogeneousCartanCovariantGenerators K n τ
  refine ⟨H.size, fun i => cartanTensorAction K n τ j (H.generator i).val, ?_, ?_⟩
  · intro i
    exact (cartanInvariantTensorAction K n τ j ρ hj hρ (H.generator i)).property
  · intro y hy
    exact fixed_mem_cartanCovariantCentralSpan K n τ j ρ hj hρ hstable H y hy

end Module

end Langlands.Global.ArchimedeanGL
