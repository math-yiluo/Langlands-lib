import Langlands.Automorphic.CuspidalAdmissible.PolynomialRayleigh
import Langlands.Automorphic.OperatorSubquotientCompactDifferentiation
import Langlands.Global.ArchimedeanCasimirCartan
import Langlands.Global.ArchimedeanCompactTangentProof

/-!
# A uniform polynomial annihilating the compact Casimir operator on a multiplicity space

Let a compact representation `ρ` on `V` be differentiated by a complex Lie action `A`
against linear functionals. Any subspace of `ι → V` (for finite `ι`) stable under
componentwise compact translation is then stable under componentwise compact Lie
derivatives, hence under the compact square sum `Ω_K = ∑ A(Y_j)²` over the normalized
compact Cartan basis.

For a representation `σ` of the compact group on `ℂ^m`, the common kernel of all
`σ`-equivariant maps `ℂ^m → V` is already the common kernel of finitely many of them
`φ_1, …, φ_r`. The characteristic polynomial `p` of `Ω_K` on the range of
`v ↦ (φ_i v)_i` then kills `φ v` for every equivariant `φ` and every `v`.
-/

noncomputable section

universe uF u

open Polynomial

namespace Langlands.Automorphic.CuspidalAdmissible

open Langlands.Global Langlands.Global.ArchimedeanGL

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

attribute [local instance 100] LieRing.ofAssociativeRing

section Generic

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- A subspace of `ι → V` is stable under the componentwise action of `T`. -/
def IsPiStable {ι : Type*} (T : Module.End ℂ V) (W : Submodule ℂ (ι → V)) : Prop :=
  ∀ w ∈ W, (fun i => T (w i)) ∈ W

namespace IsPiStable

variable {ι : Type*} {W : Submodule ℂ (ι → V)}

theorem mul {S T : Module.End ℂ V} (hS : IsPiStable S W) (hT : IsPiStable T W) :
    IsPiStable (S * T) W :=
  fun w hw => hS _ (hT w hw)

theorem add {S T : Module.End ℂ V} (hS : IsPiStable S W) (hT : IsPiStable T W) :
    IsPiStable (S + T) W :=
  fun w hw => W.add_mem (hS w hw) (hT w hw)

theorem zero : IsPiStable (0 : Module.End ℂ V) W := fun _ _ => W.zero_mem

theorem sum {α : Type*} (s : Finset α) (f : α → Module.End ℂ V)
    (h : ∀ a ∈ s, IsPiStable (f a) W) : IsPiStable (∑ a ∈ s, f a) W := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : IsPiStable (0 : Module.End ℂ V) W)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

end IsPiStable

/-- The componentwise action of `T` on `ι → V`. -/
def piEnd (ι : Type*) (T : Module.End ℂ V) : Module.End ℂ (ι → V) :=
  LinearMap.pi fun i => T ∘ₗ LinearMap.proj i

@[simp]
theorem piEnd_apply (ι : Type*) (T : Module.End ℂ V) (w : ι → V) (i : ι) :
    piEnd ι T w i = T (w i) := rfl

variable {ρ : Representation ℂ (standardInfiniteCompact F n) V}
  {A : ComplexLieAlgebra F n →ₗ⁅ℂ⁆ Module.End ℂ V}

/-- Componentwise compact stability implies componentwise stability under every compact
Lie derivative. -/
theorem isPiStable_compact (hA : CompactDualDerivative ρ A) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (W : Submodule ℂ (ι → V)) (hW : ∀ k, IsPiStable (ρ k) W)
    (Y : compactLieSubalgebra F n) : IsPiStable (A (complexify F n Y.val)) W := by
  intro w hw
  obtain ⟨c, hc0, hc⟩ := compactTangentCurve F n Y
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro μ hμ
  have hμW : ∀ x ∈ W, μ x = 0 := (Submodule.mem_dualAnnihilator μ).mp hμ
  have hsplit : ∀ x : ι → V,
      μ x = ∑ i, (μ ∘ₗ LinearMap.single ℂ (fun _ : ι => V) i) (x i) := by
    intro x
    conv_lhs => rw [← Finset.univ_sum_single x]
    rw [map_sum]
    rfl
  have hd : HasDerivAt
      (fun t => ∑ i, (μ ∘ₗ LinearMap.single ℂ (fun _ : ι => V) i) (ρ (c t) (w i)))
      (∑ i, (μ ∘ₗ LinearMap.single ℂ (fun _ : ι => V) i)
        (A (complexify F n Y.val) (w i))) 0 :=
    HasDerivAt.fun_sum fun i _ => hA Y.val c hc0 hc _ (w i)
  have hconst : (fun t => ∑ i, (μ ∘ₗ LinearMap.single ℂ (fun _ : ι => V) i)
      (ρ (c t) (w i))) = fun _ => 0 := by
    funext t
    rw [← hsplit (fun i => ρ (c t) (w i))]
    exact hμW _ (hW (c t) w hw)
  rw [hconst] at hd
  rw [hsplit]
  exact hd.unique (hasDerivAt_const 0 0)

/-- The compact square sum `∑ A(Y_j)²` over the normalized compact Cartan basis. -/
def compactSquareOperator (A : ComplexLieAlgebra F n →ₗ⁅ℂ⁆ Module.End ℂ V) :
    Module.End ℂ V :=
  ∑ i, A (complexify F n (compactCartanBasis F n i : RealLieAlgebra F n)) *
    A (complexify F n (compactCartanBasis F n i : RealLieAlgebra F n))

theorem isPiStable_compactSquareOperator (hA : CompactDualDerivative ρ A) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (W : Submodule ℂ (ι → V)) (hW : ∀ k, IsPiStable (ρ k) W) :
    IsPiStable (compactSquareOperator A) W :=
  IsPiStable.sum _ _ fun _ _ =>
    (isPiStable_compact hA W hW _).mul (isPiStable_compact hA W hW _)

omit [NumberField F] in
/-- **Uniform annihilator.** If `T` preserves every subspace of `ι → V` that is stable under
componentwise compact translation, then one nonzero polynomial in `T` kills the image of
every compact-equivariant map from a fixed representation `σ` on `ℂ^m`. -/
theorem exists_annihilator_of_piStable (T : Module.End ℂ V)
    (hT : ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] (W : Submodule ℂ (ι → V)),
      (∀ k, IsPiStable (ρ k) W) → IsPiStable T W)
    {m : ℕ} (σ : Representation ℂ (standardInfiniteCompact F n) (Fin m → ℂ)) :
    ∃ p : ℂ[X], p ≠ 0 ∧ ∀ φ : (Fin m → ℂ) →ₗ[ℂ] V,
      (∀ k v, φ (σ k v) = ρ k (φ v)) → ∀ v, aeval T p (φ v) = 0 := by
  classical
  let Φ : Set ((Fin m → ℂ) →ₗ[ℂ] V) := {φ | ∀ k v, φ (σ k v) = ρ k (φ v)}
  let 𝒮 : Set (Submodule ℂ (Fin m → ℂ)) :=
    {N | ∃ s : Finset ((Fin m → ℂ) →ₗ[ℂ] V), (↑s ⊆ Φ) ∧ N = ⨅ φ ∈ s, LinearMap.ker φ}
  obtain ⟨N₀, ⟨s₀, hs₀, hN₀⟩, hmin⟩ :=
    (wellFounded_lt (α := Submodule ℂ (Fin m → ℂ))).has_min 𝒮
      ⟨⊤, ∅, by simp, by simp⟩
  -- the minimal common kernel lies in the kernel of every equivariant map
  have hker : ∀ φ ∈ Φ, ∀ v ∈ N₀, φ v = 0 := by
    intro φ hφ v hv
    have hmem : LinearMap.ker φ ⊓ N₀ ∈ 𝒮 := by
      refine ⟨insert φ s₀, ?_, ?_⟩
      · rw [Finset.coe_insert]
        exact Set.insert_subset hφ hs₀
      · rw [Finset.iInf_insert, hN₀]
    have hle : LinearMap.ker φ ⊓ N₀ ≤ N₀ := inf_le_right
    have heq : LinearMap.ker φ ⊓ N₀ = N₀ := by
      by_contra hne
      exact hmin _ hmem (lt_of_le_of_ne hle hne)
    have : v ∈ LinearMap.ker φ ⊓ N₀ := by rw [heq]; exact hv
    exact this.1
  -- the fixed finite family and its range
  let ι₀ : Type u := {x // x ∈ s₀}
  let Φ₀ : (Fin m → ℂ) →ₗ[ℂ] (ι₀ → V) := LinearMap.pi fun ψ => ψ.1
  let R₀ := LinearMap.range Φ₀
  have hR₀ : ∀ k, IsPiStable (ρ k) R₀ := by
    rintro k _ ⟨v, rfl⟩
    refine ⟨σ k v, funext fun ψ => ?_⟩
    exact hs₀ ψ.2 k v
  have hT₀ : ∀ w ∈ R₀, piEnd ι₀ T w ∈ R₀ := hT ι₀ R₀ hR₀
  refine ⟨((piEnd ι₀ T).restrict hT₀).charpoly, (LinearMap.charpoly_monic _).ne_zero, ?_⟩
  intro φ hφ v
  set p := ((piEnd ι₀ T).restrict hT₀).charpoly
  -- the enlarged family
  let ι₁ : Type u := Option ι₀
  let Φ₁ : (Fin m → ℂ) →ₗ[ℂ] (ι₁ → V) :=
    LinearMap.pi fun o => Option.elim o φ fun ψ => ψ.1
  let R₁ := LinearMap.range Φ₁
  have hR₁ : ∀ k, IsPiStable (ρ k) R₁ := by
    rintro k _ ⟨v, rfl⟩
    refine ⟨σ k v, funext fun o => ?_⟩
    cases o with
    | none => exact hφ k v
    | some ψ => exact hs₀ ψ.2 k v
  have hT₁ : ∀ w ∈ R₁, piEnd ι₁ T w ∈ R₁ := hT ι₁ R₁ hR₁
  obtain ⟨v', hv'⟩ : aeval (piEnd ι₁ T) p (Φ₁ v) ∈ R₁ :=
    aeval_mem_of_stable _ hT₁ p ⟨v, rfl⟩
  -- forgetting the new coordinate
  let P : (ι₁ → V) →ₗ[ℂ] (ι₀ → V) := LinearMap.pi fun ψ => LinearMap.proj (some ψ)
  have hP : ∀ w, P (piEnd ι₁ T w) = piEnd ι₀ T (P w) := fun w => rfl
  have hPΦ : ∀ x, P (Φ₁ x) = Φ₀ x := fun x => rfl
  have h0 : Φ₀ v' = 0 := by
    rw [← hPΦ, hv', aeval_intertwine P hP, hPΦ]
    exact aeval_charpoly_restrict_apply _ hT₀ ⟨v, rfl⟩
  have hv'N : v' ∈ N₀ := by
    rw [hN₀]
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    intro ψ hψ
    exact congrFun h0 ⟨ψ, hψ⟩
  have hnone : (LinearMap.proj none : (ι₁ → V) →ₗ[ℂ] V)
      (aeval (piEnd ι₁ T) p (Φ₁ v)) = aeval T p (φ v) :=
    aeval_intertwine (A := piEnd ι₁ T) (A' := T) (LinearMap.proj none) (fun w => rfl) p
      (Φ₁ v)
  rw [← hnone, ← hv']
  exact hker φ hφ v' hv'N

end Generic

section Realization

open Langlands.Automorphic

local instance compactCasimirRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance compactCasimirContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance compactCasimirSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance compactCasimirFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance compactCasimirStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _

variable (S : OperatorRealization F n)

local instance compactCasimirSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

/-- The compact Casimir operator `∑ Y_j²` of a realization. -/
abbrev compactCasimirOperator : Module.End ℂ S.Space :=
  S.envelopingAction (ArchimedeanGL.compactCartanSquareSum F n)

theorem envelopingAction_realEnvelopingGenerator (Y : RealLieAlgebra F n) :
    S.envelopingAction (ArchimedeanGL.realEnvelopingGenerator F n Y) =
      S.complexLieAction (complexify F n Y) :=
  LinearMap.ext fun _ => rfl

theorem compactCasimirOperator_eq :
    compactCasimirOperator S = compactSquareOperator S.complexLieAction :=
  (map_sum S.envelopingAction (fun i => ArchimedeanGL.realEnvelopingGenerator F n
      (compactCartanBasis F n i : RealLieAlgebra F n) *
    ArchimedeanGL.realEnvelopingGenerator F n
      (compactCartanBasis F n i : RealLieAlgebra F n)) Finset.univ).trans
    (Finset.sum_congr rfl fun _ _ => (map_mul S.envelopingAction _ _).trans
      (congrArg₂ (· * ·) (envelopingAction_realEnvelopingGenerator S _)
        (envelopingAction_realEnvelopingGenerator S _)))

set_option maxHeartbeats 1000000 in
/-- **Uniform compact Casimir annihilator.** For a fixed representation `σ` of the standard
compact group on `ℂ^m`, one nonzero polynomial in the compact Casimir operator kills the
image of every compact-equivariant map `ℂ^m → S.Space`. -/
theorem exists_compactCasimir_annihilator {m : ℕ}
    (σ : Representation ℂ (standardInfiniteCompact F n) (Fin m → ℂ)) :
    ∃ p : ℂ[X], p ≠ 0 ∧ ∀ φ : (Fin m → ℂ) →ₗ[ℂ] S.Space,
      (∀ k v, φ (σ k v) = S.compactRepresentation k (φ v)) →
        ∀ v, aeval (compactCasimirOperator S) p (φ v) = 0 := by
  have hA : CompactDualDerivative S.compactRepresentation S.complexLieAction :=
    S.compactDualDerivative
  have hT : ∀ (ι : Type uF) [Fintype ι] [DecidableEq ι] (W : Submodule ℂ (ι → S.Space)),
      (∀ k, IsPiStable (S.compactRepresentation k) W) →
        IsPiStable (compactSquareOperator S.complexLieAction) W :=
    fun _ _ _ W hW => isPiStable_compactSquareOperator hA W hW
  obtain ⟨p, hp, h⟩ := exists_annihilator_of_piStable _ hT σ
  exact ⟨p, hp, fun φ hφ v =>
    (congrArg (fun T : Module.End ℂ S.Space => aeval T p (φ v))
      (compactCasimirOperator_eq S)).trans (h φ hφ v)⟩

end Realization

end Langlands.Automorphic.CuspidalAdmissible
