import Langlands.BaseChange.CyclicProductFieldCoordinates
import Langlands.TraceFormula.LocalIntegralProduct
import Langlands.Global.AdelicSpaceLocalFields

/-! # Actual cyclic coordinates for a finite-place local algebra -/

noncomputable section

namespace Langlands.TraceFormula

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Langlands.BaseChange Langlands.Global Langlands.Global.AdelicFunctoriality
open scoped NumberField FiniteExtension TensorProduct PlaceCompletion

universe u

variable (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] (v : Langlands.Global.FinitePlace K)

local notation "Kᵥ" => v.adicCompletion K
local notation "Eᵥ" => LocalBaseChangeAlgebra K L (Sum.inr v)
local notation "Places" => FinitePlacesAbove L v

local instance : Algebra Kᵥ Eᵥ := LocalBaseChangeAlgebra.algebra K L (.inr v)

local instance : IsModuleTopology Kᵥ Eᵥ := LocalBaseChangeAlgebra.isModuleTopology K L (.inr v)

omit [FiniteDimensional K L] in
private theorem completion_isModuleTopology (q : Places) :
    IsModuleTopology Kᵥ (q.1.adicCompletion L) := by
  let : NontriviallyNormedField Kᵥ := AdelicSpaceLocalFields.normedField (𝓞 K) K v
  let : FiniteDimensional Kᵥ (q.1.adicCompletion L) := FiniteExtension.local_finite v q.1
  let : ContinuousSMul Kᵥ (q.1.adicCompletion L) :=
    continuousSMul_of_algebraMap _ _ (FiniteExtension.continuous_completionMap v q.1)
  exact isModuleTopologyOfFiniteDimensional (𝕜 := Kᵥ) (E := q.1.adicCompletion L)

private theorem mem_adicCompletionIntegers_of_powers_mem_compact
    (q : Langlands.Global.FinitePlace L) (x : q.adicCompletion L)
    {C : Set (q.adicCompletion L)} (hC : IsCompact C) (hx : ∀ k : ℕ, x ^ k ∈ C) :
    x ∈ (q.adicCompletionIntegers L : Set (q.adicCompletion L)) := by
  let : NormedField (q.adicCompletion L) :=
    (AdelicSpaceLocalFields.normedField (𝓞 L) L q).toNormedField
  by_contra h
  have hnorm : 1 < ‖x‖ := by
    apply lt_of_not_ge
    intro hn
    apply h
    exact (AdelicSpaceLocalFields.mem_adicCompletionIntegers_iff (𝓞 L) L q x).mpr hn
  obtain ⟨b, hb⟩ := hC.bddAbove_image continuous_norm.continuousOn
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt b hnorm
  have hle : ‖x ^ k‖ ≤ b := hb ⟨x ^ k, hx k, rfl⟩
  rw [norm_pow] at hle
  exact (not_lt_of_ge hle) hk

private theorem integers_iff_in_product
    {q : Places} {m : ℕ} (c : Eᵥ ≃ₐ[Kᵥ] (Fin (m + 1) → q.1.adicCompletion L))
    (hc : Continuous c) (hc' : Continuous c.symm) (x : Eᵥ) :
    x ∈ localIntegers K L v ↔
      ∀ j, c x j ∈ (q.1.adicCompletionIntegers L : Set (q.1.adicCompletion L)) := by
  constructor
  · intro hx j
    apply mem_adicCompletionIntegers_of_powers_mem_compact L q.1 (c x j)
      ((isCompact_localIntegers K L v).image ((continuous_apply j).comp hc))
    intro k
    refine ⟨x ^ k, pow_mem hx k, ?_⟩
    change c (x ^ k) j = (c x j) ^ k
    rw [map_pow, Pi.pow_apply]
  · intro hx
    apply (mem_localIntegers_iff_finiteTensorCoordinates K L v x).mpr
    intro q'
    let a : (Fin (m + 1) → q.1.adicCompletion L) → q'.1.adicCompletion L :=
      fun y ↦ finiteTensorMap (L := L) v (c.symm y) q'
    let : ∀ q : Places, IsModuleTopology Kᵥ (q.1.adicCompletion L) :=
      completion_isModuleTopology K L v
    let f : Eᵥ →ₗ[Kᵥ] (q : Places) → q.1.adicCompletion L :=
      (finiteTensorMap (L := L) v).toLinearMap
    have htensor : Continuous f := IsModuleTopology.continuous_of_linearMap f
    have ha : Continuous a := (continuous_apply q').comp (htensor.comp hc')
    have hcompact : IsCompact (Set.pi Set.univ fun _ : Fin (m + 1) ↦
        (q.1.adicCompletionIntegers L : Set (q.1.adicCompletion L))) :=
      isCompact_univ_pi fun _ ↦ isCompact_adicCompletionIntegers L q.1
    apply mem_adicCompletionIntegers_of_powers_mem_compact L q'.1
      (finiteTensorMap (L := L) v x q') (hcompact.image ha)
    intro k
    refine ⟨c (x ^ k), Set.mem_pi.mpr fun j _ ↦ ?_, ?_⟩
    · rw [map_pow, Pi.pow_apply]
      exact pow_mem (hx j) k
    · let g : Eᵥ →ₐ[Kᵥ] (q : Places) → q.1.adicCompletion L := finiteTensorMap (L := L) v
      change g (c.symm (c (x ^ k))) q' = (g x q') ^ k
      rw [c.symm_apply_apply, map_pow, Pi.pow_apply]

/-- The completed tensor local algebra of a cyclic number-field extension has
coordinates in copies of a single actual completion of the extension. -/
theorem exists_localCyclicProductCoordinates
    (σ : L ≃ₐ[K] L) (l : ℕ) (hσ : IsCyclicAlgebra σ l) :
    ∃ (q : Places) (m d : ℕ) (τ : q.1.adicCompletion L ≃ₐ[Kᵥ] q.1.adicCompletion L)
      (c : Eᵥ ≃ₐ[Kᵥ] (Fin (m + 1) → q.1.adicCompletion L)),
      l = (m + 1) * d ∧ IsCyclicAlgebra τ d ∧ Continuous c ∧ Continuous c.symm ∧
      (∀ (x : Eᵥ) (j : Fin m),
        c (localGalois K L σ (.inr v) x) j.castSucc = c x j.succ) ∧
      (∀ x : Eᵥ, c (localGalois K L σ (.inr v) x) (Fin.last m) = τ (c x 0)) ∧
      ∀ x : Eᵥ, x ∈ localIntegers K L v ↔
        ∀ j, c x j ∈ (q.1.adicCompletionIntegers L : Set (q.1.adicCompletion L)) := by
  classical
  let c₀ : Eᵥ ≃ₐ[Kᵥ] (q : Places) → q.1.adicCompletion L :=
    AlgEquiv.ofBijective (finiteTensorMap (L := L) v)
    ((completedTensorComparison K L).1 v)
  let σᵥ : Eᵥ ≃ₐ[Kᵥ] Eᵥ := localGalois K L σ (.inr v)
  have hσᵥ : IsCyclicAlgebra σᵥ l := isCyclicAlgebra_localGalois K L σ l (.inr v) hσ
  obtain ⟨q, m, d, τ, c, hl, hτ, _, hshift, hwrap⟩ :=
    exists_cyclicProductFieldCoordinates hσᵥ c₀
  let : IsModuleTopology Kᵥ (q.1.adicCompletion L) := completion_isModuleTopology K L v q
  have hc : Continuous c := IsModuleTopology.continuous_of_linearMap c.toLinearMap
  have hc' : Continuous c.symm := IsModuleTopology.continuous_of_linearMap c.symm.toLinearMap
  exact ⟨q, m, d, τ, c, hl, hτ, hc, hc', hshift, hwrap, integers_iff_in_product K L v c hc hc'⟩

/-- Actual finite-place cyclic product coordinates with the factor integer rings. -/
def LocalCyclicProductCoordinatesStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (v : Langlands.Global.FinitePlace K)
    (σ : L ≃ₐ[K] L) (l : ℕ), IsCyclicAlgebra σ l →
      let E := LocalBaseChangeAlgebra K L (.inr v)
      ∃ (q : FinitePlacesAbove L v) (m d : ℕ)
        (τ : q.1.adicCompletion L ≃ₐ[v.adicCompletion K] q.1.adicCompletion L)
        (c : E ≃ₐ[v.adicCompletion K] (Fin (m + 1) → q.1.adicCompletion L)),
        l = (m + 1) * d ∧ IsCyclicAlgebra τ d ∧ Continuous c ∧ Continuous c.symm ∧
        (∀ (x : E) (j : Fin m), c (localGalois K L σ (.inr v) x) j.castSucc = c x j.succ) ∧
        (∀ x : E, c (localGalois K L σ (.inr v) x) (Fin.last m) = τ (c x 0)) ∧
        ∀ x : E, x ∈ localIntegers K L v ↔
          ∀ j, c x j ∈ (q.1.adicCompletionIntegers L : Set (q.1.adicCompletion L))

theorem localCyclicProductCoordinates : LocalCyclicProductCoordinatesStatement := by
  intro K L _ _ _ _ _ _ v σ l hσ
  exact exists_localCyclicProductCoordinates K L v σ l hσ

end Langlands.TraceFormula
