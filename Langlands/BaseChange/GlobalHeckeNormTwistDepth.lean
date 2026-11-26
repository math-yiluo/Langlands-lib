import Langlands.BaseChange.CommonNormTwistAuxiliaryFactors
import Langlands.BaseChange.DeepNormTwistConductors
import Langlands.Global.Arithmetic.RamifiedTwistIsolationProof
import Langlands.LocalFactor.BrauerKernel.PlaceRamification

/-! # A global Hecke twist meeting prescribed local conductor bounds -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.BaseChange

open Correspondence Global Global.AdelicFunctoriality Global.CompletionPadic
open HarmonicAnalysis LocalClassField
open scoped BigOperators NumberField FiniteExtension

universe u uI

private theorem conductor_quasicharacterAt_eq {K : Type u} [Field K] [NumberField K]
    (v : FinitePlace K) {p : ℕ} [Fact p.Prime] (h : residuePrime v = p)
    (χ : (v.adicCompletion K)ˣ →ₜ* ℂˣ) :
    (padicFieldAt v h).canonicalTopologicalData.multiplicativeConductor (quasicharacterAt v h χ) =
      (padicField v).canonicalTopologicalData.multiplicativeConductor (quasicharacterBase v χ) := by
  subst p
  rfl

/-- A finite-order Hecke character can be trivial at the distinguished finite
place while meeting all prescribed lower and upper conductor bounds on a
finite auxiliary set. The upper twist is its idelic norm pullback. -/
def GlobalHeckeNormTwistDepthStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (I : Type uI) [Fintype I] (χ : I → HeckeCharacter K)
    (v₀ : FinitePlace K) (S : Finset (FinitePlace K)), v₀ ∉ S →
    (∀ v ∈ S, ∀ (w : FinitePlacesAbove L v) (κ : (v.adicCompletion K)ˣ →* ℂˣ),
      IsNormTrivial (w.1.adicCompletion L) κ ↔ ∃ i, ((χ i).finiteComponent v).toMonoidHom = κ) →
    ∀ (B₁ : FinitePlace K → ℕ) (B₂ : FinitePlace L → ℕ),
    ∃ ν : HeckeCharacter K, ν.HasFiniteOrder ∧ ν.finiteComponent v₀ = 1 ∧
      (∀ w : FinitePlacesAbove L v₀, (ν.normComp (L := L)).finiteComponent w.1 = 1) ∧
      ∀ v ∈ S,
        (letI := (padicField v).canonicalTopologicalData.topology
         ∀ i, B₁ v ≤ (padicField v).canonicalTopologicalData.multiplicativeConductor
           (quasicharacterBase v ((χ i).finiteComponent v) * quasicharacterBase v (ν.finiteComponent v))) ∧
        ∀ w : FinitePlacesAbove L v, B₂ w.1 ≤ (padicField w.1).canonicalTopologicalData.multiplicativeConductor
          (quasicharacterBase w.1 ((ν.normComp (L := L)).finiteComponent w.1))

set_option maxHeartbeats 2050000 in
/-- Bound the lower conductor at each auxiliary place using a common bound
over its upper places, then apply finite character prescription. -/
theorem globalHeckeNormTwistDepth : GlobalHeckeNormTwistDepthStatement.{u, uI} := by
  classical
  intro K L _ _ _ _ _ _ _ I _ χ v₀ S hS hres B₁ B₂
  have hlocal (v : S) (w : FinitePlacesAbove L v.1) : ∃ N : ℕ, ∀ ν : HeckeCharacter K,
      N < (padicField v.1).canonicalTopologicalData.multiplicativeConductor
        (quasicharacterBase v.1 (ν.finiteComponent v.1)) →
      (letI := (padicField v.1).canonicalTopologicalData.topology
       ∀ i, B₁ v.1 ≤ (padicField v.1).canonicalTopologicalData.multiplicativeConductor
         (quasicharacterBase v.1 ((χ i).finiteComponent v.1) * quasicharacterBase v.1 (ν.finiteComponent v.1))) ∧
      B₂ w.1 ≤ (padicField w.1).canonicalTopologicalData.multiplicativeConductor
        (quasicharacterBase w.1 ((ν.normComp (L := L)).finiteComponent w.1)) := by
    let p := v.1
    let F := padicField p
    let E := CompletionPadic.towerPadicField p w.1
    have hscalar := towerPadicField_isScalarTower p w.1
    obtain ⟨_, hgal, hf, d, hd⟩ := completionRelativeFieldInvariants K L p w.1
    let := hscalar
    let := hgal
    let raw (i : I) := ((χ i).finiteComponent p).toMonoidHom
    let A := Finset.univ.image raw
    have hA (κ : F.Carrierˣ →* ℂˣ) : κ ∈ A ↔ IsNormTrivial E.Carrier κ := by
      rw [hres p v.2 w κ]
      simp [A, raw]
    obtain ⟨N, hN⟩ := deepNormTwistConductors (residuePrime p) F E
      F.canonicalTopologicalData E.canonicalTopologicalData (w.1.asIdeal.inertiaDeg (𝓞 K)) d hf hd A hA
      I (fun i => quasicharacterBase p ((χ i).finiteComponent p)) (B₁ p) (B₂ w.1)
    refine ⟨N, fun ν hν => ?_⟩
    obtain ⟨h₁, h₂, -⟩ := hN (quasicharacterBase p (ν.finiteComponent p)) hν
    rw [← quasicharacterAt_normComp p w ν, conductor_quasicharacterAt_eq] at h₂
    exact ⟨fun i => (h₁ i).1, h₂⟩
  choose N hN using hlocal
  let depth (v : S) : ℕ := ∑ w : FinitePlacesAbove L v.1, N v w
  have hvS : Disjoint ({v₀} : Finset (FinitePlace K)) S := Finset.disjoint_singleton_left.mpr hS
  obtain ⟨ν, hfinite, ht, -, hdepth⟩ := ramifiedTwistIsolation K {v₀} S hvS
    (fun v => (1 : (v.1.adicCompletion K)ˣ →ₜ* ℂˣ)) depth
    (fun _ => ⟨1, Nat.zero_lt_one, by simp⟩)
  have h₀ : ν.finiteComponent v₀ = 1 := ht ⟨v₀, Finset.mem_singleton_self _⟩
  refine ⟨ν, hfinite, h₀, fun w => ?_, ?_⟩
  · apply ContinuousMonoidHom.ext
    intro x
    rw [ν.normComp_finiteComponent v₀ w x, h₀]
    rfl
  · intro v hv
    let v' : S := ⟨v, hv⟩
    have hcond : depth v' < (padicField v).canonicalTopologicalData.multiplicativeConductor
        (quasicharacterBase v (ν.finiteComponent v)) :=
      LocalFactor.NonabelianBrauer.lt_multiplicativeConductor_of_nontrivialOnPrincipalUnits
        v (ν.finiteComponent v) (depth v') (hdepth v') rfl
    have hχ (w : FinitePlacesAbove L v) : N v' w <
        (padicField v).canonicalTopologicalData.multiplicativeConductor
          (quasicharacterBase v (ν.finiteComponent v)) :=
      (Finset.single_le_sum (f := N v') (fun _ _ => Nat.zero_le _) (Finset.mem_univ w)).trans_lt hcond
    let w₀ := placeAbove L v
    exact ⟨(hN v' w₀ ν (hχ w₀)).1, fun w => (hN v' w ν (hχ w)).2⟩

end Langlands.BaseChange
