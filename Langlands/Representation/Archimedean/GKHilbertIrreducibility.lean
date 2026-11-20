import Langlands.Representation.Archimedean.GKModule
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! # Topological irreducibility from compact-finite recovery -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Manifold TensorProduct

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing
universe uA uG uK uV uE

variable {A : Type uA} [NormedAddCommGroup A] [NormedSpace ℝ A]
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace A G]
  {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (π : G →* (E →L[ℂ] E))

omit [TopologicalSpace G] in
/-- Orthogonal projection onto a closed invariant subspace commutes with the unitary action. -/
theorem starProjection_commutes_of_invariant (M : Submodule ℂ E) (hM : IsClosed (M : Set E))
    (hstable : ∀ g x, x ∈ M → π g x ∈ M)
    (hinner : ∀ g x y, Inner.inner ℂ (π g x) (π g y) = Inner.inner ℂ x y)
    (g : G) (x : E) :
    letI : CompleteSpace M := hM.completeSpace_coe
    M.starProjection (π g x) = π g (M.starProjection x) := by
  let : CompleteSpace M := hM.completeSpace_coe
  have hinv (y : E) : π g (π g⁻¹ y) = y := by
    change (π g * π g⁻¹) y = y
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (hstable g _ (M.starProjection_apply_mem x)) fun y hy => ?_
  rw [← hinv y, ← (π g).map_sub, hinner]
  exact Submodule.starProjection_inner_eq_zero x _ (hstable g⁻¹ y hy)

/-- A genuine orbit derivative stays in a closed invariant subspace whenever
its starting smooth vector is in that subspace. -/
theorem lieDerivative_mem_of_invariant (M : Submodule ℂ E) (hM : IsClosed (M : Set E))
    (hstable : ∀ g x, x ∈ M → π g x ∈ M)
    (X : A) {x : E} (hx : x ∈ M) (hs : IsSmoothVector 𝓘(ℝ, A) π x) :
    lieDerivative 𝓘(ℝ, A) π X x ∈ M := by
  let : CompleteSpace M := hM.completeSpace_coe
  let P : E →L[ℝ] E := M.starProjection.restrictScalars ℝ
  have he : P ∘ orbitMap π x = orbitMap π x := by
    funext g
    change M.starProjection (π g x) = π g x
    exact Submodule.starProjection_eq_self_iff.mpr (hstable g x hx)
  have hf : MDifferentiableAt 𝓘(ℝ, A) 𝓘(ℝ, E) (orbitMap π x) 1 :=
    hs.mdifferentiableAt (by simp)
  have hP : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) P (orbitMap π x 1) :=
    P.differentiableAt.mdifferentiableAt
  have hd := mfderiv_comp 1 hP hf
  rw [he, ContinuousLinearMap.mfderiv_eq] at hd
  have hX := congrArg (fun f : A →L[ℝ] E => f X) hd.symm
  change M.starProjection (lieDerivative 𝓘(ℝ, A) π X x) = _ at hX
  exact Submodule.starProjection_eq_self_iff.mp hX

/-- A unitary Hilbert representation with a dense irreducible compact-finite
carrier is topologically irreducible if the compact-finite vectors are recovered
from the carrier and its real Lie generators agree with genuine orbit derivatives. -/
def GKHilbertIrreducibilityStatement : Prop :=
  ∀ (A : Type uA) [NormedRing A] [NormedAlgebra ℝ A]
    (G : Type uG) [Group G] [TopologicalSpace G] [ChartedSpace A G]
    (K : Type uK) [Group K] (iK : K →* G)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (κ : Representation ℂ K V) (d : (ℂ ⊗[ℝ] A) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (E : Type uE) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (π : G →* (E →L[ℂ] E)) (j : V →ₗ[ℂ] E),
    IsIrreducibleGKModule κ d → Function.Injective j → DenseRange j →
    (∀ g x y, Inner.inner ℂ (π g x) (π g y) = Inner.inner ℂ x y) →
    (∀ k v, j (κ k v) = π (iK k) (j v)) →
    (∀ v, FiniteVectors.IsFiniteVector κ v) →
    (∀ x, FiniteVectors.IsFiniteVector (linearRepresentation (π.comp iK)) x →
      x ∈ LinearMap.range j) →
    (∀ v, IsSmoothVector 𝓘(ℝ, A) π (j v)) →
    (∀ X v, j (d (1 ⊗ₜ[ℝ] X) v) = lieDerivative 𝓘(ℝ, A) π X (j v)) →
    IsTopologicallyIrreducible π

theorem gkHilbertIrreducibility : GKHilbertIrreducibilityStatement.{uA,uG,uK,uV,uE} := by
  intro A _ _ G _ _ _ K _ iK V _ _ κ d E _ _ _ π j hirr hinj hd hinner hK hfin hrec hs hD
  let : Nontrivial V := hirr.1
  refine ⟨hinj.nontrivial, fun M hM hstable => ?_⟩
  let : CompleteSpace M := hM.completeSpace_coe
  let N : Submodule ℂ V := M.comap j
  have hNK (k : K) (v : V) (hv : v ∈ N) : κ k v ∈ N := by
    change j (κ k v) ∈ M
    rw [hK]
    exact hstable _ _ hv
  have hND (Y : ℂ ⊗[ℝ] A) (v : V) (hv : v ∈ N) : d Y v ∈ N := by
    change j (d.toLinearMap Y v) ∈ M
    induction Y using TensorProduct.inductionOn with
    | tmul c X =>
      have he : c ⊗ₜ[ℝ] X = c • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have hh : j (d.toLinearMap (1 ⊗ₜ[ℝ] X) v) ∈ M := by
        rw [show j (d.toLinearMap (1 ⊗ₜ[ℝ] X) v) = _ from hD X v]
        exact lieDerivative_mem_of_invariant π M hM hstable X hv (hs v)
      rw [he, map_smul, LinearMap.smul_apply, map_smul]
      exact M.smul_mem _ hh
    | add Y Z hY hZ =>
      rw [map_add, LinearMap.add_apply, map_add]
      exact M.add_mem hY hZ
  rcases hirr.2 N hNK hND with hN | hN
  · left
    let T : κ.IntertwiningMap (linearRepresentation (π.comp iK)) :=
      ⟨M.starProjection.toLinearMap.comp j, fun k => LinearMap.ext fun v => by
        change M.starProjection (j (κ k v)) = π (iK k) (M.starProjection (j v))
        rw [hK]
        exact starProjection_commutes_of_invariant π M hM hstable hinner (iK k) (j v)⟩
    have hz (v : V) : M.starProjection (j v) = 0 := by
      obtain ⟨w, hw⟩ := hrec (T v) ((hfin v).map T)
      change j w = M.starProjection (j v) at hw
      have hwN : w ∈ N := by
        change j w ∈ M
        rw [hw]
        exact M.starProjection_apply_mem _
      rw [hN, Submodule.mem_bot] at hwN
      rw [← hw, hwN, map_zero]
    have hzero (x : E) : M.starProjection x = 0 := by
      exact hd.induction_on x (isClosed_eq M.starProjection.continuous continuous_const) hz
    rw [Submodule.eq_bot_iff]
    intro x hx
    exact (Submodule.starProjection_eq_self_iff.mpr hx).symm.trans (hzero x)
  · right
    have hsub : Set.range j ⊆ M := by
      rintro _ ⟨v, rfl⟩
      have hv : v ∈ N := by rw [hN]; exact Submodule.mem_top
      exact hv
    have hc := closure_minimal hsub hM
    rw [hd.closure_range] at hc
    exact Submodule.eq_top_iff'.mpr fun x => hc (Set.mem_univ x)

end Langlands.Archimedean
