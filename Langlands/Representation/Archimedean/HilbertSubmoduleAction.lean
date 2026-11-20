import Langlands.Representation.Archimedean.SmoothVectors
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! # Restriction of bounded actions to invariant Hilbert subspaces -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Manifold

namespace Langlands.Archimedean

universe uA uG uE uV

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

section Restriction

variable {G : Type uG} [Monoid G] (π : G →* (E →L[ℂ] E)) (M : Submodule ℂ E)
  (hM : ∀ g (x : M), π g x ∈ M)

/-- The restricted bounded action on an invariant subspace. -/
def invariantSubmoduleRepresentation : G →* (M →L[ℂ] M) where
  toFun g := (π g).restrict (fun x hx => hM g ⟨x, hx⟩)
  map_one' := by
    ext x
    change π 1 x = (x : E)
    rw [map_one]
    rfl
  map_mul' g h := by
    ext x
    change π (g * h) x = π g (π h x)
    rw [map_mul]
    rfl

@[simp] theorem coe_invariantSubmoduleRepresentation (g : G) (x : M) :
    (invariantSubmoduleRepresentation π M hM g x : E) = π g x := rfl

theorem inner_invariantSubmoduleRepresentation
    (hπ : ∀ g x y, Inner.inner ℂ (π g x) (π g y) = Inner.inner ℂ x y)
    (g : G) (x y : M) :
    Inner.inner ℂ (invariantSubmoduleRepresentation π M hM g x)
        (invariantSubmoduleRepresentation π M hM g y) = Inner.inner ℂ x y :=
  hπ g x y

end Restriction

variable {G : Type uG} [Group G] [TopologicalSpace G]
  (π : G →* (E →L[ℂ] E)) (M : Submodule ℂ E) (hM : ∀ g (x : M), π g x ∈ M)

theorem isContinuousRepresentation_invariantSubmodule (hπ : IsContinuousRepresentation π) :
    IsContinuousRepresentation (invariantSubmoduleRepresentation π M hM) :=
  (hπ.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _

section Smooth

variable {A : Type uA} [NormedAddCommGroup A] [NormedSpace ℝ A] [ChartedSpace A G]

/-- Smooth ambient orbits valued in a closed subspace are smooth in that
subspace, by composing with the bounded orthogonal projection. -/
theorem isSmoothVector_invariantSubmodule [CompleteSpace M]
    (x : M) (hx : IsSmoothVector 𝓘(ℝ, A) π (x : E)) :
    IsSmoothVector 𝓘(ℝ, A) (invariantSubmoduleRepresentation π M hM) x := by
  let P : E →L[ℝ] M := M.orthogonalProjectionOnto.restrictScalars ℝ
  have he : orbitMap (invariantSubmoduleRepresentation π M hM) x = P ∘ orbitMap π (x : E) := by
    funext g
    apply Subtype.ext
    exact (Submodule.starProjection_eq_self_iff.mpr (hM g x)).symm
  change ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, M) ∞ (orbitMap (invariantSubmoduleRepresentation π M hM) x)
  rw [he]
  exact P.contDiff.contMDiff.comp hx

/-- The derivative of the restricted orbit agrees with the ambient derivative
under the inclusion of the invariant subspace. -/
theorem coe_lieDerivative_invariantSubmodule (X : A) (x : M)
    (hx : IsSmoothVector 𝓘(ℝ, A) (invariantSubmoduleRepresentation π M hM) x) :
    ((lieDerivative 𝓘(ℝ, A) (invariantSubmoduleRepresentation π M hM) X x : M) : E) =
      lieDerivative 𝓘(ℝ, A) π X (x : E) := by
  let L : M →L[ℝ] E := M.subtypeL.restrictScalars ℝ
  let f := orbitMap (invariantSubmoduleRepresentation π M hM) x
  have hf : MDifferentiableAt 𝓘(ℝ, A) 𝓘(ℝ, M) f 1 := hx.mdifferentiableAt (by simp)
  have hL : MDifferentiableAt 𝓘(ℝ, M) 𝓘(ℝ, E) L (f 1) :=
    L.differentiableAt.mdifferentiableAt
  change L (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, M) f 1 X) = mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) (L ∘ f) 1 X
  rw [mfderiv_comp 1 hL hf, ContinuousLinearMap.mfderiv_eq]
  rfl

end Smooth

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The original image inside its closed linear span. -/
def rangeClosureEmbedding (j : V →ₗ[ℂ] E) : V →ₗ[ℂ] (LinearMap.range j).topologicalClosure :=
  j.codRestrict _ (fun v => Submodule.le_topologicalClosure _ (LinearMap.mem_range_self j v))

@[simp] theorem coe_rangeClosureEmbedding (j : V →ₗ[ℂ] E) (v : V) :
    (rangeClosureEmbedding j v : E) = j v := rfl

theorem rangeClosureEmbedding_injective (j : V →ₗ[ℂ] E) (hj : Function.Injective j) :
    Function.Injective (rangeClosureEmbedding j) :=
  fun _ _ h => hj (congrArg Subtype.val h)

theorem rangeClosureEmbedding_denseRange (j : V →ₗ[ℂ] E) : DenseRange (rangeClosureEmbedding j) := by
  intro x
  rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  have he : Subtype.val '' Set.range (rangeClosureEmbedding j) = Set.range j :=
    (Set.range_comp _ _).symm
  rw [he]
  exact x.property

end Langlands.Archimedean
