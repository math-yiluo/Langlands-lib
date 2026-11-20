import Langlands.Representation.Archimedean.CompactHilbertAdmissibility
import Langlands.Representation.Archimedean.GKHilbertIrreducibility
import Langlands.Representation.Archimedean.HilbertSubmoduleAction

/-! # Hilbert realization on the invariant closure of a compact-finite module -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Manifold TensorProduct

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing
universe uA uG uK uV uE

/-- A unitary Hilbert realization with the specified compact-finite carrier,
its compact action and its genuine real generators. -/
def IsGKHilbertRealization {A : Type uA} [NormedRing A] [NormedAlgebra ℝ A]
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace A G]
    {K : Type uK} [Group K] [TopologicalSpace K] (iK : K →* G)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (κ : Representation ℂ K V) (d : (ℂ ⊗[ℝ] A) →ₗ⁅ℂ⁆ Module.End ℂ V)
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (π : G →* (E →L[ℂ] E)) (j : V →ₗ[ℂ] E) : Prop :=
  IsContinuousRepresentation π ∧ IsTopologicallyIrreducible π ∧
  (∀ g x y, Inner.inner ℂ (π g x) (π g y) = Inner.inner ℂ x y) ∧
  IsAdmissibleGKModule (linearRepresentation (π.comp iK)) ∧
  Function.Injective j ∧ DenseRange j ∧
  (∀ x, x ∈ LinearMap.range j ↔ FiniteVectors.IsFiniteVector (linearRepresentation (π.comp iK)) x) ∧
  (∀ k v, j (κ k v) = π (iK k) (j v)) ∧
  (∀ v, IsSmoothVector 𝓘(ℝ, A) π (j v)) ∧
  ∀ X v, j (d (1 ⊗ₜ[ℝ] X) v) = lieDerivative 𝓘(ℝ, A) π X (j v)

/-- The invariant closure of an irreducible admissible compact-finite carrier
with compatible smooth and unitary action data has the same compact-finite
carrier and is a topologically irreducible Hilbert realization. -/
def GKHilbertClosureStatement : Prop :=
  ∀ (A : Type uA) [NormedRing A] [NormedAlgebra ℝ A]
    (G : Type uG) [Group G] [TopologicalSpace G] [ChartedSpace A G]
    (K : Type uK) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
    (iK : K →* G) (_hiK : Continuous iK)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (κ : Representation ℂ K V) (d : (ℂ ⊗[ℝ] A) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (E : Type uE) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (π : G →* (E →L[ℂ] E)) (j : V →ₗ[ℂ] E)
    (hstable : ∀ g (x : (LinearMap.range j).topologicalClosure),
      π g x ∈ (LinearMap.range j).topologicalClosure),
    IsIrreducibleGKModule κ d → IsAdmissibleGKModule κ →
    (∀ v, FiniteVectors.IsFiniteVector κ v) → Function.Injective j →
    IsContinuousRepresentation π →
    (∀ g x y, Inner.inner ℂ (π g x) (π g y) = Inner.inner ℂ x y) →
    (∀ k v, j (κ k v) = π (iK k) (j v)) →
    (∀ v, IsSmoothVector 𝓘(ℝ, A) π (j v)) →
    (∀ X v, j (d (1 ⊗ₜ[ℝ] X) v) = lieDerivative 𝓘(ℝ, A) π X (j v)) →
    IsGKHilbertRealization iK κ d (invariantSubmoduleRepresentation π _ hstable)
      (rangeClosureEmbedding j)

theorem gkHilbertClosure : GKHilbertClosureStatement.{uA,uG,uK,uV,uE} := by
  intro A _ _ G _ _ _ K _ _ _ _ _ _ _ iK hiK V _ _ κ d E _ _ _ π j hstable
    hirr hadm hfin hinj hcont hinner hK hs hD
  let M := (LinearMap.range j).topologicalClosure
  let : CompleteSpace M := (LinearMap.range j).isClosed_topologicalClosure.completeSpace_coe
  let R := invariantSubmoduleRepresentation π M hstable
  let J := rangeClosureEmbedding j
  change IsGKHilbertRealization iK κ d R J
  have hR : IsContinuousRepresentation R :=
    isContinuousRepresentation_invariantSubmodule π M hstable hcont
  have hRU (g : G) (x y : M) : Inner.inner ℂ (R g x) (R g y) = Inner.inner ℂ x y :=
    inner_invariantSubmoduleRepresentation π M hstable hinner g x y
  have hRcontK : IsContinuousRepresentation (R.comp iK) :=
    hR.comp ((hiK.comp continuous_fst).prodMk continuous_snd)
  have hRnormK (k : K) (x : M) : ‖(R.comp iK) k x‖ = ‖x‖ := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ) ((R.comp iK) k x),
      norm_eq_sqrt_re_inner (𝕜 := ℂ) x]
    exact congrArg (fun z : ℂ => Real.sqrt z.re) (hRU (iK k) x x)
  have hJK (k : K) (v : V) : J (κ k v) = (R.comp iK) k (J v) := Subtype.ext (hK k v)
  have hJinj : Function.Injective J := rangeClosureEmbedding_injective j hinj
  have hJdense : DenseRange J := rangeClosureEmbedding_denseRange j
  have hJs (v : V) : IsSmoothVector 𝓘(ℝ, A) R (J v) :=
    isSmoothVector_invariantSubmodule π M hstable (J v) (hs v)
  have hJD (X : A) (v : V) : J (d (1 ⊗ₜ[ℝ] X) v) = lieDerivative 𝓘(ℝ, A) R X (J v) := by
    apply Subtype.ext
    exact (hD X v).trans (coe_lieDerivative_invariantSubmodule π M hstable X (J v) (hJs v)).symm
  obtain ⟨hRAdm, hrec⟩ := compactHilbertAdmissibility κ (R.comp iK) J hJK hJinj hJdense
    hfin hadm hRcontK hRnormK
  have hRI := gkHilbertIrreducibility A G K iK V κ d M R J hirr hJinj hJdense hRU hJK hfin
    (fun x => (hrec x).mpr) hJs hJD
  exact ⟨hR, hRI, hRU, hRAdm, hJinj, hJdense, hrec, hJK, hJs, hJD⟩

end Langlands.Archimedean
