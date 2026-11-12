import Mathlib.Geometry.Manifold.LocalDiffeomorph

noncomputable section

open Set Filter Topology
open scoped Manifold

namespace Langlands.Geometry.Manifold

variable {k : Type*} [NontriviallyNormedField k]
variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace k E]
  [NormedAddCommGroup F] [NormedSpace k F]
  [NormedAddCommGroup G] [NormedSpace k G]
variable {H H' H'' : Type*}
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
variable {I : ModelWithCorners k E H} {J : ModelWithCorners k F H'}
  {L : ModelWithCorners k G H''}
variable {M N W Z : Type*}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N]
  [TopologicalSpace W] [ChartedSpace H'' W]
  [TopologicalSpace Z]
variable {r : WithTop ℕ∞}

/-- Analyticity of a map lifted through a topological branch descends through a local
diffeomorphism on its source. -/
theorem contMDiffAt_branch_lift
    (e : OpenPartialHomeomorph N Z) (f : M → Z) (g : N → Z)
    (he : EqOn g e e.source) (p : W → M) (q : W → N)
    (hcomm : ∀ w, f (p w) = g (q w)) (w : W) (hw : q w ∈ e.source)
    (hp : IsLocalDiffeomorphAt L I r p w) (hq : ContMDiffAt L J r q w) :
    ContMDiffAt I J r (e.symm ∘ f) (p w) := by
  have hs : hp.localInverse (p w) = w := hp.localInverse_left_inv hp.localInverse_mem_target
  have han : ContMDiffAt I J r (q ∘ hp.localInverse) (p w) :=
    (hs ▸ hq).comp (p w) hp.localInverse_contMDiffAt
  have hsource : ∀ᶠ y in 𝓝 (p w), q (hp.localInverse y) ∈ e.source :=
    han.continuousAt.preimage_mem_nhds (by simpa [hs] using e.open_source.mem_nhds hw)
  apply han.congr_of_eventuallyEq
  filter_upwards [hsource, hp.localInverse_eventuallyEq_right] with y hy hright
  have hpoint : f y = e (q (hp.localInverse y)) := by
    calc
      f y = f (p (hp.localInverse y)) := congrArg f hright.symm
      _ = g (q (hp.localInverse y)) := hcomm _
      _ = e (q (hp.localInverse y)) := he hy
  change e.symm (f y) = q (hp.localInverse y)
  rw [hpoint, e.left_inv hy]

/-- Analyticity descends through a local analytic diffeomorphism. -/
theorem contMDiffAt_of_comp_localDiffeomorph
    (p : W → M) (f : M → N) (w : W)
    (hp : IsLocalDiffeomorphAt L I r p w) (hf : ContMDiffAt L J r (f ∘ p) w) :
    ContMDiffAt I J r f (p w) := by
  have hs : hp.localInverse (p w) = w := hp.localInverse_left_inv hp.localInverse_mem_target
  have han : ContMDiffAt I J r ((f ∘ p) ∘ hp.localInverse) (p w) :=
    (hs ▸ hf).comp (p w) hp.localInverse_contMDiffAt
  apply han.congr_of_eventuallyEq
  filter_upwards [hp.localInverse_eventuallyEq_right] with y hy
  exact (congrArg f hy).symm

/-- Local analytic invertibility descends through a local analytic diffeomorphism. -/
theorem isLocalDiffeomorphAt_of_comp
    (p : W → M) (f : M → N) (w : W)
    (hp : IsLocalDiffeomorphAt L I r p w)
    (hf : IsLocalDiffeomorphAt L J r (f ∘ p) w) :
    IsLocalDiffeomorphAt I J r f (p w) := by
  obtain ⟨D, hw, hD⟩ := hf
  refine ⟨hp.localInverse.trans D, ?_, ?_⟩
  · refine ⟨hp.localInverse_mem_source, ?_⟩
    change hp.localInverse (p w) ∈ D.source
    rw [hp.localInverse_left_inv hp.localInverse_mem_target]
    exact hw
  · intro y hy
    change f y = D (hp.localInverse y)
    calc
      f y = f (p (hp.localInverse y)) := congrArg f (hp.localInverse_right_inv hy.1).symm
      _ = D (hp.localInverse y) := hD hy.2

end Langlands.Geometry.Manifold
