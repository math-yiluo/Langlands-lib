import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold

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

/-- A common analytic refinement makes the change between two topological branches analytic. -/
theorem contMDiffAt_branch_transition
    (e : OpenPartialHomeomorph M Z) (e' : OpenPartialHomeomorph N Z)
    (f : M → Z) (g : N → Z)
    (he : EqOn f e e.source) (he' : EqOn g e' e'.source)
    (p : W → M) (q : W → N) (hcomm : ∀ w, f (p w) = g (q w))
    (w : W) (hw : p w ∈ e.source) (hw' : q w ∈ e'.source)
    (hp : IsLocalDiffeomorphAt L I r p w) (hq : ContMDiffAt L J r q w) :
    ContMDiffAt I J r (e'.symm ∘ e) (p w) := by
  have hs : hp.localInverse (p w) = w := hp.localInverse_left_inv hp.localInverse_mem_target
  have han : ContMDiffAt I J r (q ∘ hp.localInverse) (p w) :=
    (hs ▸ hq).comp (p w) hp.localInverse_contMDiffAt
  have hsource : ∀ᶠ y in 𝓝 (p w), q (hp.localInverse y) ∈ e'.source :=
    han.continuousAt.preimage_mem_nhds (by simpa [hs] using e'.open_source.mem_nhds hw')
  apply han.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hw, hsource,
    hp.localInverse_eventuallyEq_right] with y hy hy' hright
  have hpoint : e y = e' (q (hp.localInverse y)) := by
    calc
      e y = f y := (he hy).symm
      _ = f (p (hp.localInverse y)) := congrArg f hright.symm
      _ = g (q (hp.localInverse y)) := hcomm _
      _ = e' (q (hp.localInverse y)) := he' hy'
  change e'.symm (e y) = q (hp.localInverse y)
  rw [hpoint, e'.left_inv hy']

end Langlands.Geometry.Manifold
