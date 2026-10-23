import Langlands.Representation.CompactCoefficient.Classes
import Langlands.Representation.Compact.Definitions
import Mathlib.Topology.Algebra.Support

/-!
# Compact coefficients and compact averaged orbits

This proposition states Bernstein--Zelevinsky (1976), Lemma--Definition 2.40:
for a smooth complex representation of a locally profinite group, compact
smooth-dual coefficients are equivalent to compact support of every averaged
orbit. It supplies no proof.
-/

namespace Langlands

/-- For every smooth complex representation of a Hausdorff, locally compact,
totally disconnected topological group, all coefficients against smooth
algebraic-dual vectors have compact support if and only if, for every compact
open subgroup `K` and every vector `v`, the averaged orbit
`g ↦ e_K (ρ g v)` has compact support. The group and carrier universes are
independent; no admissibility, finite dimension, irreducibility, finite
generation, unimodularity, Haar measure or countability is assumed. -/
def CompactCoefficientAveragedOrbitStatement.{uG, uV} : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ),
    HasCompactSmoothDualCoefficients ρ ↔
      ∀ (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (v : V),
        HasCompactSupport (fun g : G => Compact.averageMap ρ hρ K hK (ρ g v))

end Langlands
