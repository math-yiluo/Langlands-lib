import Langlands.Shimura.Coefficients.Lattice
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Compact orbit saturation of an open lattice -/

namespace Langlands.Shimura.Coefficients

universe u v w z

/-- The orbit span of an open full lattice under a compact group with continuous
orbit maps is itself an open full stable lattice. -/
def CompactLatticeStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type v) [CommRing K] [Algebra R K]
    (V : Type w) [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    [TopologicalSpace V] [IsTopologicalAddGroup V]
    (G : Type z) [Group G] [TopologicalSpace G] [CompactSpace G]
    (ρ : G →* (V ≃ₗ[K] V)),
    (∀ x : V, Continuous (fun g : G => ρ g x)) →
    ∀ (Λ : Submodule R V) [Submodule.IsLattice K Λ], IsOpen (Λ : Set V) →
      Submodule.IsLattice K (orbitSpan ρ Λ) ∧
      IsStable ρ (orbitSpan ρ Λ) ∧ IsOpen (orbitSpan ρ Λ : Set V)

/-- A continuous action on a finite module has open congruence kernels when
the reduction submodules are open. For a compact topological group the resulting
quotient group is finite. -/
def CongruenceKernelTopologyStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (G : Type z) [Group G] [TopologicalSpace G]
    [SeparatelyContinuousMul G] [CompactSpace G]
    (M : Action (ModuleCat.{w} R) G) [Module.Finite R M.V]
    [TopologicalSpace M.V] [IsTopologicalAddGroup M.V],
    (∀ x : M.V, Continuous (fun g : G => (M.ρ g).hom x)) →
    ∀ (I : Ideal R) (n : ℕ), IsOpen ((I ^ n • ⊤ : Submodule R M.V) : Set M.V) →
      IsOpen (congruenceKernel I M n : Set G) ∧ Finite (G ⧸ congruenceKernel I M n)

/-- The two topological prerequisites for stable integral coefficient actions
and their finite congruence quotients. -/
def LatticeTopologyStatement : Prop :=
  CompactLatticeStatement.{u,v,w,z} ∧ CongruenceKernelTopologyStatement.{u,z,w}

end Langlands.Shimura.Coefficients
