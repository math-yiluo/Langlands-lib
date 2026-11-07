import Langlands.AbelianScheme.Tate.CommensurableInvariantLatticeRealizationStatement
import Langlands.AbelianScheme.Tate.CommensurableLatticeKernel
import Langlands.AlgebraicGeometry.FiniteEtale.InvariantSubgroupRealizationProof

/-! # Realization of commensurable invariant full Tate lattices -/

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u

namespace Langlands.AbelianScheme.Tate

open Langlands.AlgebraicGeometry.FiniteEtale GroupScheme.Tate

/-- Every commensurable invariant full Tate lattice is realized by an abelian scheme. -/
theorem commensurableInvariantLatticeRealization :
    CommensurableInvariantLatticeRealizationStatement.{u} := by
  intro htor h S _ _ hu Ω _ _ _ s hs A hfib L hL hbound
  obtain ⟨n, hn, hlower, hupper⟩ := hbound
  let N : Index (fun _ => True) := ⟨n, hn, trivial⟩
  let G : CommGroupScheme S :=
    { toGrp := GroupScheme.kernel (GroupScheme.multiplication A.toGrp ((n * n : ℕ) : ℤ)) }
  let : IsFinite G.X.hom := torsionKernel_isFinite htor A (n * n)
    (Nat.mul_pos hn hn) (hu (fullSquareIndex N))
  let : Etale G.X.hom := torsionKernel_etale htor A (n * n)
    (Nat.mul_pos hn hn) (hu (fullSquareIndex N))
  have hM := normalizedKernelSubgroup_monodromy s hs htor A hu N L.toAddSubgroup hL
  obtain ⟨H, i, hfin, het, hclosed, himage⟩ :=
    invariantSubgroupRealization S Ω s hs G
      (normalizedKernelSubgroup A.toGrp (Over.mk s) N L.toAddSubgroup) hM
  let : IsFinite H.X.hom := hfin
  let : Etale H.X.hom := het
  let : IsClosedImmersion (CommGroupScheme.hom i) := hclosed
  exact exists_realization_of_normalizedKernelSubgroup s A hfib N L.toAddSubgroup
    hlower hupper H (CommGroupScheme.groupHom i) himage

end Langlands.AbelianScheme.Tate
