import Langlands.AlgebraicGeometry.FiniteEtaleChartDescentStatement
import Langlands.AlgebraicGeometry.ChartAlgebraDescent

/-! # Finite étale chart descent: exact statement adapter -/

universe u
open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Exact functorial chart descent, via the actual invariant-algebra construction. -/
theorem finiteEtaleChartDescent : FiniteEtaleChartDescentStatement.{u} := by
  intro A B C _ _ _ _ _ _ _ _ _ hs θ hid hcyc hnat
  let D : ChartAlgebraDescent.Datum A B C := {
    equiv := θ
    identity := hid
    cocycle := hcyc
    naturality := hnat }
  have hφ : (algebraMap A B).FaithfullyFlat :=
    RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mpr
      ⟨RingHom.flat_algebraMap_iff.mpr inferInstance, hs.surj⟩
  let P := D.descend hφ (RingHom.finite_algebraMap.mpr inferInstance)
    (RingHom.etale_algebraMap.mpr inferInstance)
  exact ⟨P.ring, P.commRing, P.algebra, P.finite, P.projective, P.etale, P.equiv, P.invariant⟩

end Langlands.AlgebraicGeometry
