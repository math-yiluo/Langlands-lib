import Langlands.GroupScheme.SimplyConnected.TypeCDivisionFormStatement
import Langlands.GroupScheme.SimplyConnected.TypeCRankOneQuaternionicStatement

/-! # Extracting the quaternionic rank-one model from type-C classification -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The general division-form classification supplies the exact rank-one
quaternionic identification. The classification remains an explicit premise. -/
theorem typeCRankOneQuaternionic_of_typeCDivisionForm
    (hclass : TypeCDivisionFormStatement.{u}) :
    TypeCRankOneQuaternionicStatement.{u} := by
  intro K _ G _ _ d n hsc haas hindex hrank
  rcases hindex with ⟨hn, ⟨e, hcartan, hmarked⟩, _⟩
  have hn2 : 2 ≤ n := by omega
  obtain ⟨degree, m, hm, D, hD, hKD, hcentral, hfinite,
    hdegree, hsize, hdim, σ, hsym, H, hanti, hunit, hwitt, hiso, hvertices⟩ :=
    hclass K G d n e hn2 hsc haas hcartan
  let a : d.Vertex := e.symm ⟨1, by omega⟩
  have ha : a ∈ d.distinguishedVertices := (hmarked a).2 (by simp [a])
  obtain ⟨j, hjpos, hjrank, hjdegree⟩ := (hvertices a).1 ha
  have hjrank_nat : j ≤ 1 := by simpa [hrank] using hjrank
  have hj : j = 1 := by omega
  have hdegree2 : degree = 2 := by simpa [a, hj] using hjdegree.symm
  subst degree
  have hm_eq : m = n := by omega
  subst m
  refine ⟨D, hD, hKD, hcentral, hfinite, ?_, σ, ?_, hm, H,
    hanti, hunit, ?_, hiso⟩
  · simpa using hdim
  · simpa using hsym
  · exact_mod_cast hwitt.trans hrank

end Langlands.GroupScheme
