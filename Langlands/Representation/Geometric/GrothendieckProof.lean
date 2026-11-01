import Langlands.Representation.Geometric.GrothendieckStatement
import Langlands.Representation.Geometric.GeometricLemmaProof
import Langlands.Representation.Filtration.GrothendieckProof

/-! Evaluate the actual natural geometric-lemma filtration in exact K0. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear CategoryTheory

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The actual geometric lemma computes the exact finite-length class of
normalized Jacquet restriction after normalized induction. -/
theorem geometricLemmaGrothendieck :
    GeometricLemmaGrothendieckStatement.{uF, uV} F T := by
  let := T.topology
  intro n hn B C
  obtain ⟨S, R, hS, hR, m, e, hglue⟩ :=
    padicGeometricLemma.{uF, max uF uV} p F T n hn B C
  refine ⟨S, R, hS, hR, m, e, ?_⟩
  let J := T.normalizedParabolicInductionFunctor.{uF, max uF uV} B ⋙
    T.normalizedJacquetFunctor.{uF, max uF uV} C
  let P (i : Fin m) :=
    CuspidalSupport.geometricPieceSmoothFunctor.{uF, max uF uV}
      F T B C (e i).val (S (e i)) (R (e i))
      (hS (e i)).2.1 (hR (e i)).2.1
  have hg : IsGluedFrom (J ⋙ SmoothRep.toRep)
      (fun i => P i ⋙ SmoothRep.toRep) := by
    simpa only [J, P, CuspidalSupport.geometricPieceSmoothFunctor_toRep,
      jacquetInductionFunctor, Functor.assoc] using hglue
  intro A hA
  have hI := Parabolic.normalizedInductionK0_hasFiniteLength.{uF, uV} F T B A hA
  have hJ : (J.obj A).HasFiniteLength :=
    Parabolic.normalizedJacquetK0_hasFiniteLength.{uF, uV} F T C _ hI
  obtain ⟨hP, hclass⟩ := SmoothRep.filtrationGrothendieckStatement
    ℂ (C.Levi F.Carrier) _ J m P hg A hJ
  refine ⟨hP, ?_⟩
  rw [Parabolic.normalizedInductionK0_finiteLengthClass F T B A hA hI,
    Parabolic.normalizedJacquetK0_finiteLengthClass F T C _ hI hJ]
  exact hclass

end Langlands.Geometric
