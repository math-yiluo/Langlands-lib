import Langlands.Representation.Aubert.General.LocalFieldMatrixGeometricGrothendieckStatement
import Langlands.Representation.Aubert.General.LocalFieldMatrixParabolicPreservationProof
import Langlands.AllField.Representation.Geometric.GeometricLemmaProof
import Langlands.Representation.Filtration.GrothendieckProof

/-! The natural geometric filtration computes the actual class sum. -/

noncomputable section

namespace Langlands.Aubert.General.RationalPointFamily.GL

open GeneralLinear Geometric _root_.CategoryTheory

universe u v

/-- The all-field geometric lemma evaluated on actual smooth exact classes. -/
theorem localFieldMatrixGeometricGrothendieck :
    LocalFieldMatrixGeometricGrothendieckStatement.{u, v} := by
  intro F _ T n hn B C
  let := T.topology
  obtain ⟨S, R, hS, hR, m, e, hglue⟩ :=
    AllField.Geometric.padicGeometricLemma.{u, max (u + 1) v} F T n hn B C
  refine ⟨S, R, hS, hR, m, e, ?_⟩
  let J := T.normalizedParabolicInductionFunctor.{u, max (u + 1) v} B ⋙
    T.normalizedJacquetFunctor.{u, max (u + 1) v} C
  let P (i : Fin m) := AllField.CuspidalSupport.geometricPieceSmoothFunctor.{u, max (u + 1) v}
    F T B C (e i).val (S (e i)) (R (e i)) (hS (e i)).2.1 (hR (e i)).2.1
  have hg : IsGluedFrom (J ⋙ SmoothRep.toRep) (fun i => P i ⋙ SmoothRep.toRep) := by
    simpa only [J, P, AllField.CuspidalSupport.geometricPieceSmoothFunctor_toRep,
      AllField.Geometric.jacquetInductionFunctor, Functor.assoc] using hglue
  intro A hA
  let w := localFieldMatrixParabolicPreservation.{u, v} F T n
  have hI := (w B).1 A hA
  have hJ : (J.obj A).HasFiniteLength := (w C).2.2.1 _ hI
  obtain ⟨hP, hclass⟩ := SmoothRep.filtrationGrothendieckStatement ℂ (C.Levi F) _ J m P hg A hJ
  exact ⟨hJ, hP, hclass⟩

end Langlands.Aubert.General.RationalPointFamily.GL
