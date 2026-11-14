import Langlands.GroupScheme.Rational.SplitTorusCentralizerReduction
import Langlands.GroupScheme.Dynamic.NestedDecomposition

/-! # Generic centralizers in smooth connected affine groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

/-- The canonical identity-on-ambient-points equivalence between the generic
cocharacter centralizer and the full split-torus centralizer. -/
def genericCentralizerPointsEquiv
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (V : Over (Spec (CommRingCat.of k))) :
    (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).carrier V ≃*
      (torusCentralizer i).carrier V :=
  MulEquiv.subgroupCongr (congrArg (fun H : SubgroupFunctor G => H.carrier V)
    (hT.dynamicCentralizer_eq_torusCentralizer i ν hν))

omit [Smooth G.X.hom] [ConnectedSpace G.X.left] in
/-- Centralizer and positive dynamic containment imply full dynamic parabolic
containment, on every scheme test. -/
theorem Dynamic.parabolic_le_of_centralizer_le_of_unipotent_le
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (H : SubgroupFunctor G)
    (hZ : Dynamic.centralizer χ ≤ H) (hU : Dynamic.unipotent χ ≤ H) :
    Dynamic.parabolic χ ≤ H := by
  intro V g hg
  obtain ⟨z, hz, n, hn, rfl⟩ := Dynamic.exists_centralizer_mul_unipotent χ hg
  exact (H.carrier V).mul_mem (hZ V hz) (hU V hn)

/-- For an adjoint-generic cocharacter of a split torus, full torus-centralizer
and positive dynamic containment imply dynamic parabolic containment. -/
theorem parabolic_le_of_torusCentralizer_le_of_unipotent_le
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (H : SubgroupFunctor G) (hZ : torusCentralizer i ≤ H)
    (hU : Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i) ≤ H) :
    Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤ H := by
  apply Dynamic.parabolic_le_of_centralizer_le_of_unipotent_le _ H
  · rwa [hT.dynamicCentralizer_eq_torusCentralizer i ν hν]
  · exact hU

end Langlands.GroupScheme
