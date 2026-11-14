import Langlands.GroupScheme.Reductive.FiniteKernelOfTorusRestriction
import Langlands.GroupScheme.Reductive.SplitIsogenyGraphReductive

/-! # Full-kernel finiteness of the second local-isogeny graph projection -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.RootDatumIsogenyRealization

variable {k : Type u} [Field k]
    {G G' : GroupScheme (Spec (CommRingCat.of k))}
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    {I : Type v} {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G'} {t : T ⟶ T'}
    {ν : I → cocharacterLattice T} {ν' : I → cocharacterLattice T'}
    {C : ∀ j, LocalIsogeny i i' t (ν j) (ν' j)}

namespace LocalIsogenyGraphEnvelope

variable (D : LocalIsogenyGraphEnvelope C)

/-- A connected reductive graph with maximal source graph torus has finite
full second-projection kernel whenever the prescribed torus map is finite. -/
theorem second_kernel_isFinite_of_maximal_torus
    [IsSeparated G'.X.hom] (hD : IsConnectedReductive D.group)
    (hmax : IsMaximalTorus D.torusLift) (hi' : IsClosedSubgroup i')
    [IsFinite (CommGroupScheme.groupHom t).hom.hom.left] :
    IsFinite (kernel D.second).X.hom :=
  kernel_isFinite_of_finite_torus_restriction hD D.second D.torusLift i' t
    hmax hi' D.torusLift_second

/-- The second projection is an actual isogeny under the established fpqc
geometry and maximal-torus hypotheses, with no smooth-kernel restriction. -/
theorem second_isIsogeny_of_maximal_torus
    [IsSeparated G'.X.hom] (hD : IsConnectedReductive D.group)
    (hmax : IsMaximalTorus D.torusLift) (hi' : IsClosedSubgroup i')
    [IsFinite (CommGroupScheme.groupHom t).hom.hom.left]
    (hflat : Flat D.second.hom.hom.left) (hsurj : Surjective D.second.hom.hom.left)
    (hqc : QuasiCompact D.second.hom.hom.left) : IsIsogeny D.second := by
  let : Flat D.second.hom.hom.left := hflat
  let : Surjective D.second.hom.hom.left := hsurj
  let : QuasiCompact D.second.hom.hom.left := hqc
  let : IsFinite (kernel D.second).X.hom :=
    D.second_kernel_isFinite_of_maximal_torus hD hmax hi'
  exact ⟨isFinite_of_finite_kernel D.second, hflat, hsurj⟩

end LocalIsogenyGraphEnvelope

/-- The original certified reductive graph, now with maximal source graph
torus and isogeny second projection. No first-projection isomorphism is assumed. -/
structure IsogenyProjectionGraphEnvelope
    {G G' : GroupScheme (Spec (CommRingCat.of k))}
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    {I : Type v} {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G'} {t : T ⟶ T'}
    {ν : I → cocharacterLattice T} {ν' : I → cocharacterLattice T'}
    (C : ∀ j, LocalIsogeny i i' t (ν j) (ν' j)) where
  reductiveGraph : ReductiveLocalIsogenyGraphEnvelope C
  torusMaximal : IsMaximalTorus reductiveGraph.projections.graph.torusLift
  secondIsogeny : IsIsogeny reductiveGraph.projections.graph.second

/-- Certify the second projection without changing the graph or its actual
maps, using finite maximal-torus restriction and the recorded fpqc geometry. -/
def isogenyProjectionGraphEnvelope
    [IsSeparated G'.X.hom] (E : ReductiveLocalIsogenyGraphEnvelope C)
    (hmax : IsMaximalTorus E.projections.graph.torusLift) (hi' : IsClosedSubgroup i')
    [IsFinite (CommGroupScheme.groupHom t).hom.hom.left] :
    IsogenyProjectionGraphEnvelope C :=
  ⟨E, hmax, E.projections.graph.second_isIsogeny_of_maximal_torus
    E.reductive hmax hi' E.projections.secondGeometry.1
    E.projections.secondGeometry.2.1 E.projections.secondGeometry.2.2.2⟩

end Langlands.GroupScheme.RootDatumIsogenyRealization
