import Langlands.GroupScheme.Rational.SplitReductiveDimensionStatement
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Reductive.IsogenyRootIndex
import Langlands.GroupScheme.HomogeneousQuotientDimension
import Langlands.GroupScheme.ReducedBaseSmooth.DimensionBridge

/-! # The dimension of a split reductive group -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

private theorem topologicalKrullDim_eq_lieDimension
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left] :
    topologicalKrullDim G.X.left =
      (Module.finrank k (Additive (lieKernel G k)) : WithBot ℕ∞) := by
  obtain ⟨n, hn⟩ := Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension
    G.X.left (Spec (CommRingCat.of k)) G.X.hom inferInstance inferInstance
  let : SmoothOfRelativeDimension n G.X.hom := hn
  have hd := Lie.dimension_eq_of_smoothOfRelativeDimension G hn
  rw [ReducedBaseSmooth.topologicalKrullDim_eq_of_smoothOfRelativeDimension
    k G.X.left G.X.hom n]
  exact_mod_cast hd.symm

/-- The dimension of a connected reductive group with a split maximal torus
is the dimension of that torus plus the number of its roots (Milne 21.13). -/
theorem splitReductiveDimension : SplitReductiveDimensionStatement.{u} := by
  intro k _ G hG
  let : IsAffineHom G.X.hom := hG.isAffineHom
  intro T t ht hmax
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let : IsAffineHom T.toGrp.X.hom := ht.1.isAffineHom
  let : Smooth T.toGrp.X.hom := ht.1.smooth
  let : ConnectedSpace T.toGrp.X.left := ht.1.connectedSpace
  obtain ⟨J, hJ, P, hP, _⟩ := rootDatumExistence k G hG T ht.1 t hmax
  let : Finite J := hJ
  have hcount : (relativeRoots t).ncard = Nat.card J := by
    rw [relativeRoots_eq_roots, ← hP.2.1]
    exact Set.ncard_range_of_injective P.root.injective
  rw [topologicalKrullDim_eq_lieDimension G,
    topologicalKrullDim_eq_lieDimension T.toGrp, hcount]
  exact_mod_cast hP.finrank_lie_eq_torus_add_card hG ht.1 hmax

end Langlands.GroupScheme
