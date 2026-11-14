import Langlands.GroupScheme.Rational.QuasiSplitSplittingReduction

/-! # Nonempty relative roots before quasi-split splitting -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

/-- A maximal split torus of a quasi-split absolutely almost-simple group
has an actual relative root, without a splitting or absolute-maximality premise. -/
theorem IsQuasiSplit.relativeRoots_nonempty_of_isAbsolutelyAlmostSimple
    {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsQuasiSplit G) (habs : IsAbsolutelyAlmostSimple G)
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : S.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) :
    haveI := hG.isConnectedReductive.isAffineHom
    (relativeRoots i).Nonempty := by
  let : IsAffineHom G.X.hom := hG.isConnectedReductive.isAffineHom
  let : Smooth G.X.hom := hG.isConnectedReductive.smooth
  obtain ⟨T, j, hj, f, hf⟩ :=
    exists_maximalTorus_extension_of_finiteType G i hi.1.1.isTorus hi.1.2
  obtain ⟨L, hL, hA, hfin, hgal, hTL⟩ := torusFiniteGaloisSplitting k T.toGrp hj.1
  let := hL
  let := hA
  let := hfin
  let := hgal
  let b := algebraBaseMap k L
  let T_L := (CommGroupScheme.baseChange b).obj T
  let G_L := (GroupScheme.baseChange b).obj G
  let j_L := (GroupScheme.baseChange b).map j
  have hGL : IsAlmostSimple G_L :=
    (habs.baseChange_of_algebraicExtension (K := L)).1
  let : IsAffineHom G_L.X.hom := hGL.isSemisimple.isConnectedReductive.isAffineHom
  have hjL : IsMaximalTorus (T := T_L) (G := G_L) j_L :=
    (maximalTorusBaseChange k L G T j hj.1 hj.2.1).mp hj
  obtain ⟨β, hβ⟩ := hGL.relativeRoots_nonempty_of_split_maximalTorus (T := T_L) j_L hTL hjL
  let α := hG.rootRestriction (L := L) i j (Additive.ofMul f) hi hj hf hTL ⟨β, hβ⟩
  exact ⟨α.val, α.property⟩

/-- Choose an actual relative root of a maximal split torus in a quasi-split
absolutely almost-simple group, without assuming splitting. -/
def IsQuasiSplit.relativeRootOfIsAbsolutelyAlmostSimple
    {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsQuasiSplit G) (habs : IsAbsolutelyAlmostSimple G)
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : S.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) :
    haveI := hG.isConnectedReductive.isAffineHom
    relativeRoots i := by
  let : IsAffineHom G.X.hom := hG.isConnectedReductive.isAffineHom
  let h := hG.relativeRoots_nonempty_of_isAbsolutelyAlmostSimple habs i hi
  exact ⟨h.choose, h.choose_spec⟩

end Langlands.GroupScheme
