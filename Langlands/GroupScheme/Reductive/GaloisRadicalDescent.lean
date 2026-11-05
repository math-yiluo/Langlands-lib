import Langlands.AlgebraicGeometry.PointTopology.AffineScheme
import Langlands.GroupScheme.Descent.RadicalIdealSheaf
import Langlands.GroupScheme.Reductive.RadicalOverlapDescent

/-! # Radical descent and pseudo-reductive ascent over Galois extensions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

open Descent

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {U : GroupScheme (Spec (CommRingCat.of K))}
    {i : U ⟶ (GroupScheme.baseChange (algebraBaseMap k K)).obj G}

/-- Every represented radical over a Galois extension descends with its actual
inclusion and a recovering source isomorphism. -/
def IsUnipotentRadical.galoisRadicalDescent [IsGalois k K]
    (hi : IsUnipotentRadical i) : UnipotentRadicalDescent i := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let A := Langlands.AlgebraicGeometry.PointTopology.AffineCoordinateRing k G.X
  let e : (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A)) ≅ G.X :=
    (Langlands.AlgebraicGeometry.PointTopology.affineSchemeOverIso k G.X).symm
  exact hi.descentOfOverlapRangeEq (RadicalTensorIdeal.overlap_range_eq e hi)

omit [IsAffineHom G.X.hom] in
/-- Pseudo-reductivity is preserved by any Galois field extension. -/
theorem IsPseudoReductive.baseChange_galois [IsGalois k K]
    (hG : IsPseudoReductive G) :
    IsPseudoReductive ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) := by
  let b := algebraBaseMap k K
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let : Smooth ((GroupScheme.baseChange b).obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom b)
    infer_instance
  let : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  let : ConnectedSpace ((GroupScheme.baseChange b).obj G).X.left :=
    G.connectedSpace_baseChange_of_smooth_affine b
  obtain ⟨U, i, hi⟩ := unipotentRadicalExistence K ((GroupScheme.baseChange b).obj G)
  let d := hi.galoisRadicalDescent
  exact ⟨inferInstance, inferInstance, inferInstance,
    hi.hasTrivialUnipotentRadical_iff.mpr
      (SubgroupFunctor.range_eq_bot_of_radical_descent hG.hasTrivialUnipotentRadical
        d.isRadical d.comparison d.recovers)⟩

end Langlands.GroupScheme
