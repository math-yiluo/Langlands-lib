import Langlands.GroupScheme.Torus.RationalDensity
import Langlands.GroupScheme.Torus.Integral
import Langlands.GroupScheme.GaloisPointRational
import Langlands.GroupScheme.HomConjugacy
import Langlands.GroupScheme.Torus.LatticeGalois
import Langlands.AlgebraicGeometry.PointTopology.RationalDensityExt

/-! # An element centralizing the rational points of a split torus centralizes the torus -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building.TwistedFixedTranslationCentralizer

/-- Let `S` and `G` be group schemes over a field `k`, let `iS : S ⟶ G`, and let `K / k`
be a field extension with `K` infinite such that the base change `S_K` is a split torus.
If a point `h ∈ G(K)` commutes with the image of every point of `S(K)`, then conjugation
by `h` fixes the base-changed morphism `S_K ⟶ G_K`. -/
theorem comp_innerIso_eq_of_commute {k K : Type u} [Field k] [Field K] [Algebra k K]
    [Infinite K] {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsSeparated G.X.hom]
    (iS : S.toGrp ⟶ G)
    (hS : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj S).toGrp)
    (h : rationalPoints (baseChanged k K G))
    (hh : ∀ s : rationalPoints (baseChanged k K S.toGrp),
      Commute h (rationalPoints.map ((GroupScheme.baseChange (baseMap k K)).map iS) s)) :
    (GroupScheme.baseChange (algebraBaseMap k K)).map iS ≫
        (((GroupScheme.baseChange (algebraBaseMap k K)).obj G).innerIso h).hom =
      (GroupScheme.baseChange (algebraBaseMap k K)).map iS := by
  have hS' : IsSplitTorus ((GroupScheme.baseChange (algebraBaseMap k K)).obj S.toGrp) := hS
  have : IsIntegral ((GroupScheme.baseChange (algebraBaseMap k K)).obj S.toGrp).X.left :=
    hS'.isIntegral
  have : IsSeparated ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
    change IsSeparated (Limits.pullback.snd G.X.hom (algebraBaseMap k K))
    infer_instance
  have hD : HasDenseRationalPoints K
      ((GroupScheme.baseChange (algebraBaseMap k K)).obj S.toGrp).X :=
    TorusDensity.dense_rationalPoints_of_isSplitTorus_baseChange (k := K) (K := K) _
      (hS'.baseChange _)
  apply Grp.hom_ext
  apply hom_ext_of_denseRationalPoints hD
  intro p
  have hc := (hh p).eq
  rw [rationalPoints.map_apply] at hc
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom, constantPoint_self]
  change h * (p ≫ ((GroupScheme.baseChange (algebraBaseMap k K)).map iS).hom.hom) * h⁻¹ = _
  rw [hc, mul_inv_cancel_right]

end Langlands.Geometry.Building.TwistedFixedTranslationCentralizer
