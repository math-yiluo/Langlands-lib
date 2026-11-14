import Langlands.GroupScheme.Torus.RelativeMaximalLocus
import Langlands.GroupScheme.Torus.RelativeCommutativity
import Langlands.GroupScheme.Torus.MaximalModuliRestriction
import Langlands.GroupScheme.HomScheme.SmoothTorusSubgroupRepresentabilityProof

/-! # The smooth universal family of maximal tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

/-- A pulled-back closed torus is fibrewise maximal exactly when the image
of the base map lies in its original maximal locus. -/
theorem isFibrewiseMaximalTorus_baseChange_iff_range_subset
    {S S' : Scheme.{u}} {G : GroupScheme S}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] {K : CommGroupScheme S}
    (b : S' ⟶ S) (j : K.toGrp ⟶ G) (hj : IsClosedSubgroup j) :
    IsFibrewiseMaximalTorus (T := (CommGroupScheme.baseChange b).obj K)
      ((baseChange b).map j) ↔ Set.range b ⊆ maximalTorusLocus j := by
  change (∀ x : S', x ∈ maximalTorusLocus
    (T := (CommGroupScheme.baseChange b).obj K) ((baseChange b).map j)) ↔ _
  rw [maximalTorusLocus_baseChange (T := K) (G := G) b j hj]
  exact (Set.range_subset_iff (f := (b : S' → S))
    (s := maximalTorusLocus j)).symm

namespace TorusSubgroupModuli

variable {S : Scheme.{u}} {G : GroupScheme S} {M : Over S}
  {K : CommGroupScheme M.left}

/-- The open parameter subscheme on which the actual torus family is maximal. -/
def maximalOpen (hG : IsReductive G)
    (j : K.toGrp ⟶ (baseChange M.hom).obj G)
    (hj : IsClosedSubgroup j) (hK : RelativeTorus.IsTorus K.toGrp) : M.left.Opens :=
  maximalTorusOpen (hG.baseChange M.hom) hK j hj

/-- Evaluation on every test scheme detects the actual maximal open locus. -/
theorem isFibrewiseMaximalTorus_familyHom_iff
    (hG : IsReductive G) (j : K.toGrp ⟶ (baseChange M.hom).obj G)
    (hj : IsClosedSubgroup j) (hK : RelativeTorus.IsTorus K.toGrp)
    (T : Over S) (a : T ⟶ M) :
    IsFibrewiseMaximalTorus (T := (CommGroupScheme.baseChange a.left).obj K)
      (familyHom j a) ↔
        Set.range a.left ⊆ (maximalOpen hG j hj hK : Set M.left) := by
  let H := (baseChange M.hom).obj G
  let : Smooth H.X.hom := (hG.baseChange M.hom).smooth
  let : IsAffineHom H.X.hom := (hG.baseChange M.hom).isAffineHom
  let e := Descent.pullbackComparison M.hom a.left T.hom (Over.w a) G
  have he : IsFibrewiseMaximalTorus
      (T := (CommGroupScheme.baseChange a.left).obj K) (familyHom j a) ↔
      IsFibrewiseMaximalTorus (T := (CommGroupScheme.baseChange a.left).obj K)
        ((baseChange a.left).map j) := by
    apply forall_congr'
    intro x
    let c := T.left.fromSpecResidueField x
    change IsMaximalTorus
      (T := (CommGroupScheme.baseChange c).obj ((CommGroupScheme.baseChange a.left).obj K))
      ((baseChange c).map ((baseChange a.left).map j ≫ e.hom)) ↔ _
    rw [Functor.map_comp]
    exact IsMaximalTorus.comp_iso_iff
      (T := (CommGroupScheme.baseChange c).obj ((CommGroupScheme.baseChange a.left).obj K))
      ((baseChange c).map ((baseChange a.left).map j)) ((baseChange c).mapIso e)
  exact he.trans (isFibrewiseMaximalTorus_baseChange_iff_range_subset
    (G := H) (K := K) a.left j hj)

/-- A reductive group over any scheme has a smooth universal family of closed
fibrewise maximal relative tori. -/
theorem exists_smooth_isUniversalMaximal (S : Scheme.{u})
    (G : GroupScheme S) (hG : IsReductive G) :
    ∃ (M : Over S) (K : CommGroupScheme M.left)
      (j : K.toGrp ⟶ (baseChange M.hom).obj G),
      RelativeTorus.IsTorus K.toGrp ∧ IsClosedSubgroup j ∧
        IsFibrewiseMaximalTorus j ∧ IsUniversalMaximal j ∧ Smooth M.hom := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨M, K, j, hj, hK, huni, hs⟩ := smoothTorusSubgroupRepresentability S G
  let C : CommGroupScheme M.left := hK.commGroupScheme
  let i : C.toGrp ⟶ (baseChange M.hom).obj G := j
  let U := maximalOpen hG i hj hK
  let : Smooth M.hom := hs
  have hm := isUniversalMaximal_openFamily (K := C) i hj huni U
    (fun T a => isFibrewiseMaximalTorus_familyHom_iff hG i hj hK T a)
  have hc := openFamily_isClosed_isTorus (K := C) i U hj hK
  exact ⟨openModuli M U, (CommGroupScheme.baseChange U.ι).obj C,
    openFamily i U, hc.2, hc.1, hm.1, hm.2, smooth_openModuli U⟩

end TorusSubgroupModuli
end Langlands.GroupScheme
