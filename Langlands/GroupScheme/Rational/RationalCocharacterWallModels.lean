import Langlands.GroupScheme.Rational.RationalCocharacterParabolicModels
import Langlands.GroupScheme.SubgroupFunctor.IntersectionNormalizer

/-! # Actual rank-one wall models with the original embedded Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.LinearAlgebra.FiniteHyperplaneSegment
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RationalCocharacter

open RepresentedParabolicLeviIntersection

variable {k : Type u} [Field k]
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {G L M : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]

/-- A regular endpoint has the original fixed Levi as its centralizer inside
any closed subgroup through which both the endpoint torus and that Levi factor. -/
theorem innerCentralizer_isRepresentedBy
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (hA : IsSplitTorus A.toGrp) {i : A.toGrp ⟶ G} {j : L ⟶ G}
    (hj : (torusCentralizer i).IsRepresentedBy j)
    {jM : M ⟶ G} (hjM : IsClosedSubgroup jM)
    (iM : A.toGrp ⟶ M) (hiM : iM ≫ jM = i)
    (jL : L ⟶ M) (hjL : IsClosedSubgroup jL) (hcomp : jL ≫ jM = j)
    {x : Space A} (hx : Regular (rootForms i) x) :
    (Dynamic.centralizer
      (CommGroupScheme.groupHom (integralRealization hA x).cocharacter ≫ iM)).IsRepresentedBy jL := by
  let : Mono jM.hom.hom := mono_of_isClosedSubgroup hjM
  refine ⟨mono_of_isClosedSubgroup hjL, ?_⟩
  rw [Dynamic.centralizer_eq_comap_of_isClosedSubgroup _ jM hjM,
    Category.assoc, hiM]
  change SubgroupFunctor.range jL = (centralizer hA i x).comap jM
  rw [centralizer_eq_torusCentralizer_of_regular hA i hx, ← hj.2,
    ← hcomp, range_comp_eq_map, SubgroupFunctor.comap_map_of_mono]

/-- Actual rank-one wall data together with its exact outer centralizer
representation, retaining the original embedded Levi. -/
structure WallModel (hA : IsSplitTorus A.toGrp) (i : A.toGrp ⟶ G)
    (j : L ⟶ G) (x y w : Space A) where
  wall : RationalRankOneWallData j (parabolic hA i x) (parabolic hA i y)
  centralizer_rep : (centralizer hA i w).IsRepresentedBy (wall.m ≫ wall.p)

namespace IsWallDirection

/-- Construct the outer dynamic wall parabolic and the two opposite maximal
proper inner parabolics, with their common Levi source equal to the supplied L. -/
def wallModel (hG : IsConnectedReductive G)
    {a : A.toGrp ⟶ L} (ha : IsSplitComponent a)
    {j : L ⟶ G} (hjc : IsClosedSubgroup j)
    (hj : (torusCentralizer (a ≫ j)).IsRepresentedBy j)
    {x y w : Space A} (h : IsWallDirection (a ≫ j) x y w) :
    WallModel ha.1.1.1 (a ≫ j) j x y w := by
  let hA := ha.1.1.1
  let i := a ≫ j
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let : LocallyOfFiniteType G.X.hom := inferInstance
  let r := integralRealization hA w
  let s := integralRealization hA x
  let t := integralRealization hA y
  let d := Dynamic.rationalParabolicModel hG (CommGroupScheme.groupHom r.cocharacter ≫ i)
  let jM := d.m ≫ d.p
  have hjMc : IsClosedSubgroup jM :=
    d.levi.isClosedSubgroup.comp d.parabolic.isClosedSubgroup
  let : Mono jM.hom.hom := mono_of_isClosedSubgroup hjMc
  have hM := d.levi.isConnectedReductive
  let : IsAffineHom d.M.X.hom := hM.isAffineHom
  let : IsAffine d.M.X.left := isAffine_of_isAffineHom d.M.X.hom
  let : Smooth d.M.X.hom := hM.smooth
  let : LocallyOfFiniteType d.M.X.hom := inferInstance
  let iM := Dynamic.torusFactor i (CommGroupScheme.groupHom r.cocharacter) d.centralizer_rep
  have hiM : iM ≫ jM = i :=
    Dynamic.torusFactor_comp i (CommGroupScheme.groupHom r.cocharacter) d.centralizer_rep
  have hle : SubgroupFunctor.range j ≤
      Dynamic.centralizer (CommGroupScheme.groupHom r.cocharacter ≫ i) := by
    rw [hj.2]
    exact torusCentralizer_le_dynamicCentralizer i _
  let jL := d.centralizer_rep.factorHom j hle
  have hcomp : jL ≫ jM = j := d.centralizer_rep.factorHom_comp j hle
  have hjLc : IsClosedSubgroup jL := IsClosedSubgroup.of_comp hjMc (by
    rw [hcomp]
    exact hjc)
  have hxrep := innerCentralizer_isRepresentedBy hA hj hjMc iM hiM jL hjLc hcomp h.regular
  have hyrep := innerCentralizer_isRepresentedBy hA hj hjMc iM hiM jL hjLc hcomp h.regular'
  let dx := fixedLeviParabolicModel hM (CommGroupScheme.groupHom s.cocharacter ≫ iM) hxrep
  let dy := fixedLeviParabolicModel hM (CommGroupScheme.groupHom t.cocharacter ≫ iM) hyrep
  have hproper : ¬ IsIso dx.p := by
    intro hiso
    let := hiso
    apply h.parabolic_ne_top r d.centralizer_rep iM hiM hM s
    rw [← dx.parabolic_rep.2]
    calc
      SubgroupFunctor.range dx.p =
          SubgroupFunctor.range ((asIso dx.p).hom ≫ 𝟙 d.M) := by simp
      _ = SubgroupFunctor.range (𝟙 d.M) := SubgroupFunctor.range_iso_comp _ _
      _ = ⊤ := (SubgroupFunctor.top_isRepresentedBy_id d.M).2
  have haM : a ≫ dx.l ≫ dx.p = iM := by
    apply Grp.hom_ext
    apply (cancel_mono jM.hom.hom).mp
    change ((a ≫ dx.l ≫ dx.p) ≫ jM).hom.hom = (iM ≫ jM).hom.hom
    exact congrArg (fun b : A.toGrp ⟶ G => b.hom.hom) (by
      rw [dx.comp, Category.assoc, hcomp, hiM])
  refine
    { wall :=
      { P := d.P
        M := d.M
        Q := dx.P
        Q' := dy.P
        p := d.p
        m := d.m
        q := dx.p
        q' := dy.p
        l := dx.l
        l' := dy.l
        parabolic := d.parabolic
        levi := d.levi
        innerParabolic := dx.parabolic
        innerParabolic' := dy.parabolic
        innerLevi := dx.levi
        innerLevi' := dy.levi
        commonLevi := dy.comp.trans dx.comp.symm
        levi_comp := by simpa only [Category.assoc] using
          (congrArg (fun f => f ≫ jM) dx.comp).trans hcomp
        contained := by
          rw [d.parabolic_rep.2]
          exact (h.parabolic_le hA).1
        contained' := by
          rw [d.parabolic_rep.2]
          exact (h.parabolic_le hA).2
        intersection := by
          rw [dx.parabolic_rep.2,
            Dynamic.parabolic_eq_comap_of_isClosedSubgroup _ jM hjMc,
            Category.assoc, hiM]
          rfl
        intersection' := by
          rw [dy.parabolic_rep.2,
            Dynamic.parabolic_eq_comap_of_isClosedSubgroup _ jM hjMc,
            Category.assoc, hiM]
          rfl
        opposite := by
          rw [dx.parabolic_rep.2, dy.parabolic_rep.2,
            h.parabolic_eq_opposite r d.centralizer_rep iM hiM hA hM s t,
            groupHom_neg_comp_eq_oppositeCocharacter,
            Dynamic.parabolic_inf_opposite_eq_centralizer, ← hxrep.2, dx.comp]
        proper := hproper
        maximal := by
          apply isMaximalParabolic_of_proportional_splitComponent_pairings
            hM dx.parabolic dx.levi ha hproper
          rw [haM]
          exact h.proportional_pairings r d.centralizer_rep iM hiM }
      centralizer_rep := d.centralizer_rep }

end IsWallDirection

end Langlands.GroupScheme.RationalCocharacter
