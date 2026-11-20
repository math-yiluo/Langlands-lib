import Langlands.Representation.Plancherel.DynamicCommonLeviGallery
import Langlands.Representation.Plancherel.DynamicRepresentedInductionEvaluation
import Langlands.Representation.Exponents.LeviInductionStages

/-! # Parabolic extension data at a dynamic rank-one wall -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Plancherel.DynamicCommonLeviComposition

open Aubert.General.RepresentedParabolic DynamicCommonLeviPresentations
open DynamicOppositeStandardIntertwining

variable {F : Type u} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

/-- A radical satisfying the multiplication property for the specified Levi inclusion. -/
structure LeviRadical {P M : GroupScheme (Spec (CommRingCat.of F))} (l : M ⟶ P) where
  group : GroupScheme (Spec (CommRingCat.of F))
  inclusion : group ⟶ P
  isRadical : LeviSubgroup.IsGeometricUnipotentRadical inclusion
  multiplication : IsIso (subgroupMultiplication l inclusion)

/-- Choose the radical supplied by the rational Levi property. -/
def LeviRadical.ofLevi {P M : GroupScheme (Spec (CommRingCat.of F))}
    (l : M ⟶ P) (hl : IsRationalLeviSubgroup l) : LeviRadical l :=
  let h := hl.exists_unipotentRadical
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.1, h.choose_spec.choose_spec.2⟩

namespace DynamicRankOneWall

variable {χ ψ ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G}
  (W : DynamicRankOneWall χ ψ ψ')

/-- The radical of the outer parabolic through which induction is performed. -/
def outerRadical (W : DynamicRankOneWall χ ψ ψ') : LeviRadical W.wall.m :=
  LeviRadical.ofLevi _ W.wall.levi

/-- The radical of the first parabolic in the wall Levi. -/
def innerRadical (W : DynamicRankOneWall χ ψ ψ') : LeviRadical W.wall.l :=
  LeviRadical.ofLevi _ W.wall.innerLevi

/-- The radical of the opposite parabolic in the same wall Levi. -/
def innerRadical' (W : DynamicRankOneWall χ ψ ψ') : LeviRadical W.wall.l' :=
  LeviRadical.ofLevi _ W.wall.innerLevi'

omit [IsAffineHom G.X.hom] in
private theorem pointImage_comp_eq_map {P L : GroupScheme (Spec (CommRingCat.of F))}
    (q : P ⟶ L) (j : L ⟶ G) :
    pointImage (q ≫ j) = (pointImage q).map (rationalPoints.map j) := by
  rw [pointImage, pointImage, MonoidHom.map_range]
  congr 1

omit [IsAffineHom G.X.hom] in
private theorem pointImage_comp_eq_inf {P L R : GroupScheme (Spec (CommRingCat.of F))}
    (q : P ⟶ L) (j : L ⟶ G) (r : R ⟶ G)
    (h : SubgroupFunctor.range q = (SubgroupFunctor.range r).comap j) :
    pointImage (q ≫ j) = pointImage j ⊓ pointImage r := by
  have hpoint : pointImage q = (pointImage r).comap (rationalPoints.map j) := by
    rw [pointImage_eq_range_carrier q, h, pointImage_eq_range_carrier r]
    rfl
  rw [pointImage_comp_eq_map, hpoint, Subgroup.map_comap_eq]

/-- The two inner parabolics intersect in the original embedded Levi on points. -/
theorem pointImage_inner_inf :
    pointImage W.wall.q ⊓ pointImage W.wall.q' = pointImage (W.wall.l ≫ W.wall.q) := by
  rw [pointImage_eq_range_carrier W.wall.q, pointImage_eq_range_carrier W.wall.q',
    pointImage_eq_range_carrier (W.wall.l ≫ W.wall.q)]
  exact congrArg (fun D : SubgroupFunctor W.wall.M => D.carrier (Over.mk (𝟙 _))) W.wall.opposite

variable {T : CommGroupScheme (Spec (CommRingCat.of F))} {a : T.toGrp ⟶ parameterScheme χ}
  (hG : IsConnectedReductive G) (d : ParabolicData χ ψ T a) (d' : ParabolicData χ ψ' T a)

/-- The first upper represented parabolic is the extension of the first
wall parabolic through the outer wall parabolic. -/
def extension : LeviParabolicExtensionDatum W.wall.p W.wall.m W.wall.q W.wall.l where
  R := d.P
  W := d.U
  pR := d.p
  nR := d.l
  rR := d.n
  hpR := d.r.isCompatible.parabolic
  hnR := d.r.isCompatible.levi
  hrR := d.radical
  hmulR := multiplication_isIso hG d
  levi_comp := d.levi_comp.trans (by rw [← Category.assoc, W.wall.levi_comp])
  pointImage_le := by
    rw [pointImage_eq_range_carrier, pointImage_eq_range_carrier, d.realizes.parabolic]
    exact W.wall.contained _
  pointImage_inf := by
    apply pointImage_comp_eq_inf
    rw [d.realizes.parabolic]
    exact W.wall.intersection

/-- The second upper represented parabolic is the extension of the opposite
wall parabolic through the same outer wall parabolic. -/
def extension' : LeviParabolicExtensionDatum W.wall.p W.wall.m W.wall.q' W.wall.l' where
  R := d'.P
  W := d'.U
  pR := d'.p
  nR := d'.l
  rR := d'.n
  hpR := d'.r.isCompatible.parabolic
  hnR := d'.r.isCompatible.levi
  hrR := d'.radical
  hmulR := multiplication_isIso hG d'
  levi_comp := d'.levi_comp.trans (by
    rw [← Category.assoc, W.wall.commonLevi, W.wall.levi_comp])
  pointImage_le := by
    rw [pointImage_eq_range_carrier, pointImage_eq_range_carrier, d'.realizes.parabolic]
    exact W.wall.contained' _
  pointImage_inf := by
    apply pointImage_comp_eq_inf
    rw [d'.realizes.parabolic]
    exact W.wall.intersection'

end DynamicRankOneWall

end Langlands.Plancherel.DynamicCommonLeviComposition
