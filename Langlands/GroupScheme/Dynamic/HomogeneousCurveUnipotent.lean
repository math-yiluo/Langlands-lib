import Langlands.GroupScheme.HomogeneousQuotientCurveOrbit
import Langlands.GroupScheme.HomogeneousQuotientDimension
import Langlands.GroupScheme.Lie.SignedDynamicDimension
import Langlands.GroupScheme.Dynamic.UnipotentStructure
import Langlands.GroupScheme.UnitriangularUnipotentProof
import Langlands.GroupScheme.UnipotentClosedSubgroupProof
import Langlands.GroupScheme.Reductive.PositiveRootTangentDimension

/-! # Dynamic unipotent bounds from an actual homogeneous quotient curve -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HomogeneousQuotient

variable {k : Type u} [Field k]
    {G B : GroupScheme (Spec (CommRingCat.of k))}
    {Q : Over (Spec (CommRingCat.of k))}

/-- An actual smooth connected affine unipotent representative, with a moving
rational orbit on the quotient curve and actual Lie dimension at most one. -/
structure CurveUnipotentData
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (q : G.X ⟶ Q) (a : SchemeAction G Q) where
  group : GroupScheme (Spec (CommRingCat.of k))
  inclusion : group ⟶ G
  represents : (Dynamic.unipotent χ).IsRepresentedBy inclusion
  closed : IsClosedSubgroup inclusion
  affine : IsAffineHom group.X.hom
  smooth : Smooth group.X.hom
  connected : ConnectedSpace group.X.left
  unipotent : IsUnipotent group
  orbit : CurveOrbitData (a.restrict inclusion) (identityCoset G q)
  dimension_le_one : haveI := affine
    Lie.dimension group ≤ 1

/-- The constructed representative bounds the intrinsic tangent dimension of
the original all-test dynamic subgroup. -/
theorem CurveUnipotentData.finrank_tangent_le_one
    [IsAffineHom G.X.hom]
    {χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G}
    {q : G.X ⟶ Q} {a : SchemeAction G Q} (D : CurveUnipotentData χ q a) :
    Module.finrank k (RelativeRoot.tangentSubmodule (Dynamic.unipotent χ)) ≤ 1 := by
  have : IsAffineHom D.group.X.hom := D.affine
  rw [RelativeRoot.finrank_tangentSubmodule_eq_of_isRepresentedBy _ D.inclusion D.represents]
  exact D.dimension_le_one

variable [IsAlgClosed k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (b : B ⟶ G) (q : G.X ⟶ Q)
    (hfib : ∀ (Y : Over (Spec (CommRingCat.of k))) (g h : Y ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range b).carrier Y)
    [QuasiCompact q.left] [Smooth q.left] [Surjective q.left] [IsSeparated Q.hom]

/-- Construct the actual small dynamic group from a quotient curve and
noncontainment. Its unipotence, geometry and dimension gap are derived. -/
def curveUnipotentData
    (htorus : AlgClosedReductiveNormalSolvableTorusStatement.{u})
    (hG : IsPseudoReductive G) (hb : IsClosedSubgroup b)
    (hB : IsSolvableGroupScheme B)
    (hT : IsSplitTorus T.toGrp) (t : T.toGrp ⟶ B) (ν : cocharacterLattice T)
    (hdimQ : topologicalKrullDim Q.left ≤ 1)
    (hnot : ¬ Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ t ≫ b) ≤
      SubgroupFunctor.range b) :
    CurveUnipotentData (CommGroupScheme.groupHom ν ≫ t ≫ b) q
      (Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range b) q hfib) := by
  letI : Smooth G.X.hom := hG.smooth
  letI : IsAffineHom G.X.hom := hG.isAffineHom
  letI : ConnectedSpace G.X.left := hG.connectedSpace
  letI : IsClosedImmersion b.hom.hom.left := hb
  letI : Mono b.hom.hom := Over.mono_of_mono_left _
  letI : Smooth B.X.hom := smooth_subgroup_of_smooth_quotient G B b q hfib
  letI : IsAffineHom B.X.hom := affine_subgroup_of_closed G B b hb
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : IsAffine B.X.left := isAffine_of_isAffineHom B.X.hom
  let χB := CommGroupScheme.groupHom ν ≫ t
  let χG := χB ≫ b
  let U := Dynamic.Affine.unipotentScheme χG
  let H := Dynamic.Affine.unipotentScheme χB
  let i : U ⟶ G := Dynamic.Affine.unipotentHom χG
  let l : H ⟶ B := Dynamic.Affine.unipotentHom χB
  have hi : (Dynamic.unipotent χG).IsRepresentedBy i :=
    Dynamic.Affine.isRepresentedBy_unipotentHom χG
  have hl : (Dynamic.unipotent χB).IsRepresentedBy l :=
    Dynamic.Affine.isRepresentedBy_unipotentHom χB
  have hic : IsClosedSubgroup i := Dynamic.Affine.isClosedSubgroup_unipotentHom χG
  have hlc : IsClosedSubgroup l := Dynamic.Affine.isClosedSubgroup_unipotentHom χB
  let j : H ⟶ U := hl.mapHom hi b (Dynamic.unipotent_le_comap χB b)
  have hjc : IsClosedSubgroup j :=
    hl.isClosedSubgroup_mapHom hi b (Dynamic.unipotent_le_comap χB b) hlc hic hb
  have hji : j ≫ i = l ≫ b := hl.mapHom_comp hi b (Dynamic.unipotent_le_comap χB b)
  letI : Mono i.hom.hom := hi.1
  letI : IsAffineHom U.X.hom := hic.isAffineHom
  letI : IsAffineHom H.X.hom := hlc.isAffineHom
  letI : Smooth U.X.hom := (dynamicSmooth k G χG U i).2.2 hi
  letI : Smooth H.X.hom := (dynamicSmooth k B χB H l).2.2 hl
  letI : ConnectedSpace U.X.left :=
    DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent G χG hi
  letI : ConnectedSpace H.X.left :=
    DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent B χB hl
  have hU : IsUnipotent U := Dynamic.isUnipotent_of_unitriangular_inputs χG i hi hic
    unitriangularUnipotent unipotentClosedSubgroup
  have hH : IsUnipotent H := Dynamic.isUnipotent_of_unitriangular_inputs χB l hl hlc
    unitriangularUnipotent unipotentClosedSubgroup
  have hgap := lie_dimension_le_add_one_of_dimension_le_one b q hfib hdimQ
  have hsigned :=
    (RelativeRoot.signed_dynamic_dimensions_of_codimension_le_one hT t b ν hgap).1
  have hdim : Lie.dimension U ≤ Lie.dimension H + 1 := by
    change Module.finrank k (Additive (lieKernel U k)) ≤
      Module.finrank k (Additive (lieKernel H k)) + 1
    rw [← RelativeRoot.finrank_tangentSubmodule_eq_of_isRepresentedBy _ i hi,
      ← RelativeRoot.finrank_tangentSubmodule_eq_of_isRepresentedBy _ l hl]
    have heq : Dynamic.unipotent χG =
        Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ t ≫ b) :=
      congrArg Dynamic.unipotent (Category.assoc (CommGroupScheme.groupHom ν) t b)
    rw [heq]
    exact hsigned
  have hnon : ¬ SubgroupFunctor.range i ≤ SubgroupFunctor.range b := by
    rw [hi.2]
    simpa only [χG, χB, Category.assoc] using hnot
  have hsub : SubgroupFunctor.range (j ≫ i) ≤ SubgroupFunctor.range b := by
    rw [hji]
    intro Y g hg
    obtain ⟨h, hh⟩ := SubgroupFunctor.mem_range.mp hg
    exact SubgroupFunctor.mem_range.mpr ⟨h ≫ l.hom.hom, by
      simpa only [Grp.comp_hom_hom, Category.assoc] using hh⟩
  have hsmall := unipotent_dimension_le_one_of_structural b q hfib htorus hG
    hdimQ i j hjc hU hH hdim hnon hsub hb hB
  exact ⟨U, i, hi, hic, inferInstance, inferInstance, inferInstance, hU,
    curveOrbitData b q hfib hdimQ i hnon, hsmall.2.2⟩

include q hfib in
/-- A noncontained dynamic direction on an actual homogeneous quotient curve
has at most one positive root, under the explicit normal-solvable-torus input. -/
theorem positive_roots_eq_of_curve_quotient_of_noncontained_unipotent
    (htorus : AlgClosedReductiveNormalSolvableTorusStatement.{u})
    (hG : IsPseudoReductive G) (hb : IsClosedSubgroup b)
    (hB : IsSolvableGroupScheme B)
    (hT : IsSplitTorus T.toGrp) (t : T.toGrp ⟶ B) (ν : cocharacterLattice T)
    (hdimQ : topologicalKrullDim Q.left ≤ 1)
    (hnot : ¬ Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ t ≫ b) ≤
      SubgroupFunctor.range b) :
    haveI := hG.isAffineHom
    ∀ {α β : characterLattice T}, α ∈ roots (t ≫ b) → β ∈ roots (t ≫ b) →
      0 < latticePairing T α ν → 0 < latticePairing T β ν → α = β := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  let D := curveUnipotentData b q hfib htorus hG hb hB hT t ν hdimQ hnot
  intro α β
  exact RelativeRoot.positive_roots_eq_of_tangentSubmodule_unipotent_finrank_le_one
    hT (t ≫ b) ν D.finrank_tangent_le_one

end Langlands.GroupScheme.HomogeneousQuotient
