import Langlands.GroupScheme.Dynamic.HomogeneousCurveUnipotent
import Langlands.GroupScheme.Reductive.UnipotentSolvableNormalClosure

/-! # Unipotent bounds from dominant orbits in pseudo-reductive groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SchemeAction

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G H B : GroupScheme (Spec (CommRingCat.of k))}
    {X : Over (Spec (CommRingCat.of k))}
    (a : SchemeAction G X)

/-- A smooth connected affine unipotent source acting trivially has trivial
all-test image when a point has a solvable closed stabilizer. -/
theorem range_eq_bot_of_unipotent_kernel
    (hG : IsPseudoReductive G)
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    (j : H ⟶ G) (hH : IsUnipotent H)
    (hj : SubgroupFunctor.range j ≤ a.kernel)
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X) (b : B ⟶ G)
    (hb : IsClosedSubgroup b) (hrep : (a.stabilizer x).IsRepresentedBy b)
    (hB : IsSolvableGroupScheme B) : SubgroupFunctor.range j = ⊥ := by
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : ConnectedSpace G.X.left := hG.connectedSpace
  let D := smoothConnectedNormalClosure j
  exact D.range_eq_bot_of_isSolvable_of_isPseudoReductive hG hH
    (a.normalClosure_isSolvable_of_stabilizer D hj x b hb hrep hB)

/-- A codimension-at-most-one unipotent subgroup fixing a point with dominant
unipotent orbit is trivial in the pseudo-reductive ambient group with a supplied
solvable closed stabilizer. -/
theorem unipotent_dimension_le_one_of_dominant_orbit
    (hG : IsPseudoReductive G)
    {U : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth U.X.hom] [IsAffineHom U.X.hom] [ConnectedSpace U.X.left]
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    [IsReduced X.left] [LocallyOfFiniteType X.hom] [IsSeparated X.hom]
    (i : U ⟶ G) [Mono i.hom.hom] (j : H ⟶ U) (hj : IsClosedSubgroup j)
    (hU : IsUnipotent U) (hH : IsUnipotent H)
    (hdim : Lie.dimension U ≤ Lie.dimension H + 1)
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X)
    (hx : ((a.restrict i).restrict j).IsFixed x)
    [IsDominant ((a.restrict i).orbitMap x).left]
    [QuasiCompact ((a.restrict i).orbitMap x).left]
    (b : B ⟶ G) (hb : IsClosedSubgroup b)
    (hrep : (a.stabilizer x).IsRepresentedBy b) (hB : IsSolvableGroupScheme B) :
    SubgroupFunctor.range j = ⊥ ∧ Lie.dimension H = 0 ∧ Lie.dimension U ≤ 1 := by
  have : IsClosedImmersion j.hom.hom.left := hj
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have : Mono (j ≫ i).hom.hom := by
    rw [Grp.comp_hom_hom]
    infer_instance
  have hn := isNormal_of_lieDimension_le_succ_of_isUnipotent j hj hdim hU
  have hk := a.range_comp_le_kernel_of_dominant_orbit i j hn x hx
  have hz := a.range_eq_bot_of_unipotent_kernel hG
    (j ≫ i) hH hk x b hb hrep hB
  have hjz := (SubgroupFunctor.range_comp_eq_bot_iff j i).mp hz
  have hHz := Lie.dimension_eq_zero_of_range_eq_bot j hjz
  exact ⟨hjz, hHz, by omega⟩

end SchemeAction

namespace HomogeneousQuotient

section OrbitBound

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G B U H : GroupScheme (Spec (CommRingCat.of k))}
    {Q : Over (Spec (CommRingCat.of k))}
    (b : B ⟶ G) (q : G.X ⟶ Q)
    (hfib : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range b).carrier T)
    [QuasiCompact q.left] [Smooth q.left] [Surjective q.left]

include q hfib in
/-- The unipotent orbit bound for the actual identity coset of a smooth
exact homogeneous quotient curve in a pseudo-reductive group. -/
theorem unipotent_dimension_le_one
    (hG : IsPseudoReductive G)
    [Smooth U.X.hom] [IsAffineHom U.X.hom] [ConnectedSpace U.X.left]
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    [IsSeparated Q.hom]
    (hdimQ : topologicalKrullDim Q.left ≤ 1)
    (i : U ⟶ G) [Mono i.hom.hom] (j : H ⟶ U) (hj : IsClosedSubgroup j)
    (hU : IsUnipotent U) (hH : IsUnipotent H)
    (hdim : Lie.dimension U ≤ Lie.dimension H + 1)
    (hi : ¬ SubgroupFunctor.range i ≤ SubgroupFunctor.range b)
    (hji : SubgroupFunctor.range (j ≫ i) ≤ SubgroupFunctor.range b)
    (hb : IsClosedSubgroup b) (hB : IsSolvableGroupScheme B) :
    SubgroupFunctor.range j = ⊥ ∧ Lie.dimension H = 0 ∧ Lie.dimension U ≤ 1 := by
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : ConnectedSpace G.X.left := hG.connectedSpace
  have : IsClosedImmersion b.hom.hom.left := hb
  have : Mono b.hom.hom := Over.mono_of_mono_left _
  obtain ⟨hsm, hred, _⟩ := smooth_reduced_irreducible_quotient q
  have := hsm
  have := hred
  let a := Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range b) q hfib
  let D := curveOrbitData b q hfib hdimQ i hi
  have := D.dominant
  have := D.quasiCompact
  have hfix : ((a.restrict i).restrict j).IsFixed (identityCoset G q) := by
    have h := (isFixed_identityCoset_iff b q hfib (j ≫ i)).mpr hji
    intro T f g
    simpa only [SchemeAction.restrict_act, Grp.comp_hom_hom, Category.assoc]
      using h T f g
  exact a.unipotent_dimension_le_one_of_dominant_orbit
    hG i j hj hU hH hdim (identityCoset G q) hfix b hb
    (stabilizer_identityCoset_isRepresentedBy b q hfib) hB

end OrbitBound

variable {k : Type u} [Field k]
    {G B : GroupScheme (Spec (CommRingCat.of k))}
    {Q : Over (Spec (CommRingCat.of k))}

variable [IsAlgClosed k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (b : B ⟶ G) (q : G.X ⟶ Q)
    (hfib : ∀ (Y : Over (Spec (CommRingCat.of k))) (g h : Y ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range b).carrier Y)
    [QuasiCompact q.left] [Smooth q.left] [Surjective q.left] [IsSeparated Q.hom]

/-- Construct the actual small dynamic group from a quotient curve and
noncontainment. Its unipotence, geometry and dimension gap are derived. -/
def curveUnipotentDataOfPseudoReductive
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
  have hsmall := unipotent_dimension_le_one b q hfib hG
    hdimQ i j hjc hU hH hdim hnon hsub hb hB
  exact ⟨U, i, hi, hic, inferInstance, inferInstance, inferInstance, hU,
    curveOrbitData b q hfib hdimQ i hnon, hsmall.2.2⟩

include q hfib in
/-- A noncontained dynamic direction on an actual homogeneous quotient curve
has at most one positive root in a pseudo-reductive ambient group. -/
theorem positive_roots_eq_of_noncontained_unipotent_on_curve
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
  let D := curveUnipotentDataOfPseudoReductive b q hfib hG hb hB hT t ν hdimQ hnot
  intro α β
  exact RelativeRoot.positive_roots_eq_of_tangentSubmodule_unipotent_finrank_le_one
    hT (t ≫ b) ν D.finrank_tangent_le_one

end HomogeneousQuotient

end Langlands.GroupScheme
