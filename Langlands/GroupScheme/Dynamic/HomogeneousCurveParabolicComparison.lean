import Langlands.GroupScheme.Dynamic.HomogeneousCurveUnipotentProof
import Langlands.GroupScheme.Dynamic.SignedParabolicComparison

/-! # Actual dynamic parabolics from homogeneous quotient curves -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace HomogeneousQuotient

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G B : GroupScheme (Spec (CommRingCat.of k))}
    {Q : Over (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (b : B ⟶ G) (q : G.X ⟶ Q)
    (hfib : ∀ (Y : Over (Spec (CommRingCat.of k))) (g h : Y ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range b).carrier Y)
    [QuasiCompact q.left] [Smooth q.left] [Surjective q.left] [IsSeparated Q.hom]

include q hfib in
/-- The internal contracting subgroup is trivial when its ambient dynamic
subgroup moves on an actual homogeneous quotient curve. -/
theorem unipotent_eq_bot_of_noncontained_on_curve
    (hG : IsPseudoReductive G) (hb : IsClosedSubgroup b)
    (hB : IsSolvableGroupScheme B)
    (hT : IsSplitTorus T.toGrp) (t : T.toGrp ⟶ B) (ν : cocharacterLattice T)
    (hdimQ : topologicalKrullDim Q.left ≤ 1)
    (hnot : ¬ Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ t ≫ b) ≤
      SubgroupFunctor.range b) :
    Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ t) = ⊥ := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let : IsClosedImmersion b.hom.hom.left := hb
  let : Mono b.hom.hom := Over.mono_of_mono_left _
  let : Smooth B.X.hom := smooth_subgroup_of_smooth_quotient G B b q hfib
  let : IsAffineHom B.X.hom := affine_subgroup_of_closed G B b hb
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine B.X.left := isAffine_of_isAffineHom B.X.hom
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
  let : Mono i.hom.hom := hi.1
  let : IsAffineHom U.X.hom := hic.isAffineHom
  let : IsAffineHom H.X.hom := hlc.isAffineHom
  let : Smooth U.X.hom := (dynamicSmooth k G χG U i).2.2 hi
  let : Smooth H.X.hom := (dynamicSmooth k B χB H l).2.2 hl
  let : ConnectedSpace U.X.left :=
    DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent G χG hi
  let : ConnectedSpace H.X.left :=
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
  have hjz : SubgroupFunctor.range (j ≫ i) = ⊥ :=
    (SubgroupFunctor.range_comp_eq_bot_iff j i).mpr hsmall.1
  rw [hji] at hjz
  have hlz : SubgroupFunctor.range l = ⊥ :=
    (SubgroupFunctor.range_comp_eq_bot_iff l b).mp hjz
  rw [hl.2] at hlz
  exact hlz

end HomogeneousQuotient

namespace Dynamic

variable {k : Type u} [Field k]
    {G B : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    [IsAffineHom B.X.hom] [Smooth B.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Equal signed tangent dimensions along an actual smooth closed inclusion
force the ambient contracting subgroup to lie in that inclusion on all tests. -/
theorem unipotent_le_range_of_finrank_eq
    (b : B ⟶ G) (hb : IsClosedSubgroup b) (t : T.toGrp ⟶ B)
    (ν : cocharacterLattice T)
    (hdim : Module.finrank k (RelativeRoot.tangentSubmodule
      (unipotent (CommGroupScheme.groupHom ν ≫ t))) =
      Module.finrank k (RelativeRoot.tangentSubmodule
        (unipotent (CommGroupScheme.groupHom ν ≫ t ≫ b)))) :
    unipotent (CommGroupScheme.groupHom ν ≫ t ≫ b) ≤ SubgroupFunctor.range b := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine B.X.left := isAffine_of_isAffineHom B.X.hom
  let χB := CommGroupScheme.groupHom ν ≫ t
  let χG := χB ≫ b
  let U := Affine.unipotentScheme χG
  let H := Affine.unipotentScheme χB
  let i : U ⟶ G := Affine.unipotentHom χG
  let l : H ⟶ B := Affine.unipotentHom χB
  have hi : (unipotent χG).IsRepresentedBy i := Affine.isRepresentedBy_unipotentHom χG
  have hl : (unipotent χB).IsRepresentedBy l := Affine.isRepresentedBy_unipotentHom χB
  have hic : IsClosedSubgroup i := Affine.isClosedSubgroup_unipotentHom χG
  have hlc : IsClosedSubgroup l := Affine.isClosedSubgroup_unipotentHom χB
  let : IsAffineHom U.X.hom := hic.isAffineHom
  let : IsAffineHom H.X.hom := hlc.isAffineHom
  let : Smooth U.X.hom := (dynamicSmooth k G χG U i).2.2 hi
  let : Smooth H.X.hom := (dynamicSmooth k B χB H l).2.2 hl
  let : ConnectedSpace U.X.left :=
    DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent G χG hi
  let j : H ⟶ U := hl.mapHom hi b (unipotent_le_comap χB b)
  have hji : j ≫ i = l ≫ b := hl.mapHom_comp hi b (unipotent_le_comap χB b)
  let : IsIso j := hl.isIso_mapHom_of_finrank_eq hi b
    (unipotent_le_comap χB b) hlc hic hb (by
      change Module.finrank k (RelativeRoot.tangentSubmodule
        (unipotent (CommGroupScheme.groupHom ν ≫ t))) =
        Module.finrank k (RelativeRoot.tangentSubmodule
          (unipotent ((CommGroupScheme.groupHom ν ≫ t) ≫ b)))
      rwa [Category.assoc])
  have hrange : SubgroupFunctor.range (l ≫ b) = SubgroupFunctor.range i := by
    rw [← hji]
    exact SubgroupFunctor.range_iso_comp (asIso j) i
  intro Y g hg
  have hg' : g ∈ (SubgroupFunctor.range (l ≫ b)).carrier Y := by
    rw [hrange, hi.2]
    simpa only [χG, χB, Category.assoc] using hg
  obtain ⟨x, hx⟩ := SubgroupFunctor.mem_range.mp hg'
  refine SubgroupFunctor.mem_range.mpr ⟨x ≫ l.hom.hom, ?_⟩
  simpa only [Grp.comp_hom_hom, Category.assoc] using hx

/-- In codimension at most one, at least one ambient signed contracting
subgroup lies in the actual smooth closed subgroup. -/
theorem unipotent_or_neg_le_range_of_codimension_le_one
    (b : B ⟶ G) (hb : IsClosedSubgroup b)
    (hT : IsSplitTorus T.toGrp) (t : T.toGrp ⟶ B) (ν : cocharacterLattice T)
    (hdim : Lie.dimension G ≤ Lie.dimension B + 1) :
    unipotent (CommGroupScheme.groupHom ν ≫ t ≫ b) ≤ SubgroupFunctor.range b ∨
      unipotent (CommGroupScheme.groupHom (-ν) ≫ t ≫ b) ≤ SubgroupFunctor.range b := by
  let : IsClosedImmersion b.hom.hom.left := hb
  let : Mono b.hom.hom := Over.mono_of_mono_left _
  obtain ⟨_, _, heq⟩ :=
    RelativeRoot.signed_dynamic_dimensions_of_codimension_le_one hT t b ν hdim
  rcases heq with heq | heq
  · exact Or.inl (unipotent_le_range_of_finrank_eq b hb t ν heq.symm)
  · exact Or.inr (unipotent_le_range_of_finrank_eq b hb t (-ν) heq.symm)

end Dynamic

namespace HomogeneousQuotient

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G B : GroupScheme (Spec (CommRingCat.of k))}
    {Q : Over (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (b : B ⟶ G) (q : G.X ⟶ Q)
    (hfib : ∀ (Y : Over (Spec (CommRingCat.of k))) (g h : Y ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range b).carrier Y)
    [QuasiCompact q.left] [Smooth q.left] [Surjective q.left] [IsSeparated Q.hom]

include q hfib in
/-- A dynamic direction moving on a homogeneous quotient curve forces the
prescribed connected solvable subgroup to be the opposite dynamic parabolic,
provided it contains the actual dynamic centralizer. -/
theorem parabolic_neg_isRepresentedBy_of_noncontained_on_curve
    (hG : IsPseudoReductive G) (hb : IsClosedSubgroup b)
    (hB : IsSolvableGroupScheme B) (hBconn : ConnectedSpace B.X.left)
    (hT : IsSplitTorus T.toGrp) (t : T.toGrp ⟶ B) (ν : cocharacterLattice T)
    (hdimQ : topologicalKrullDim Q.left ≤ 1)
    (hnot : ¬ Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ t ≫ b) ≤
      SubgroupFunctor.range b)
    (hZ : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ t ≫ b) ≤
      SubgroupFunctor.range b) :
    (Dynamic.parabolic (CommGroupScheme.groupHom (-ν) ≫ t ≫ b)).IsRepresentedBy b := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let : IsClosedImmersion b.hom.hom.left := hb
  let : Mono b.hom.hom := Over.mono_of_mono_left _
  let : Smooth B.X.hom := smooth_subgroup_of_smooth_quotient G B b q hfib
  let : IsAffineHom B.X.hom := affine_subgroup_of_closed G B b hb
  let : ConnectedSpace B.X.left := hBconn
  have hgap := lie_dimension_le_add_one_of_dimension_le_one b q hfib hdimQ
  have hUn : Dynamic.unipotent (CommGroupScheme.groupHom (-ν) ≫ t ≫ b) ≤
      SubgroupFunctor.range b :=
    (Dynamic.unipotent_or_neg_le_range_of_codimension_le_one b hb hT t ν hgap).resolve_left
      hnot
  have hUb := unipotent_eq_bot_of_noncontained_on_curve b q hfib hG hb hB hT t ν
    hdimQ hnot
  have hPb := Dynamic.parabolic_neg_eq_top_of_unipotent_eq_bot hT t ν hUb
  have hZn : Dynamic.centralizer (CommGroupScheme.groupHom (-ν) ≫ t ≫ b) ≤
      SubgroupFunctor.range b := by
    rw [Dynamic.centralizer_groupHom_neg (t ≫ b) ν]
    exact hZ
  have hP_le := Dynamic.parabolic_le_of_unipotent_le_of_centralizer_le
    (CommGroupScheme.groupHom (-ν) ≫ t ≫ b) (SubgroupFunctor.range b) hUn hZn
  refine ⟨inferInstance, le_antisymm ?_ hP_le⟩
  intro Y g hg
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  have hx : x ∈ (Dynamic.parabolic (CommGroupScheme.groupHom (-ν) ≫ t)).carrier Y := by
    rw [hPb]
    exact Subgroup.mem_top _
  have him := Dynamic.parabolic_le_comap (CommGroupScheme.groupHom (-ν) ≫ t) b Y hx
  change x ≫ b.hom.hom ∈
    (Dynamic.parabolic ((CommGroupScheme.groupHom (-ν) ≫ t) ≫ b)).carrier Y at him
  simpa only [Category.assoc] using him

include q hfib in
/-- A proper connected solvable subgroup with an actual homogeneous quotient
curve and the dynamic centralizer represents one of the two signed parabolics. -/
theorem parabolic_or_neg_isRepresentedBy_of_curve
    (hG : IsPseudoReductive G) (hb : IsClosedSubgroup b)
    (hB : IsSolvableGroupScheme B) (hBconn : ConnectedSpace B.X.left)
    (hT : IsSplitTorus T.toGrp) (t : T.toGrp ⟶ B) (ν : cocharacterLattice T)
    (hdimQ : topologicalKrullDim Q.left ≤ 1) (hproper : ¬ IsIso b)
    (hZ : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ t ≫ b) ≤
      SubgroupFunctor.range b) :
    (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ t ≫ b)).IsRepresentedBy b ∨
      (Dynamic.parabolic (CommGroupScheme.groupHom (-ν) ≫ t ≫ b)).IsRepresentedBy b := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let : IsClosedImmersion b.hom.hom.left := hb
  let : Mono b.hom.hom := Over.mono_of_mono_left _
  let : Smooth B.X.hom := smooth_subgroup_of_smooth_quotient G B b q hfib
  let : IsAffineHom B.X.hom := affine_subgroup_of_closed G B b hb
  rcases Dynamic.not_le_range_unipotent_or_neg hT (t ≫ b) ν b hb hproper hZ with hp | hn
  · exact Or.inr (parabolic_neg_isRepresentedBy_of_noncontained_on_curve
      b q hfib hG hb hB hBconn hT t ν hdimQ hp hZ)
  · have hZn : Dynamic.centralizer (CommGroupScheme.groupHom (-ν) ≫ t ≫ b) ≤
        SubgroupFunctor.range b := by
      rw [Dynamic.centralizer_groupHom_neg (t ≫ b) ν]
      exact hZ
    left
    simpa only [neg_neg] using parabolic_neg_isRepresentedBy_of_noncontained_on_curve
      b q hfib hG hb hB hBconn hT t (-ν) hdimQ hn hZn

/-- Choose an actual signed cocharacter whose dynamic parabolic is represented
by the prescribed subgroup under the homogeneous-curve comparison hypotheses. -/
def signedParabolicRepresentativeOfCurve
    (hG : IsPseudoReductive G) (hb : IsClosedSubgroup b)
    (hB : IsSolvableGroupScheme B) (hBconn : ConnectedSpace B.X.left)
    (hT : IsSplitTorus T.toGrp) (t : T.toGrp ⟶ B) (ν : cocharacterLattice T)
    (hdimQ : topologicalKrullDim Q.left ≤ 1) (hproper : ¬ IsIso b)
    (hZ : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ t ≫ b) ≤
      SubgroupFunctor.range b) :
    {eta : cocharacterLattice T // (eta = ν ∨ eta = -ν) ∧
      (Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ t ≫ b)).IsRepresentedBy b} := by
  classical
  by_cases hp : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ t ≫ b)).IsRepresentedBy b
  · exact ⟨ν, Or.inl rfl, hp⟩
  · exact ⟨-ν, Or.inr rfl,
      (parabolic_or_neg_isRepresentedBy_of_curve
        b q hfib hG hb hB hBconn hT t ν hdimQ hproper hZ).resolve_left hp⟩

end HomogeneousQuotient

end Langlands.GroupScheme
