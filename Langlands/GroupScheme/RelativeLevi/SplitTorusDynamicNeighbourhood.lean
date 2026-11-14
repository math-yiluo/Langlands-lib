import Langlands.GroupScheme.RelativeLevi.SplitTorusContainment

/-! # Dynamic parabolic neighbourhoods through a prescribed split torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeLevi

/-- A relative parabolic containing the supplied split torus has a dynamic
presentation by that torus near any point where it is ambient maximal. -/
theorem exists_open_torusDynamicPresentation_of_splitTorus
    {S : Scheme.{u}} {G P : GroupScheme S}
    (hG : IsReductive G) (i : P ⟶ G) (hi : IsRelativeParabolicSubgroup i)
    (T : CommGroupScheme S) (t : T.toGrp ⟶ P) (hT : IsSplitTorus T.toGrp) (s : S)
    (hmax : IsMaximalTorus
      (T := (CommGroupScheme.baseChange (S.fromSpecResidueField s)).obj T)
      ((GroupScheme.baseChange (S.fromSpecResidueField s)).map (t ≫ i))) :
    ∃ (U : Scheme.{u}) (p : U ⟶ S), IsOpenImmersion p ∧ s ∈ Set.range p ∧
      ∃ nu : (Gm U).toGrp ⟶ (GroupScheme.baseChange p).obj T.toGrp,
        (Dynamic.parabolic
          (nu ≫ (GroupScheme.baseChange p).map t ≫
            (GroupScheme.baseChange p).map i)).IsRepresentedBy
          ((GroupScheme.baseChange p).map i) := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : GeometricallyConnected G.X.hom := hG.geometricallyConnected
  let : Smooth P.X.hom := hi.smooth
  let : IsAffineHom P.X.hom := hi.isAffineHom
  let : GeometricallyConnected P.X.hom := hi.geometricallyConnected hG
  let : Mono i.hom.hom := hi.mono
  let : Mono i.hom.hom.left := Over.mono_left_of_mono _
  let b := S.fromSpecResidueField s
  have hTPb : SubgroupFunctor.range ((GroupScheme.baseChange b).map (t ≫ i)) ≤
      SubgroupFunctor.range ((GroupScheme.baseChange b).map i) := by
    rw [Functor.map_comp]
    exact SubgroupFunctor.range_comp_le _ _
  obtain ⟨ν, hν⟩ := exists_fixedTorusDynamicPresentation_of_isParabolicSubgroup
    (T := (CommGroupScheme.baseChange b).obj T)
    (hG.isConnectedReductive_residueFiber s) ((GroupScheme.baseChange b).map i)
    (hi.residueFiber s) ((GroupScheme.baseChange b).map (t ≫ i)) hmax hTPb
  obtain ⟨nuGlobal, hnuGlobal⟩ :=
    IsSplitTorus.cocharacterLattice_baseChange_surjective_field T hT b ν
  let χP := CommGroupScheme.groupHom nuGlobal ≫ t
  have hfield : SubgroupFunctor.range ((GroupScheme.baseChange b).map i) =
      Dynamic.parabolic (Dynamic.baseChangeCocharacter b (χP ≫ i)) := by
    have hbχ : Dynamic.baseChangeCocharacter b (χP ≫ i) =
        CommGroupScheme.groupHom ν ≫ (GroupScheme.baseChange b).map (t ≫ i) := by
      have h :=
        (baseChangeCocharacter_torus_comp b T (t ≫ i) nuGlobal).trans
          (congrArg
            (fun (nuF : cocharacterLattice ((CommGroupScheme.baseChange b).obj T)) =>
              CommGroupScheme.groupHom (G := Gm (Spec (CommRingCat.of (S.residueField s))))
                (H := (CommGroupScheme.baseChange b).obj T) nuF ≫
                  (GroupScheme.baseChange b).map (t ≫ i))
            hnuGlobal)
      exact (congrArg (Dynamic.baseChangeCocharacter b)
        (Category.assoc (CommGroupScheme.groupHom nuGlobal) t i)).trans h
    exact hν.trans (congrArg Dynamic.parabolic hbχ.symm)
  have hbpoint : b (IsLocalRing.closedPoint (S.residueField s)) = s :=
    Scheme.fromSpecResidueField_apply _ _
  have hic : IsClosedSubgroup ((GroupScheme.baseChange
      (S.fromSpecResidueField (b (IsLocalRing.closedPoint (S.residueField s))))).map i) := by
    rw [hbpoint]
    exact (hi.residueFiber s).isClosedSubgroup
  obtain ⟨U, p, hp, bU, hbU, hpres⟩ :=
    Dynamic.exists_local_presentation_of_fieldPoint i χP b hic hfield
  have hs : s ∈ Set.range p := by
    refine ⟨bU (IsLocalRing.closedPoint (S.residueField s)), ?_⟩
    rw [← Scheme.Hom.comp_apply, hbU]
    exact hbpoint
  let nu := Dynamic.baseChangeCocharacter p (CommGroupScheme.groupHom nuGlobal)
  have hlocal : Dynamic.baseChangeCocharacter p (χP ≫ i) =
      nu ≫ (GroupScheme.baseChange p).map t ≫
        (GroupScheme.baseChange p).map i := by
    simp only [χP, Dynamic.baseChangeCocharacter_comp, nu, Functor.map_comp, Category.assoc]
  rw [hlocal] at hpres
  have : Mono ((GroupScheme.baseChange p).map i).hom.hom := by
    change Mono ((Over.pullback p).map i.hom.hom)
    infer_instance
  exact ⟨U, p, hp, hs, nu, inferInstance, hpres⟩

/-- Actual neighbourhood data retaining the supplied torus and the normalized
cocharacter into its pullback. -/
structure SplitTorusDynamicNeighbourhoodData
    {S : Scheme.{u}} {G P : GroupScheme S} (i : P ⟶ G)
    (T : CommGroupScheme S) (t : T.toGrp ⟶ P) (s : S) where
  base : Scheme.{u}
  projection : base ⟶ S
  openImmersion : IsOpenImmersion projection
  contains : s ∈ Set.range projection
  cocharacter : (Gm base).toGrp ⟶ (GroupScheme.baseChange projection).obj T.toGrp
  presents :
    (Dynamic.parabolic
      (cocharacter ≫ (GroupScheme.baseChange projection).map t ≫
        (GroupScheme.baseChange projection).map i)).IsRepresentedBy
      ((GroupScheme.baseChange projection).map i)

/-- Choose the proved dynamic presentation neighbourhood in the same split torus. -/
def splitTorusDynamicNeighbourhood
    {S : Scheme.{u}} {G P : GroupScheme S}
    (hG : IsReductive G) (i : P ⟶ G) (hi : IsRelativeParabolicSubgroup i)
    (T : CommGroupScheme S) (t : T.toGrp ⟶ P) (hT : IsSplitTorus T.toGrp) (s : S)
    (hmax : IsMaximalTorus
      (T := (CommGroupScheme.baseChange (S.fromSpecResidueField s)).obj T)
      ((GroupScheme.baseChange (S.fromSpecResidueField s)).map (t ≫ i))) :
    SplitTorusDynamicNeighbourhoodData i T t s :=
  Classical.choice (by
    obtain ⟨U, p, hp, hs, nu, hnu⟩ :=
      exists_open_torusDynamicPresentation_of_splitTorus hG i hi T t hT s hmax
    exact ⟨⟨U, p, hp, hs, nu, hnu⟩⟩)

end Langlands.GroupScheme.RelativeLevi
