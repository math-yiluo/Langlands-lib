import Langlands.GroupScheme.RelativeLevi.ParabolicLieContainmentStatement
import Langlands.GroupScheme.SubgroupFunctor.ZariskiLocality

/-! # Equality of relative parabolics from residue fibres

The parabolic comparison lemmas in this module take the published
`RelativeParabolicLieContainmentStatement` as an explicit hypothesis.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- Containment in a monomorphically represented subgroup follows from
containment after restriction to a neighbourhood of each base point. -/
theorem le_range_of_forall_exists_open (F : SubgroupFunctor G) (i : H ⟶ G)
    [Mono i.hom.hom]
    (h : ∀ s : S, ∃ V : S.Opens, s ∈ V ∧
      F.baseChange V.ι ≤ (range i).baseChange V.ι) :
    F ≤ range i := by
  choose V hmem hle using h
  let 𝒰 := S.openCoverOfIsOpenCover V (by
    apply TopologicalSpace.IsOpenCover.mk
    apply top_le_iff.mp
    intro s _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨s, hmem s⟩)
  exact (le_range_iff_baseChange_openCover 𝒰 i).mpr hle

end SubgroupFunctor

variable {S : Scheme.{u}} {G P Q : GroupScheme S}
  (i : P ⟶ G) (j : Q ⟶ G) (T : CommGroupScheme S) (t : T.toGrp ⟶ G)

/-- The neighbourhood conclusion of the Lie-containment statement globalizes
when its Lie premise holds at every residue-field fibre. -/
theorem relativeParabolic_range_le_of_residueFiber_lie_le
    (hLie : RelativeParabolicLieContainmentStatement.{u})
    (hG : IsReductive G)
    (hi : IsRelativeParabolicSubgroup i) (hj : IsRelativeParabolicSubgroup j)
    (hT : RelativeTorus.IsTorus T.toGrp) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus t)
    (hti : SubgroupFunctor.range t ≤ SubgroupFunctor.range i)
    (htj : SubgroupFunctor.range t ≤ SubgroupFunctor.range j)
    (hfib : haveI := hG.isAffineHom
      ∀ s : S,
        haveI : IsAffineHom ((GroupScheme.baseChange (S.fromSpecResidueField s :
            Spec (CommRingCat.of (S.residueField s)) ⟶ S)).obj G).X.hom :=
          inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom _))
        (SubgroupFunctor.range (RelativeLevi.residueFiberHom j s)).lie (S.residueField s) ≤
          (SubgroupFunctor.range (RelativeLevi.residueFiberHom i s)).lie
            (S.residueField s)) :
    SubgroupFunctor.range j ≤ SubgroupFunctor.range i := by
  letI : Mono i.hom.hom := hi.mono
  apply SubgroupFunctor.le_range_of_forall_exists_open
  intro s
  obtain ⟨V, hs, hV⟩ :=
    hLie S G P Q i j T t s hG hi hj hT ht hmax hti htj (hfib s)
  refine ⟨V, hs, ?_⟩
  simpa only [SubgroupFunctor.range_baseChangeHom] using hV

/-- Conditional on Lie containment spreading, two relative parabolics
containing a common maximal torus are equal if their residue-fibre images agree. -/
theorem relativeParabolic_range_eq_of_residueFiber_range_eq
    (hLie : RelativeParabolicLieContainmentStatement.{u})
    (hG : IsReductive G)
    (hi : IsRelativeParabolicSubgroup i) (hj : IsRelativeParabolicSubgroup j)
    (hT : RelativeTorus.IsTorus T.toGrp) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus t)
    (hti : SubgroupFunctor.range t ≤ SubgroupFunctor.range i)
    (htj : SubgroupFunctor.range t ≤ SubgroupFunctor.range j)
    (hfib : ∀ s : S,
      SubgroupFunctor.range (RelativeLevi.residueFiberHom i s) =
        SubgroupFunctor.range (RelativeLevi.residueFiberHom j s)) :
    SubgroupFunctor.range i = SubgroupFunctor.range j := by
  haveI := hG.isAffineHom
  apply le_antisymm
  · apply relativeParabolic_range_le_of_residueFiber_lie_le j i T t hLie hG hj hi
      hT ht hmax htj hti
    intro s
    rw [hfib s]
  · apply relativeParabolic_range_le_of_residueFiber_lie_le i j T t hLie hG hi hj
      hT ht hmax hti htj
    intro s
    rw [hfib s]

end Langlands.GroupScheme
