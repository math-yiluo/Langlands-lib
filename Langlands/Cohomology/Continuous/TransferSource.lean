import Langlands.Cohomology.Continuous.FiniteQuotientComparisonProof
import Langlands.Cohomology.Continuous.SubgroupFiniteStages

universe u

open CategoryTheory

namespace Langlands.Continuous

variable {k G : Type u} [CommRing k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-- The subgroup's actual finite cohomology diagram, indexed by ambient normal subgroups. -/
noncomputable def transferSourceDiagram (A : Rep.{u} k G) (H : OpenSubgroup G) (q : ℕ) :
    FiniteQuotientIndex (G := G) ⥤ ModuleCat.{u} k :=
  transferIndexFunctor H ⋙ finiteQuotientDiagram (Rep.res H.toSubgroup.subtype A) q

variable [TopologicalSpace k]

/-- The proved final change of index and comparison identify the source of continuous transfer. -/
noncomputable def transferSourceComparisonIso (A : DiscreteModule k G)
    (H : OpenSubgroup G) (q : ℕ) :
    Limits.colimit (transferSourceDiagram A.toRep H q) ≅
      (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).obj
        (continuousCohomology q (A.restrict H.toSubgroup).toTopRep) := by
  letI : CompactSpace H := isCompact_iff_compactSpace.mp H.isClosed.isCompact
  exact Functor.Final.colimitIso (transferIndexFunctor H)
      (finiteQuotientDiagram (A.restrict H.toSubgroup).toRep q) ≪≫
    finiteQuotientComparisonIso (A.restrict H.toSubgroup) q

set_option backward.isDefEq.respectTransparency false in
theorem transferSourceComparisonIso_ι (A : DiscreteModule k G)
    (H : OpenSubgroup G) (N : OpenNormalSubgroup G) (q : ℕ) :
    Limits.colimit.ι (transferSourceDiagram A.toRep H q) (OrderDual.toDual N) ≫
        (transferSourceComparisonIso A H q).hom =
      finiteStageToContinuous (A.restrict H.toSubgroup)
        (restrictOpenNormal H (ambientOpenNormalCore H ⊓ N)) q := by
  let : CompactSpace H := isCompact_iff_compactSpace.mp H.isClosed.isCompact
  dsimp only [transferSourceComparisonIso, Iso.trans_hom]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ (finiteQuotientComparisonIso (A.restrict H.toSubgroup) q).hom)
      (Functor.Final.ι_colimitIso_hom (transferIndexFunctor H)
        (finiteQuotientDiagram (A.restrict H.toSubgroup).toRep q) (OrderDual.toDual N))).trans
      (finiteStageToColimit_comp_comparison (A.restrict H.toSubgroup) _ q))

set_option backward.isDefEq.respectTransparency false in
theorem transferSourceComparisonIso_inv_ι (A : DiscreteModule k G)
    (H : OpenSubgroup G) (N : OpenNormalSubgroup G) (q : ℕ) :
    finiteStageToContinuous (A.restrict H.toSubgroup)
        (restrictOpenNormal H (ambientOpenNormalCore H ⊓ N)) q ≫
      (transferSourceComparisonIso A H q).inv =
    Limits.colimit.ι (transferSourceDiagram A.toRep H q) (OrderDual.toDual N) := by
  rw [← transferSourceComparisonIso_ι A H N q, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

end Langlands.Continuous
