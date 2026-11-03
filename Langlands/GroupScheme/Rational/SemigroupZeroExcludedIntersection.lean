import Langlands.GroupScheme.Rational.CoordinateInvariantComponents
import Langlands.GroupScheme.Rational.CoordinateSemigroupStatement
import Langlands.GroupScheme.Rational.SemigroupIntersectionGeometry

/-! # The zero-excluded semigroup intersection comparison -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace CoordinateWeights

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

/-- An actual equivariant closed immersion includes augmentation weight support
in the augmentation weight support of the ambient group. -/
theorem support_subset_of_closedImmersion (hS : IsSplitTorus S.toGrp)
    (c : AutomorphicAction S.toGrp H) (b : AutomorphicAction S.toGrp G)
    (j : H ⟶ G) (hj : IsClosedSubgroup j)
    (heq : IsEquivariant c b j.hom.hom) : support c ⊆ support b := by
  have hf : PointedCoordinateWeights.IsPointedEquivariant
      (PointedCoordinateWeights.PointedAction.ofGroup c)
      (PointedCoordinateWeights.PointedAction.ofGroup b) j.hom.hom :=
    ⟨heq, IsMonHom.one_hom j.hom.hom⟩
  exact (PointedCoordinateWeights.closedImmersionPullback k S hS H.X G.X
    (PointedCoordinateWeights.PointedAction.ofGroup c)
    (PointedCoordinateWeights.PointedAction.ofGroup b) j.hom.hom hf hj).2.2.2.2

/-- For split-torus actions, absence of invariant augmentation functions passes
to every stable closed subgroup. -/
theorem trivialInvariantAugmentation_of_closedImmersion (hS : IsSplitTorus S.toGrp)
    (c : AutomorphicAction S.toGrp H) (b : AutomorphicAction S.toGrp G)
    (j : H ⟶ G) (hj : IsClosedSubgroup j)
    (heq : IsEquivariant c b j.hom.hom) (h : HasTrivialInvariantAugmentation b) :
    HasTrivialInvariantAugmentation c :=
  fun hz => h (support_subset_of_closedImmersion hS c b j hj heq hz)

end CoordinateWeights

namespace RelativeRoot

/-- The two independent geometric and coordinate inputs retained in the
zero-excluded intersection comparison. -/
def SemigroupZeroExcludedIntersectionPrerequisites : Prop :=
  SemigroupRealizationStatement.{u} ∧
    CoordinateWeights.AugmentationLieContainmentStatement.{u}

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

/-- The action on a connected semigroup representative has no invariant
augmentation function when zero is excluded from the semigroup. -/
theorem trivialInvariantAugmentation_semigroup_representative
    [Smooth G.X.hom]
    (hContain : CoordinateWeights.AugmentationLieContainmentStatement.{u})
    (b : AutomorphicAction S.toGrp G) (hS : IsSplitTorus S.toGrp)
    (A : AddSubsemigroup (characterLattice S)) (hA : 0 ∉ A)
    (hstable : b.IsStable (semigroupSubgroup b A))
    (hLie : HasLieImage (semigroupSubgroup b A) (semigroupWeightSpan b A))
    {L : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom L.X.hom]
    [Smooth L.X.hom] [ConnectedSpace L.X.left]
    (l : L ⟶ G) (hl : (semigroupSubgroup b A).IsRepresentedBy l) :
    CoordinateWeights.HasTrivialInvariantAugmentation
      (b.onRepresentedSubgroup l hl hstable) := by
  let d := b.onRepresentedSubgroup l hl hstable
  have hLieA : actionWeightSupport d ⊤ ⊆ A := by
    intro χ hχ
    have hnonzero : actionWeightSpace d χ ≠ ⊥ := by
      simpa only [mem_actionWeightSupport_iff, tangentSubmodule_top, inf_top_eq] using hχ
    have hχG := (mem_actionWeightSupport_iff_onRepresentedSubgroup b l hl hstable χ).mpr
      hnonzero
    exact ((HasLieImage.mem_actionWeightSupport_iff b hS A hLie χ).mp hχG).1
  have hcoordA : CoordinateWeights.support d ⊆ A :=
    (hContain k L inferInstance inferInstance inferInstance S hS d A).mpr hLieA
  exact fun hz => hA (hcoordA hz)

section Intersection

variable [Smooth G.X.hom] [Smooth H.X.hom]
    (b : AutomorphicAction S.toGrp G) (c : AutomorphicAction S.toGrp H)
    (j : H ⟶ G)
    (heq : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (x : T ⟶ H.X),
      c.act s x ≫ j.hom.hom = b.act s (x ≫ j.hom.hom))
    (hReal : SemigroupRealizationStatement.{u})
    (hContain : CoordinateWeights.AugmentationLieContainmentStatement.{u})
    (hS : IsSplitTorus S.toGrp) (hjc : IsClosedSubgroup j)
    (A : AddSubsemigroup (characterLattice S)) (hA : 0 ∉ A)

include heq hReal hContain hS hjc hA

/-- The actual semigroup inverse image is connected when zero is excluded.
No connectedness of the given closed subgroup H is required. -/
theorem semigroup_comap_eq_of_zero_not_mem :
    (semigroupSubgroup b A).comap j = semigroupSubgroup c A := by
  have hRG := hReal k G inferInstance inferInstance S hS b A
  obtain ⟨L, l, hl, hlc, hLs, hLc⟩ := hRG.1
  have : Smooth L.X.hom := hLs
  have : ConnectedSpace L.X.left := hLc
  have : IsAffineHom L.X.hom := hlc.isAffineHom
  have : Mono l.hom.hom := hl.1
  let K := subgroupIntersection j l
  let p : K ⟶ H := subgroupIntersectionFst j l
  let q : K ⟶ L := subgroupIntersectionSnd j l
  have hp : ((semigroupSubgroup b A).comap j).IsRepresentedBy p :=
    hl.comap_subgroupIntersectionFst hlc j
  have hpc : IsClosedSubgroup p :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (subgroupIntersection_isPullback_scheme j l).flip hlc
  have hqc : IsClosedSubgroup q :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (subgroupIntersection_isPullback_scheme j l) hjc
  have : IsAffineHom K.X.hom := hpc.isAffineHom
  have : Smooth K.X.hom :=
    smooth_semigroup_comap_representative b c j heq hReal hS hjc A p hp hpc
  have hstable := isStable_comap_of_equivariant b c j heq hRG.2.1
  let d := c.onRepresentedSubgroup p hp hstable
  let e := b.onRepresentedSubgroup l hl hRG.2.1
  have hfac : p.hom.hom ≫ j.hom.hom = q.hom.hom ≫ l.hom.hom :=
    (subgroupIntersection_isPullback j l).w
  have hqe : CoordinateWeights.IsEquivariant d e q.hom.hom := by
    intro T s x
    apply (cancel_mono l.hom.hom).mp
    calc
      (d.act s x ≫ q.hom.hom) ≫ l.hom.hom =
          (d.act s x ≫ p.hom.hom) ≫ j.hom.hom := by
        rw [Category.assoc, ← hfac, ← Category.assoc]
      _ = c.act s (x ≫ p.hom.hom) ≫ j.hom.hom := by
        rw [c.onRepresentedSubgroup_act_comp p hp hstable]
      _ = b.act s ((x ≫ p.hom.hom) ≫ j.hom.hom) := heq T s _
      _ = b.act s ((x ≫ q.hom.hom) ≫ l.hom.hom) := by
        rw [Category.assoc, hfac, ← Category.assoc]
      _ = e.act s (x ≫ q.hom.hom) ≫ l.hom.hom :=
        (b.onRepresentedSubgroup_act_comp l hl hRG.2.1 s _).symm
  have hzeroe : CoordinateWeights.HasTrivialInvariantAugmentation e :=
    trivialInvariantAugmentation_semigroup_representative hContain b hS A hA
      hRG.2.1 hRG.2.2.1 l hl
  have hzerod := CoordinateWeights.trivialInvariantAugmentation_of_closedImmersion
    hS d e q hqc hqe hzeroe
  have hconn := CoordinateWeights.connectedSpace_of_trivialInvariantAugmentation d hzerod
  exact semigroup_comap_eq_of_connected b c j heq hReal hS hjc A p hp hpc hconn

end Intersection

end RelativeRoot
end Langlands.GroupScheme
