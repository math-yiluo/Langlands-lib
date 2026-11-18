import Langlands.GroupScheme.Reductive.RootPartitionNormalSubgroup
import Langlands.GroupScheme.SubgroupFunctor.SmoothConnectedNormalFactorProduct
import Langlands.GroupScheme.SubgroupFunctor.FppfProductGeometry
import Langlands.GroupScheme.Reductive.CommutingMultiplicationFiniteCenters
import Langlands.GroupScheme.Reductive.DirectProductProof
import Langlands.GroupScheme.SimplyConnected.Basic

/-! # Multiplication for complementary commuting root partitions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RootPartitionNormalModel

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G)
    {s t : Set (characterLattice T)}
    (M : RootPartitionNormalModel i s) (N : RootPartitionNormalModel i t)
    (hdisj : Disjoint s t)

include hdisj in
/-- The two generated models for disjoint root parts commute on every test. -/
theorem commute (Z : Over (Spec (CommRingCat.of k)))
    (x : Z ⟶ M.group.X) (y : Z ⟶ N.group.X) :
    Commute (x ≫ M.inclusion.hom.hom) (y ≫ N.inclusion.hom.hom) := by
  have hx := M.range_le_centralizer i N hdisj Z
    (SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩)
  simpa only [Category.id_comp] using
    hx Z (𝟙 Z) (y ≫ N.inclusion.hom.hom) (SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩)

/-- Actual multiplication of the two commuting generated subgroups. -/
def multiplication : M.group ⊗ N.group ⟶ G :=
  commutingSubgroupMultiplicationHom M.inclusion N.inclusion (M.commute i N hdisj)

variable [IsAlgClosed k]

/-- If the two root parts cover all roots, the actual subgroup multiplication
is surjective. -/
theorem multiplication_surjective (hG : IsSemisimple G)
    (hsplit : IsSplitSubtorus i) (hmax : IsMaximalTorus i)
    (hcover : s ∪ t = relativeRoots i) :
    Surjective (subgroupMultiplication M.inclusion N.inclusion).left := by
  classical
  let : Smooth G.X.hom := hG.isConnectedReductive.smooth
  let : Smooth M.group.X.hom := M.semisimple.isConnectedReductive.smooth
  let : ConnectedSpace M.group.X.left := M.semisimple.isConnectedReductive.connectedSpace
  let : Smooth N.group.X.hom := N.semisimple.isConnectedReductive.smooth
  let : ConnectedSpace N.group.X.left := N.semisimple.isConnectedReductive.connectedSpace
  obtain ⟨P, p, hp, _, _⟩ :=
    SmoothConnectedNormalFactorProduct.exists_isFppfProduct
      M.inclusion N.inclusion M.closed N.closed N.normal
  have htop : SubgroupFunctor.range p = ⊤ := by
    apply semisimpleRootGeneration k G hG T i hsplit hmax P p hp.isClosedSubgroup
    intro α hα
    rw [← hcover] at hα
    rcases hα with hα | hα
    · exact (M.contains α hα).trans hp.left_le
    · exact (N.contains α hα).trans hp.right_le
  let : IsClosedImmersion p.hom.hom.left := hp.isClosedSubgroup
  have hrepP : (⊤ : SubgroupFunctor G).IsRepresentedBy p :=
    ⟨Over.mono_of_mono_left _, htop⟩
  have : IsIso p := by
    rw [← hrepP.topIso_hom]
    infer_instance
  have hps : Surjective p.hom.hom.left := by
    have : IsIso p.hom.hom.left :=
      ((Over.forget _).map_isIso ((Grp.forget _).map p))
    infer_instance
  let : IsClosedImmersion M.inclusion.hom.hom.left := M.closed
  let : IsClosedImmersion N.inclusion.hom.hom.left := N.closed
  have hrepM : (SubgroupFunctor.range M.inclusion).IsRepresentedBy M.inclusion :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  have hrepN : (SubgroupFunctor.range N.inclusion).IsRepresentedBy N.inclusion :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  let q := hp.productMul hrepM hrepN
  have hqs : Surjective q.left := hp.surjective_productMul hrepM hrepN
  let : Surjective q.left := hqs
  let : Surjective p.hom.hom.left := hps
  have hcomp : Surjective (q.left ≫ p.hom.hom.left) := inferInstance
  have he : q.left ≫ p.hom.hom.left =
      (subgroupMultiplication M.inclusion N.inclusion).left :=
    congrArg Over.Hom.left (hp.productMul_comp hrepM hrepN)
  rwa [he] at hcomp

/-- Complementary commuting root parts multiply by an actual central isogeny
onto the ambient semisimple group. -/
theorem multiplication_isCentralIsogeny (hG : IsSemisimple G)
    (hsplit : IsSplitSubtorus i) (hmax : IsMaximalTorus i)
    (hcover : s ∪ t = relativeRoots i) :
    IsCentralIsogeny (M.multiplication i N hdisj) := by
  let : Smooth G.X.hom := hG.isConnectedReductive.smooth
  exact isCentralIsogeny_commutingSubgroupMultiplicationHom_of_finite_centers
    M.inclusion N.inclusion M.closed N.closed (M.commute i N hdisj)
    (M.multiplication_surjective i N hG hsplit hmax hcover)
    M.semisimple.hasFiniteCenter N.semisimple.hasFiniteCenter

/-- In a simply connected ambient group the same actual multiplication is
an isomorphism, with no hypotheses on the sizes of the two root parts. -/
def multiplicationIso (hG : IsSimplyConnected G)
    (hsplit : IsSplitSubtorus i) (hmax : IsMaximalTorus i)
    (hcover : s ∪ t = relativeRoots i) : M.group ⊗ N.group ≅ G := by
  let : IsIso (M.multiplication i N hdisj) :=
    hG.central_isogeny_isIso (M.group ⊗ N.group) (M.multiplication i N hdisj)
      (DirectProduct.isSemisimple_tensor M.semisimple N.semisimple)
      (M.multiplication_isCentralIsogeny i N hdisj hG.isSemisimple hsplit hmax hcover)
  exact asIso (M.multiplication i N hdisj)

/-- The isomorphism has precisely the original subgroup multiplication as
its underlying forward morphism. -/
@[simp] theorem multiplicationIso_hom (hG : IsSimplyConnected G)
    (hsplit : IsSplitSubtorus i) (hmax : IsMaximalTorus i)
    (hcover : s ∪ t = relativeRoots i) :
    (M.multiplicationIso i N hdisj hG hsplit hmax hcover).hom =
      M.multiplication i N hdisj := rfl

end Langlands.GroupScheme.RootPartitionNormalModel
