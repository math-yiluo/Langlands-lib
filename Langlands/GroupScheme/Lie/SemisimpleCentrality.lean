import Langlands.GroupScheme.Lie.SemisimpleCentralizerSmooth
import Langlands.GroupScheme.Lie.SubgroupEqualityProof

/-! # Central semisimple Lie elements are fixed by the whole group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

variable {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]

/-- The full actual centralizer is equivalent to vanishing of the global
coordinate derivation of infinitesimal conjugation. -/
theorem elementCentralizer_eq_top_iff_conjugationDerivation_eq_zero
    (X : lieKernel G k) :
    elementCentralizer G X = ⊤ ↔ conjugationDerivation G X = 0 := by
  constructor
  · intro h
    have hu : universalPoint G ∈ (elementCentralizer G X).carrier _ := by
      rw [h]
      exact Subgroup.mem_top _
    have hc := (infinitesimalConjugate_eq_constant_iff_coordinates G X
      (universalPoint G)).mp
        ((infinitesimalConjugate_eq_constant_iff G X (universalPoint G)).mpr hu)
    ext c
    have hucoord := DFunLike.congr_fun (pointCoordinates_universalPoint G)
      (conjugationDerivation G X c)
    exact hucoord.symm.trans (hc c)
  · intro h
    apply SubgroupFunctor.ext
    intro T
    apply Subgroup.ext
    intro g
    constructor
    · intro _
      exact Subgroup.mem_top _
    intro _ A _ _ a
    apply (commute_constant_iff G (a ≫ g) _).mpr
    apply (mem_elementCentralizer_affine_iff G X (a ≫ g)).mp
    apply (infinitesimalConjugate_eq_constant_iff G X (a ≫ g)).mp
    apply (infinitesimalConjugate_eq_constant_iff_coordinates G X (a ≫ g)).mpr
    intro c
    simp only [h, Derivation.zero_apply, map_zero]

/-- The whole-group centralizer has the whole tangent submodule. -/
theorem elementCentralizerLie_eq_top_of_elementCentralizer_eq_top
    (X : lieKernel G k) (h : elementCentralizer G X = ⊤) :
    elementCentralizerLie G X = ⊤ := by
  apply top_unique
  intro Y _
  change Y.toMul.val ∈ (elementCentralizer G X).carrier _
  rw [h]
  exact Subgroup.mem_top _

variable [Smooth G.X.hom] [ConnectedSpace G.X.left]

/-- Smoothness of the semisimple centralizer upgrades full tangent space to
the whole group, on every scheme test. -/
theorem elementCentralizer_eq_top_of_isSemisimple_of_lie_eq_top
    {X : lieKernel G k} (hX : IsSemisimpleElement G X)
    (hLie : elementCentralizerLie G X = ⊤) :
    elementCentralizer G X = ⊤ := by
  let C := elementCentralizerGroup G X
  let j : C ⟶ G := elementCentralizerGroupι G X
  have hrep : (elementCentralizer G X).IsRepresentedBy j :=
    elementCentralizerGroup_isRepresentedBy G X
  have hj : IsClosedSubgroup j := isClosedSubgroup_elementCentralizerGroupι G X
  have : Smooth C.X.hom := smooth_elementCentralizerGroup G hX
  have hrange : LinearMap.range (targetMapLinear j k) = ⊤ := by
    rw [← (elementCentralizer G X).lie_eq_range k j hrep]
    exact hLie
  have heq : SubgroupFunctor.range j = ⊤ := by
    apply lieSubgroupEquality k G C j hj
    intro Y
    obtain ⟨Z, hZ⟩ := LinearMap.range_eq_top.mp hrange (Additive.ofMul Y)
    exact ⟨Z.toMul, congrArg (fun W => W.toMul.val) hZ⟩
  exact hrep.2.symm.trans heq

/-- For semisimple elements, Lie centrality agrees with invariance under the
whole actual adjoint action. -/
theorem elementCentralizerLie_eq_top_iff_elementCentralizer_eq_top
    {X : lieKernel G k} (hX : IsSemisimpleElement G X) :
    elementCentralizerLie G X = ⊤ ↔ elementCentralizer G X = ⊤ :=
  ⟨elementCentralizer_eq_top_of_isSemisimple_of_lie_eq_top G hX,
    elementCentralizerLie_eq_top_of_elementCentralizer_eq_top G X⟩

/-- For a semisimple element, infinitesimal Lie centrality forces the global
conjugation derivation to vanish. -/
theorem elementCentralizerLie_eq_top_iff_conjugationDerivation_eq_zero
    {X : lieKernel G k} (hX : IsSemisimpleElement G X) :
    elementCentralizerLie G X = ⊤ ↔ conjugationDerivation G X = 0 :=
  (elementCentralizerLie_eq_top_iff_elementCentralizer_eq_top G hX).trans
    (elementCentralizer_eq_top_iff_conjugationDerivation_eq_zero G X)

end Langlands.GroupScheme.Lie

namespace Langlands.GroupScheme

/-- Over an arbitrary field, a semisimple Lie element of a smooth connected
affine group has full Lie centralizer exactly when its actual centralizer is
the whole group. -/
def SemisimpleCentralityStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (X : lieKernel G k), Lie.IsSemisimpleElement G X →
      (Lie.elementCentralizerLie G X = ⊤ ↔ Lie.elementCentralizer G X = ⊤)

theorem semisimpleCentrality : SemisimpleCentralityStatement.{u} := by
  intro k _ G _ _ _ X hX
  exact Lie.elementCentralizerLie_eq_top_iff_elementCentralizer_eq_top G hX

end Langlands.GroupScheme
