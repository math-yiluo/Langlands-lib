import Langlands.GroupScheme.SubgroupFunctor.OpenCellNormalizer
import Langlands.GroupScheme.NormalizerRepresentability
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # All-test self-normalization from rational points and an open cell -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G U P : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (iU : U ⟶ G) (iP : P ⟶ G) (hiP : IsClosedSubgroup iP)
  (hrat : ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
    g ∈ (range iP).normalizer.carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) →
      g ∈ (range iP).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))))

include hiP hrat in
/-- Rational normalizer membership puts every normalizer-valued test map in the
open multiplication cell. The represented normalizer need not be reduced. -/
theorem range_subset_cell_of_rational_mem
    (hopen : IsOpenImmersion (cellMultiplication iU iP).left)
    {T : Over (Spec (CommRingCat.of k))} {g : T ⟶ G.X}
    (hg : g ∈ (range iP).normalizer.carrier T) :
    Set.range g.left ⊆ Set.range (cellMultiplication iU iP).left := by
  have : IsOpenImmersion (cellMultiplication iU iP).left := hopen
  obtain ⟨N, n, hnclosed, hn⟩ :=
    (hasClosedRepresentative_normalizer_centralizer_range iP hiP).1
  have : IsClosedImmersion n.hom.hom.left := hnclosed
  have : LocallyOfFiniteType N.X.hom := by
    rw [← Over.w n.hom.hom]
    infer_instance
  have : JacobsonSpace N.X.left := LocallyOfFiniteType.jacobsonSpace N.X.hom
  have hclosed : IsClosed
      (n.hom.hom.left ⁻¹' (Set.range (cellMultiplication iU iP).left)ᶜ) :=
    ((cellMultiplication iU iP).left.isOpenEmbedding.isOpen_range.isClosed_compl).preimage
      n.hom.hom.left.continuous
  have hnrange : Set.range n.hom.hom.left ⊆
      Set.range (cellMultiplication iU iP).left := by
    rintro _ ⟨x, rfl⟩
    by_contra hx
    obtain ⟨y, hy, hyclosed⟩ :=
      nonempty_inter_closedPoints ⟨x, hx⟩ hclosed.isLocallyClosed
    let a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ N.X :=
      Over.homMk (pointOfClosedPoint N.X.hom y hyclosed)
        (pointOfClosedPoint_comp N.X.hom y hyclosed)
    have han : a ≫ n.hom.hom ∈
        (range iP).normalizer.carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
      rw [← hn.2]
      exact ⟨a, rfl⟩
    obtain ⟨p, hp⟩ := mem_range.mp (hrat _ han)
    have hpimage : n.hom.hom.left y ∈ Set.range iP.hom.hom.left := by
      refine ⟨p.left (IsLocalRing.closedPoint k), ?_⟩
      have he := congrArg
        (fun q : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X =>
          q.left (IsLocalRing.closedPoint k)) hp
      change iP.hom.hom.left (p.left (IsLocalRing.closedPoint k)) =
        n.hom.hom.left
          (pointOfClosedPoint N.X.hom y hyclosed (IsLocalRing.closedPoint k)) at he
      simpa only [pointOfClosedPoint_apply] using he
    exact hy (range_right_subset_cell iU iP hpimage)
  have hg' : g ∈ (range n).carrier T := by
    rw [hn.2]
    exact hg
  obtain ⟨a, ha⟩ := mem_range.mp hg'
  rintro _ ⟨t, rfl⟩
  apply hnrange
  refine ⟨a.left t, ?_⟩
  exact congrArg (fun q : T ⟶ G.X => q.left t) ha

include hiP hrat in
/-- Over an algebraically closed field, rational normalizer membership and an
open cell with all-test separation imply equality of the full subgroup functors. -/
theorem normalizer_eq_of_rational_points_and_open_cell
    (hsep : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X),
      g ∈ (range iU).carrier T → g ∈ (range iP).normalizer.carrier T → g = 1)
    (hopen : IsOpenImmersion (cellMultiplication iU iP).left) :
    (range iP).normalizer = range iP := by
  apply le_antisymm
  · intro T g hg
    exact mem_range_of_mem_normalizer_of_range_subset_cell iU iP hsep hopen hg
      (range_subset_cell_of_rational_mem iU iP hiP hrat hopen hg)
  · exact le_normalizer (range iP)

include hiP hrat in
/-- The open-cell equality lifts normalizer points to the original right subgroup. -/
def normalizerPointsEquivOfRationalOpenCell
    (hsep : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X),
      g ∈ (range iU).carrier T → g ∈ (range iP).normalizer.carrier T → g = 1)
    (hopen : IsOpenImmersion (cellMultiplication iU iP).left)
    (T : Over (Spec (CommRingCat.of k))) :
    (range iP).normalizer.carrier T ≃* (T ⟶ P.X) := by
  have : IsClosedImmersion iP.hom.hom.left := hiP
  have : Mono iP.hom.hom := Over.mono_of_mono_left _
  exact (MulEquiv.subgroupCongr
    (congrArg (fun F : SubgroupFunctor G => F.carrier T)
      (normalizer_eq_of_rational_points_and_open_cell iU iP hiP hrat hsep hopen))).trans
    ((show (range iP).IsRepresentedBy iP from ⟨inferInstance, rfl⟩).pointsEquiv T).symm

include hiP hrat in
/-- The lifted point composes with the specified inclusion to the original point. -/
theorem normalizerPointsEquivOfRationalOpenCell_comp
    (hsep : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X),
      g ∈ (range iU).carrier T → g ∈ (range iP).normalizer.carrier T → g = 1)
    (hopen : IsOpenImmersion (cellMultiplication iU iP).left)
    (T : Over (Spec (CommRingCat.of k))) (g : (range iP).normalizer.carrier T) :
    normalizerPointsEquivOfRationalOpenCell iU iP hiP hrat hsep hopen T g ≫
      iP.hom.hom = g := by
  have : IsClosedImmersion iP.hom.hom.left := hiP
  have : Mono iP.hom.hom := Over.mono_of_mono_left _
  exact (show (range iP).IsRepresentedBy iP from
    ⟨inferInstance, rfl⟩).pointsEquiv_symm_comp _

end Langlands.GroupScheme.SubgroupFunctor
