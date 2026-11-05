import Langlands.GroupScheme.Rational.RootSubgroupRationalNontrivial
import Langlands.GroupScheme.Rational.RootSubgroupPositive
import Langlands.GroupScheme.Rational.QuotientActionComparisonProof
import Langlands.GroupScheme.Rational.CentralizerRootSupport
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.Dynamic.LeviCocharacterCombination
import Langlands.GroupScheme.Dynamic.Uniqueness
import Langlands.GroupScheme.Rational.ParabolicPointConjugation

/-! # Rational points detect centralizers of cocharacters of a common split torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

section Root

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (alpha : characterLattice T) (zeta : cocharacterLattice T)

/-- A root subgroup centralizes a cocharacter annihilated by its character,
on every test scheme. -/
theorem RelativeRoot.subgroup_le_dynamicCentralizer_of_pairing_eq_zero
    (hzero : latticePairing T alpha zeta = 0) :
    RelativeRoot.subgroup i alpha ≤
      Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) := by
  have hz : zeta ≫ alpha = 0 := by
    rw [eq_gmEndEquiv_zsmul k (zeta ≫ alpha)]
    change latticePairing T alpha zeta • 𝟙 _ = 0
    rw [hzero, zero_zsmul]
  intro U g hg
  obtain ⟨e, he, _⟩ := hg
  have hker := RelativeRoot.mem_kernelCentralizer_of_isOrbitExtension i alpha he
  rw [← torusCentralizer_gm_eq_dynamicCentralizer, mem_torusCentralizer]
  intro V b t
  let s := t ≫ (CommGroupScheme.groupHom zeta).hom.hom
  have hs : s ≫ (CommGroupScheme.groupHom alpha).hom.hom = 1 := by
    dsimp only [s]
    rw [← comp_groupHom_comp, hz, comp_groupHom_zero]
  let c : V ⟶ (RelativeRoot.characterKernel alpha).X :=
    (kernelPointsEquiv (CommGroupScheme.groupHom alpha) V).symm ⟨s, hs⟩
  have hc : c ≫ (RelativeRoot.characterKernelι alpha).hom.hom = s :=
    congrArg Subtype.val
      ((kernelPointsEquiv (CommGroupScheme.groupHom alpha) V).apply_symm_apply ⟨s, hs⟩)
  have h := (RelativeRoot.mem_kernelCentralizer i alpha).mp hker V b c
  simpa only [Grp.comp_hom_hom, ← Category.assoc, hc] using h

end Root

section Detection

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (zeta eta : cocharacterLattice T)

include hT

/-- Inclusion of the rational points of two cocharacter centralizers forces
inclusion of their actual zero-root supports. -/
theorem root_zero_imp_of_dynamicCentralizer_rationalPoints_le
    (hpoints :
      (Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)).rationalPoints ≤
        (Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i)).rationalPoints)
    {alpha : characterLattice T} (halpha : alpha ∈ relativeRoots i)
    (hzero : latticePairing T alpha zeta = 0) :
    latticePairing T alpha eta = 0 := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨x, hx, hx1⟩ := RelativeRoot.exists_rootPoint_actual hT i halpha
  have hxc :
      x ∈ (Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i)).carrier
        (Over.mk (𝟙 _)) :=
    hpoints (RelativeRoot.subgroup_le_dynamicCentralizer_of_pairing_eq_zero
      i alpha zeta hzero _ hx)
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hxneg :
        x ∈ (Dynamic.centralizer (CommGroupScheme.groupHom (-eta) ≫ i)).carrier
          (Over.mk (𝟙 _)) := by
      rw [groupHom_neg_comp_eq_oppositeCocharacter i eta]
      exact Dynamic.centralizer_le_precomp _
        (CommGroupScheme.groupHom (Gm.powerHom _ (-1))) _ hxc
    exact hx1 (Dynamic.eq_one_of_mem_centralizer_of_mem_unipotent
      (CommGroupScheme.groupHom (-eta) ≫ i)
      (fun _ _ _ _ h h' => h.unique _ h') hxneg
      (RelativeRoot.subgroup_le_dynamicUnipotent i (-eta) (by simpa using neg_pos.mpr hneg) _ hx))
  · exact hx1 (Dynamic.eq_one_of_mem_centralizer_of_mem_unipotent
      (CommGroupScheme.groupHom eta ≫ i)
      (fun _ _ _ _ h h' => h.unique _ h') hxc
      (RelativeRoot.subgroup_le_dynamicUnipotent i eta hpos _ hx))

variable [ConnectedSpace G.X.left]

/-- For two cocharacters of a common split torus in a smooth connected affine
group, inclusion on rational points implies containment on every test scheme. -/
theorem dynamicCentralizer_le_of_rationalPoints_le
    (hpoints :
      (Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)).rationalPoints ≤
        (Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i)).rationalPoints) :
    Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) ≤
      Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i) :=
  dynamicCentralizer_le_of_root_zero_imp dynamicConnected hT i zeta eta
    (fun _ halpha hzero =>
      root_zero_imp_of_dynamicCentralizer_rationalPoints_le hT i zeta eta hpoints halpha hzero)

/-- Equality of these rational-point subgroups detects equality of their
actual cocharacter-centralizer functors. -/
theorem dynamicCentralizer_eq_of_rationalPoints_eq
    (hpoints :
      (Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)).rationalPoints =
        (Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i)).rationalPoints) :
    Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) =
      Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i) :=
  le_antisymm
    (dynamicCentralizer_le_of_rationalPoints_le hT i zeta eta (le_of_eq hpoints))
    (dynamicCentralizer_le_of_rationalPoints_le hT i eta zeta (le_of_eq hpoints.symm))

/-- Evaluation on rational points embeds the poset of cocharacter-centralizer
functors of the given split torus into the rational-point subgroup lattice. -/
def cocharacterCentralizerRationalPointsOrderEmbedding :
    {F : SubgroupFunctor G //
      ∃ zeta : cocharacterLattice T,
        F = Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)} ↪o
      Subgroup (rationalPoints G) where
  toFun F := F.val.rationalPoints
  inj' := by
    intro A B h
    obtain ⟨alpha, halpha⟩ := A.property
    obtain ⟨beta, hbeta⟩ := B.property
    apply Subtype.ext
    change A.val = B.val
    rw [halpha, hbeta]
    apply dynamicCentralizer_eq_of_rationalPoints_eq hT i alpha beta
    simpa only [← halpha, ← hbeta] using h
  map_rel_iff' := by
    intro A B
    obtain ⟨alpha, halpha⟩ := A.property
    obtain ⟨beta, hbeta⟩ := B.property
    change A.val.rationalPoints ≤ B.val.rationalPoints ↔ A.val ≤ B.val
    rw [halpha, hbeta]
    exact ⟨dynamicCentralizer_le_of_rationalPoints_le hT i alpha beta,
      fun h => h _⟩

end Detection

end Langlands.GroupScheme
