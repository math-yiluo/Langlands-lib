import Langlands.GroupScheme.Rational.SplitSolvableTorusDomination
import Langlands.GroupScheme.Rational.TorusGeneratedSplitGeometricRadicalProof
import Langlands.GroupScheme.Unipotent.MultiplicativeTrivialityProof
import Langlands.GroupScheme.Torus.UnipotentHomNonsplit
import Langlands.GroupScheme.Torus.MultiplicativeTypeGeometry
import Langlands.GroupScheme.Torus.MaximalTransport
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.FppfHomDescent

/-! # The canonical extension of a split solvable group

Let `G` be a split solvable group over a field, with a closed unipotent subgroup `U` and an fppf
quotient `q : G → D` by it onto a group of multiplicative type. We compare this extension with
the one supplied by `splitTorusDominatedSolvableQuotient`, whose kernel `U'` is smooth,
connected, unipotent and (by the split-torus domination of `G`) split, and whose quotient `D'`
is a torus. The two kernels have the same range, so `D ≅ D'` is a torus, which is split
because the domination of `G` descends to `D`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- If the kernel of `q` is contained in the kernel of `q'`, then the inclusion of the kernel of
`q` composed with `q'` is trivial. -/
theorem kernelι_comp_eq_zero_of_range_le {S : Scheme.{u}} {G Q Q' : GroupScheme S}
    (q : G ⟶ Q) (q' : G ⟶ Q')
    (h : SubgroupFunctor.range (kernelι q) ≤ SubgroupFunctor.range (kernelι q')) :
    kernelι q ≫ q' = 0 := by
  apply Grp.hom_ext
  change (kernelι q).hom.hom ≫ q'.hom.hom = 1
  apply (mem_range_kernelι_iff q' _).mp
  apply SubgroupFunctor.le_def.mp h (kernel q).X
  exact SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩

/-- Two fppf quotient maps out of the same group with the same kernel have isomorphic targets,
compatibly with the quotient maps. -/
def fppfQuotientIso {S : Scheme.{u}} {G Q Q' : GroupScheme S} (q : G ⟶ Q) (q' : G ⟶ Q')
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]
    [Flat q'.hom.hom.left] [Surjective q'.hom.hom.left]
    [LocallyOfFinitePresentation q'.hom.hom.left]
    (h : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range (kernelι q')) : Q ≅ Q' where
  hom := FppfHomDescent.hom q q' (kernelι_comp_eq_zero_of_range_le q q' h.le)
  inv := FppfHomDescent.hom q' q (kernelι_comp_eq_zero_of_range_le q' q h.ge)
  hom_inv_id := by
    have hk := kernelι_comp_eq_zero_of_range_le q q le_rfl
    rw [FppfHomDescent.unique q q hk (_ ≫ _) (by
        rw [FppfHomDescent.fac_assoc, FppfHomDescent.fac]),
      ← FppfHomDescent.unique q q hk (𝟙 _) (Category.comp_id _)]
  inv_hom_id := by
    have hk := kernelι_comp_eq_zero_of_range_le q' q' le_rfl
    rw [FppfHomDescent.unique q' q' hk (_ ≫ _) (by
        rw [FppfHomDescent.fac_assoc, FppfHomDescent.fac]),
      ← FppfHomDescent.unique q' q' hk (𝟙 _) (Category.comp_id _)]

variable {k : Type u} [Field k]

/-- Structure of the canonical extension of a split solvable group: its unipotent kernel has
the same range as a smooth connected split unipotent closed subgroup, and its
multiplicative-type quotient is a split torus. -/
theorem IsSplitSolvableGroupScheme.canonicalExtension_structure
    {G U D : GroupScheme (Spec (CommRingCat.of k))} (hG : IsSplitSolvableGroupScheme G)
    (i : U ⟶ G) (q : G ⟶ D) (hi : IsClosedSubgroup i) (hU : IsUnipotent U)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hD : IsMultiplicativeType D) :
    ∃ (U' : GroupScheme (Spec (CommRingCat.of k))) (i' : U' ⟶ G),
      IsClosedSubgroup i' ∧ Smooth U'.X.hom ∧ ConnectedSpace U'.X.left ∧ IsUnipotent U' ∧
        RelativeRoot.IsSplitUnipotent U' ∧
        SubgroupFunctor.range i' = SubgroupFunctor.range i ∧ IsSplitTorus D := by
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : ConnectedSpace G.X.left := hG.connectedSpace
  have hdom := hG.hasPointedSplitTorusDomination
  obtain ⟨U', D', i', q', hi', hU's, hU'c, hU'u, hq', hD'⟩ :=
    splitTorusDominatedSolvableQuotient k G hG.isSolvableGroupScheme hdom
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsClosedImmersion i'.hom.hom.left := hi'
  have : Smooth U'.X.hom := hU's
  have : IsAffineHom U.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : IsAffineHom U'.X.hom := by
    rw [← Over.w i'.hom.hom]
    infer_instance
  have : IsAffineHom D.X.hom := hD.isAffineHom
  have : LocallyOfFiniteType D.X.hom := hD.locallyOfFiniteType
  have h1 : SubgroupFunctor.range i ≤ SubgroupFunctor.range i' := by
    rw [SubgroupFunctor.le_def]
    intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    rw [← hq'.2.2.2]
    apply (mem_range_kernelι_iff q' _).mpr
    rw [Category.assoc, ← Grp.comp_hom_hom]
    exact hU.comp_eq_one_of_isTorus hD' (i ≫ q') T y
  have h2 : SubgroupFunctor.range i' ≤ SubgroupFunctor.range i := by
    rw [SubgroupFunctor.le_def]
    intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    rw [← hq.2.2.2]
    apply (mem_range_kernelι_iff q _).mpr
    have hbot := ((unipotentMultiplicativeTriviality k).2.2 U' D hU'u hD).1 (i' ≫ q)
    have hm : y ≫ (i' ≫ q).hom.hom ∈ (SubgroupFunctor.range (i' ≫ q)).carrier T :=
      SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩
    rw [hbot, SubgroupFunctor.bot_carrier, Subgroup.mem_bot, Grp.comp_hom_hom] at hm
    rw [Category.assoc]
    exact hm
  have hrange : SubgroupFunctor.range i' = SubgroupFunctor.range i := le_antisymm h2 h1
  have : Flat q.hom.hom.left := hq.1
  have : Surjective q.hom.hom.left := hq.2.1
  have : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  have : Flat q'.hom.hom.left := hq'.1
  have : Surjective q'.hom.hom.left := hq'.2.1
  have : LocallyOfFinitePresentation q'.hom.hom.left := hq'.2.2.1
  have hDtorus : IsTorus D :=
    IsTorus.of_iso (fppfQuotientIso q q' (by rw [hq.2.2.2, hq'.2.2.2, hrange])) hD'
  have hU'split : RelativeRoot.IsSplitUnipotent U' :=
    TorusKernelDomination.representative_isSplitUnipotent_of_stableVector
      unipotentSplitTorusDomination RelativeRoot.splitUnipotentStableVectorSubgroup
      i' hi' hU's hU'c hU'u q' hq' hD' hdom
  exact ⟨U', i', hi', hU's, hU'c, hU'u, hU'split, hrange, (hdom.postcomp q).isSplitTorus hDtorus⟩

end Langlands.GroupScheme
