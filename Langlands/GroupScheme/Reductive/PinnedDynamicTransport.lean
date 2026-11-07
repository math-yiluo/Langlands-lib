import Langlands.GroupScheme.Reductive.PinnedIsomorphismFunctoriality
import Langlands.GroupScheme.Reductive.SplitBorelCell
import Langlands.GroupScheme.Rational.RelativeRootSignInclusionsProof
import Langlands.GroupScheme.Rational.RelativeTitsNondegeneracy

/-! # Dynamic subgroup transport under actual pinned isomorphisms -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitPinning.Iso

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {p : SplitPinning G} {q : SplitPinning H} (f : SplitPinning.Iso p q)

/-- Complete pinned isomorphisms preserve the height of every root. -/
theorem height_eq (a : p.rootIndex) :
    q.base.height (f.indexEquiv a) = p.base.height a := by
  classical
  obtain ⟨c, -, -, hc⟩ := p.base.exists_root_eq_sum_int a
  have hroot : q.rootDatum.root (f.indexEquiv a) =
      ∑ b ∈ q.base.support, c (f.indexEquiv.symm b) • q.rootDatum.root b := by
    calc
      q.rootDatum.root (f.indexEquiv a) =
          characterLattice.congr f.torusIso (p.rootDatum.root a) := (f.root_eq a).symm
      _ = ∑ b ∈ p.base.support, c b • q.rootDatum.root (f.indexEquiv b) := by
        rw [hc, map_sum]
        exact Finset.sum_congr rfl fun b _ => by rw [map_zsmul, f.root_eq]
      _ = ∑ b ∈ q.base.support, c (f.indexEquiv.symm b) • q.rootDatum.root b :=
        Finset.sum_equiv f.indexEquiv f.simple_iff
          (fun b _ => by rw [Equiv.symm_apply_apply])
  rw [RootPairing.Base.height_eq_sum hroot, RootPairing.Base.height_eq_sum hc]
  exact (Finset.sum_equiv f.indexEquiv f.simple_iff
    (fun b _ => by rw [Equiv.symm_apply_apply])).symm

/-- Complete pinned isomorphisms preserve the positive roots. -/
theorem isPos_iff (a : p.rootIndex) :
    q.base.IsPos (f.indexEquiv a) ↔ p.base.IsPos a := by
  rw [RootPairing.Base.isPos_iff, RootPairing.Base.isPos_iff, f.height_eq]

/-- The inclusion square transports every torus cocharacter as an actual map. -/
theorem cocharacter_comp (ν : cocharacterLattice p.torus) :
    (CommGroupScheme.groupHom ν ≫ p.inclusion) ≫ f.groupIso.hom =
      CommGroupScheme.groupHom (cocharacterLattice.congr f.torusIso ν) ≫ q.inclusion := by
  rw [Category.assoc, f.square, ← Category.assoc]
  rfl

/-- The transported chosen cocharacter and the target chosen cocharacter have
the same nonnegative root pairings. -/
theorem positiveCocharacter_nonneg_iff (a : q.rootIndex) :
    0 ≤ latticePairing q.torus (q.rootDatum.root a)
        (cocharacterLattice.congr f.torusIso p.positiveCocharacter) ↔
      0 ≤ latticePairing q.torus (q.rootDatum.root a) q.positiveCocharacter := by
  obtain ⟨a, rfl⟩ := f.indexEquiv.surjective a
  rw [← f.root_eq, latticePairing_congr, f.root_eq,
    p.latticePairing_root_positiveCocharacter, q.latticePairing_root_positiveCocharacter,
    f.height_eq]
  exact (mul_nonneg_iff_of_pos_left p.positiveScale_pos).trans
    (mul_nonneg_iff_of_pos_left q.positiveScale_pos).symm

/-- The transported chosen cocharacter and the target chosen cocharacter have
the same positive root pairings. -/
theorem positiveCocharacter_pos_iff (a : q.rootIndex) :
    0 < latticePairing q.torus (q.rootDatum.root a)
        (cocharacterLattice.congr f.torusIso p.positiveCocharacter) ↔
      0 < latticePairing q.torus (q.rootDatum.root a) q.positiveCocharacter := by
  obtain ⟨a, rfl⟩ := f.indexEquiv.surjective a
  rw [← f.root_eq, latticePairing_congr, f.root_eq,
    p.latticePairing_root_positiveCocharacter, q.latticePairing_root_positiveCocharacter,
    f.height_eq]
  exact (mul_pos_iff_of_pos_left p.positiveScale_pos).trans
    (mul_pos_iff_of_pos_left q.positiveScale_pos).symm

/-- The dynamic positive unipotent subgroup is carried to the target one on
every relative scheme test. -/
theorem unipotent_positiveGm_comp :
    Dynamic.unipotent (p.positiveGm ≫ f.groupIso.hom) =
      Dynamic.unipotent q.positiveGm := by
  change Dynamic.unipotent
    ((CommGroupScheme.groupHom p.positiveCocharacter ≫ p.inclusion) ≫ f.groupIso.hom) = _
  rw [f.cocharacter_comp]
  have hsign (α : characterLattice q.torus) (hα : α ∈ relativeRoots q.inclusion) :
      0 < latticePairing q.torus α
          (cocharacterLattice.congr f.torusIso p.positiveCocharacter) ↔
        0 < latticePairing q.torus α q.positiveCocharacter := by
    obtain ⟨a, rfl⟩ : ∃ a, q.rootDatum.root a = α := by
      rw [← Set.mem_range, q.isRootDatum.2.1]
      exact hα
    exact f.positiveCocharacter_pos_iff a
  have h := relativeRootSignInclusions k H q.isConnectedReductive q.torus q.inclusion
    (q.isMaximalTorus.isMaximalSplitTorus q.isSplitTorus)
  apply le_antisymm
  · exact (h _ _).2 fun α hα => (hsign α hα).mp
  · exact (h _ _).2 fun α hα => (hsign α hα).mpr

/-- The negative dynamic parabolic is carried to the target one on every
relative scheme test. -/
theorem parabolic_opposite_positiveGm_comp :
    Dynamic.parabolic (Dynamic.oppositeCocharacter p.positiveGm ≫ f.groupIso.hom) =
      Dynamic.parabolic (Dynamic.oppositeCocharacter q.positiveGm) := by
  change Dynamic.parabolic
    (Dynamic.oppositeCocharacter
      (CommGroupScheme.groupHom p.positiveCocharacter ≫ p.inclusion) ≫ f.groupIso.hom) =
    Dynamic.parabolic
      (Dynamic.oppositeCocharacter
        (CommGroupScheme.groupHom q.positiveCocharacter ≫ q.inclusion))
  rw [← groupHom_neg_comp_eq_oppositeCocharacter,
    ← groupHom_neg_comp_eq_oppositeCocharacter, f.cocharacter_comp]
  have hsign (α : characterLattice q.torus) (hα : α ∈ relativeRoots q.inclusion) :
      0 ≤ latticePairing q.torus α
          (cocharacterLattice.congr f.torusIso (-p.positiveCocharacter)) ↔
        0 ≤ latticePairing q.torus α (-q.positiveCocharacter) := by
    obtain ⟨a, rfl⟩ : ∃ a, q.rootDatum.root a = α := by
      rw [← Set.mem_range, q.isRootDatum.2.1]
      exact hα
    simpa only [map_neg, neg_nonneg, not_lt] using
      not_congr (f.positiveCocharacter_pos_iff a)
  have h := relativeRootSignInclusions k H q.isConnectedReductive q.torus q.inclusion
    (q.isMaximalTorus.isMaximalSplitTorus q.isSplitTorus)
  apply le_antisymm
  · exact (h _ _).1.mpr fun α hα => (hsign α hα).mp
  · exact (h _ _).1.mpr fun α hα => (hsign α hα).mpr

/-- The transported negative-parabolic inclusion represents the target
negative dynamic parabolic. -/
theorem isRepresentedBy_negativeBorelHom_comp :
    (Dynamic.parabolic (Dynamic.oppositeCocharacter q.positiveGm)).IsRepresentedBy
      (p.negativeBorelHom ≫ f.groupIso.hom) := by
  have h := p.isRepresentedBy_negativeBorelHom.comp_iso f.groupIso
  have heq :
      (Dynamic.parabolic (Dynamic.oppositeCocharacter p.positiveGm)).comap f.groupIso.inv =
        Dynamic.parabolic (Dynamic.oppositeCocharacter q.positiveGm) := by
    rw [← f.parabolic_opposite_positiveGm_comp]
    simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      (Dynamic.parabolic_eq_comap_of_iso
        (Dynamic.oppositeCocharacter p.positiveGm ≫ f.groupIso.hom) f.groupIso.symm).symm
  rwa [heq] at h

/-- The transported positive-unipotent inclusion represents the target
positive dynamic unipotent subgroup. -/
theorem isRepresentedBy_positiveUnipotentHom_comp :
    (Dynamic.unipotent q.positiveGm).IsRepresentedBy
      (p.positiveUnipotentHom ≫ f.groupIso.hom) := by
  have h := p.isRepresentedBy_positiveUnipotentHom.comp_iso f.groupIso
  have heq : (Dynamic.unipotent p.positiveGm).comap f.groupIso.inv =
      Dynamic.unipotent q.positiveGm := by
    rw [← f.unipotent_positiveGm_comp]
    simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      (Dynamic.unipotent_eq_comap_of_iso
        (p.positiveGm ≫ f.groupIso.hom) f.groupIso.symm).symm
  rwa [heq] at h

/-- The actual isomorphism of the represented negative dynamic parabolics. -/
def negativeBorelIso : p.negativeBorel ≅ q.negativeBorel :=
  f.isRepresentedBy_negativeBorelHom_comp.isoOfIsRepresentedBy
    q.isRepresentedBy_negativeBorelHom

theorem negativeBorelIso_hom_comp :
    f.negativeBorelIso.hom ≫ q.negativeBorelHom =
      p.negativeBorelHom ≫ f.groupIso.hom :=
  f.isRepresentedBy_negativeBorelHom_comp.isoOfIsRepresentedBy_hom_comp
    q.isRepresentedBy_negativeBorelHom

/-- The actual isomorphism of the represented positive dynamic unipotent groups. -/
def positiveUnipotentIso : p.positiveUnipotent ≅ q.positiveUnipotent :=
  f.isRepresentedBy_positiveUnipotentHom_comp.isoOfIsRepresentedBy
    q.isRepresentedBy_positiveUnipotentHom

theorem positiveUnipotentIso_hom_comp :
    f.positiveUnipotentIso.hom ≫ q.positiveUnipotentHom =
      p.positiveUnipotentHom ≫ f.groupIso.hom :=
  f.isRepresentedBy_positiveUnipotentHom_comp.isoOfIsRepresentedBy_hom_comp
    q.isRepresentedBy_positiveUnipotentHom

/-- The negative dynamic parabolic has the same range after transport. -/
theorem range_negativeBorelHom_comp :
    SubgroupFunctor.range (p.negativeBorelHom ≫ f.groupIso.hom) =
      SubgroupFunctor.range q.negativeBorelHom := by
  rw [← f.negativeBorelIso_hom_comp]
  exact SubgroupFunctor.range_iso_comp f.negativeBorelIso _

/-- The positive dynamic unipotent subgroup has the same range after transport. -/
theorem range_positiveUnipotentHom_comp :
    SubgroupFunctor.range (p.positiveUnipotentHom ≫ f.groupIso.hom) =
      SubgroupFunctor.range q.positiveUnipotentHom := by
  rw [← f.positiveUnipotentIso_hom_comp]
  exact SubgroupFunctor.range_iso_comp f.positiveUnipotentIso _

/-- The negative-parabolic range square persists on every relative scheme test
following arbitrary scheme base change. -/
theorem range_baseChange_negativeBorelHom_comp {S : Scheme.{u}}
    (b : S ⟶ Spec (CommRingCat.of k)) :
    SubgroupFunctor.range
        ((GroupScheme.baseChange b).map p.negativeBorelHom ≫
          (GroupScheme.baseChange b).map f.groupIso.hom) =
      SubgroupFunctor.range ((GroupScheme.baseChange b).map q.negativeBorelHom) := by
  rw [← Functor.map_comp, ← f.negativeBorelIso_hom_comp, Functor.map_comp]
  exact SubgroupFunctor.range_iso_comp
    ((GroupScheme.baseChange b).mapIso f.negativeBorelIso) _

/-- The positive-unipotent range square persists on every relative scheme test
following arbitrary scheme base change. -/
theorem range_baseChange_positiveUnipotentHom_comp {S : Scheme.{u}}
    (b : S ⟶ Spec (CommRingCat.of k)) :
    SubgroupFunctor.range
        ((GroupScheme.baseChange b).map p.positiveUnipotentHom ≫
          (GroupScheme.baseChange b).map f.groupIso.hom) =
      SubgroupFunctor.range ((GroupScheme.baseChange b).map q.positiveUnipotentHom) := by
  rw [← Functor.map_comp, ← f.positiveUnipotentIso_hom_comp, Functor.map_comp]
  exact SubgroupFunctor.range_iso_comp
    ((GroupScheme.baseChange b).mapIso f.positiveUnipotentIso) _

end Langlands.GroupScheme.SplitPinning.Iso
