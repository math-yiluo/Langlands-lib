import Langlands.GroupScheme.Descent.AffineDatumMorphisms
import Langlands.GroupScheme.Descent.ComponentCoverLifts
import Langlands.GroupScheme.SubgroupBaseChange

/-! # Effective affine descent of monic subgroup inclusions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Descent

variable {B S : Scheme.{u}} {p : S ⟶ B} {H G : GroupScheme S} {i : H ⟶ G}
    [Mono i.hom.hom]

/-- A lift of the ambient overlap through a monic inclusion satisfies the cocycle. -/
theorem cocycle_of_monicSubgroup_lift (D : Datum p G)
    (e : OverlapIso p H)
    (he : e.hom ≫ (GroupScheme.baseChange (snd p)).map i =
      (GroupScheme.baseChange (fst p)).map i ≫ D.overlap.hom) : Cocycle e := by
  have h12 := pullHom_lift_fac (p12 p) rfl rfl D.overlap e.hom he
  have h23 := pullHom_lift_fac (p23 p) (p23_fst p) rfl D.overlap e.hom he
  have h13 := pullHom_lift_fac (p13 p) (p13_fst p) (p13_snd p) D.overlap e.hom he
  change (iso12 e).hom ≫ (GroupScheme.baseChange (p2 p)).map i =
    (GroupScheme.baseChange (p1 p)).map i ≫ (iso12 D.overlap).hom at h12
  change (iso23 e).hom ≫ (GroupScheme.baseChange (p3 p)).map i =
    (GroupScheme.baseChange (p2 p)).map i ≫ (iso23 D.overlap).hom at h23
  change (iso13 e).hom ≫ (GroupScheme.baseChange (p3 p)).map i =
    (GroupScheme.baseChange (p1 p)).map i ≫ (iso13 D.overlap).hom at h13
  have hc : ((iso12 e).hom ≫ (iso23 e).hom) ≫ (GroupScheme.baseChange (p3 p)).map i =
      (iso13 e).hom ≫ (GroupScheme.baseChange (p3 p)).map i := by
    rw [Category.assoc, h23, ← Category.assoc, h12, Category.assoc, D.cocycle, h13]
  have : Mono ((GroupScheme.baseChange (p3 p)).map i).hom.hom := by
    change Mono ((Over.pullback (p3 p)).map i.hom.hom)
    infer_instance
  apply Grp.hom_ext
  apply (cancel_mono ((GroupScheme.baseChange (p3 p)).map i).hom.hom).mp
  exact congrArg (fun a => a.hom.hom) hc

namespace Datum

variable (D : Datum p G)
    (h : SubgroupFunctor.range ((GroupScheme.baseChange (fst p)).map i ≫ D.overlap.hom) =
      SubgroupFunctor.range ((GroupScheme.baseChange (snd p)).map i))

/-- Equality of the all-test subgroup ranges constructs the source overlap isomorphism. -/
def monicSubgroupOverlap : OverlapIso p H := by
  let f := (GroupScheme.baseChange (fst p)).map i ≫ D.overlap.hom
  let g := (GroupScheme.baseChange (snd p)).map i
  have hf : (SubgroupFunctor.range f).IsRepresentedBy f := by
    refine ⟨?_, rfl⟩
    change Mono ((Over.pullback (fst p)).map i.hom.hom ≫ D.overlap.hom.hom.hom)
    infer_instance
  have hg : (SubgroupFunctor.range f).IsRepresentedBy g := by
    refine ⟨?_, h.symm⟩
    change Mono ((Over.pullback (snd p)).map i.hom.hom)
    infer_instance
  exact hf.isoOfIsRepresentedBy hg

/-- The constructed overlap commutes with the original monic inclusions. -/
theorem monicSubgroupOverlap_fac :
    (D.monicSubgroupOverlap h).hom ≫ (GroupScheme.baseChange (snd p)).map i =
      (GroupScheme.baseChange (fst p)).map i ≫ D.overlap.hom := by
  exact SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

/-- An invariant monic subgroup inherits an actual datum with its cocycle. -/
def monicSubgroup : Datum p H where
  overlap := D.monicSubgroupOverlap h
  cocycle := cocycle_of_monicSubgroup_lift D _ (D.monicSubgroupOverlap_fac h)

/-- The inclusion is compatible with the constructed source and ambient data. -/
theorem compatible_monicSubgroup : Compatible (D.monicSubgroup h) D i :=
  (D.monicSubgroupOverlap_fac h).symm

end Datum

/-- An invariant affine monic subgroup over an affine faithfully flat cover
descends to an actual affine monic subgroup, recovering the supplied inclusion. -/
theorem exists_affine_monic_descent_of_overlap_range_eq
    {B S : Scheme.{u}} (p : S ⟶ B) [IsAffine B] [IsAffine S]
    [Flat p] [Surjective p] {C : GroupScheme B}
    {H : GroupScheme S} [IsAffine H.X.left]
    {i : H ⟶ (GroupScheme.baseChange p).obj C} [Mono i.hom.hom]
    (h : SubgroupFunctor.range
        ((GroupScheme.baseChange (fst p)).map i ≫ (canonicalOverlap p C).hom) =
      SubgroupFunctor.range ((GroupScheme.baseChange (snd p)).map i)) :
    ∃ (H₀ : GroupScheme B) (j : H₀ ⟶ C) (e : (GroupScheme.baseChange p).obj H₀ ≅ H),
      IsAffine H₀.X.left ∧ Mono j.hom.hom ∧
        (GroupScheme.baseChange p).map j = e.hom ≫ i := by
  let D := (canonicalDatum p C).monicSubgroup h
  have hcompat : Compatible D (canonicalDatum p C) i :=
    (canonicalDatum p C).compatible_monicSubgroup h
  let j := D.affineHomTo C i hcompat
  have hj : (GroupScheme.baseChange p).map j = D.affineSolution.iso.hom ≫ i :=
    D.baseChange_affineHomTo C i hcompat
  have hm : Mono ((GroupScheme.baseChange p).map j).hom.hom := by
    rw [hj]
    change Mono (D.affineSolution.iso.hom.hom.hom ≫ i.hom.hom)
    infer_instance
  exact ⟨D.affineSolution.obj, j, D.affineSolution.iso, inferInstance,
    (Over.pullback p).mono_of_mono_map hm, hj⟩

end Langlands.GroupScheme.Descent
