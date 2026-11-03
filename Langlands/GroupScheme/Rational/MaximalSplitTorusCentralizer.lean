import Langlands.GroupScheme.Rational.TorusCentralizerFactorization
import Langlands.GroupScheme.Rational.TorusSplitPartTransfer
import Langlands.GroupScheme.Rational.MaximalSplitTorusExtension

/-! # Testing maximal splitness in closed subgroups and centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Base

variable {S : Scheme.{u}} {G : GroupScheme S} {A B : CommGroupScheme S}

/-- The image of a commutative group containing another commutative subgroup
centralizes the smaller subgroup on every test scheme. -/
theorem range_le_torusCentralizer_of_factor
    (a : A.toGrp ⟶ G) (b : B.toGrp ⟶ G)
    (f : A.toGrp ⟶ B.toGrp) (hf : f ≫ b = a) :
    SubgroupFunctor.range b ≤ torusCentralizer a :=
  (range_le_torusCentralizer b).trans (torusCentralizer_le_of_factor b a f hf)

end Base

section Field

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {A B : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The canonical lift of a split subtorus to a closed subgroup containing its
range on every test scheme, bundled with splitness and the factorization identity. -/
def IsSplitSubtorus.factorInClosedSubgroup
    {b : B.toGrp ⟶ G} (hb : IsSplitSubtorus b)
    {j : H ⟶ G} (hj : IsClosedSubgroup j)
    (hcontained : SubgroupFunctor.range b ≤ SubgroupFunctor.range j) :
    {bH : B.toGrp ⟶ H // IsSplitSubtorus bH ∧ bH ≫ j = b} := by
  let : IsClosedImmersion j.hom.hom.left := hj
  have hjrep : (SubgroupFunctor.range j).IsRepresentedBy j :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  refine ⟨hjrep.factorHom b hcontained, ?_, hjrep.factorHom_comp b hcontained⟩
  apply IsSplitSubtorus.of_comp hj
  rwa [hjrep.factorHom_comp]

/-- The canonical closed-subgroup factor recovers the original ambient embedding. -/
theorem IsSplitSubtorus.factorInClosedSubgroup_comp
    {b : B.toGrp ⟶ G} (hb : IsSplitSubtorus b)
    {j : H ⟶ G} (hj : IsClosedSubgroup j)
    (hcontained : SubgroupFunctor.range b ≤ SubgroupFunctor.range j) :
    (hb.factorInClosedSubgroup hj hcontained).val ≫ j = b :=
  (hb.factorInClosedSubgroup hj hcontained).property.2

/-- The canonical factor remains a split subtorus of the closed subgroup. -/
theorem IsSplitSubtorus.isSplitSubtorus_factorInClosedSubgroup
    {b : B.toGrp ⟶ G} (hb : IsSplitSubtorus b)
    {j : H ⟶ G} (hj : IsClosedSubgroup j)
    (hcontained : SubgroupFunctor.range b ≤ SubgroupFunctor.range j) :
    IsSplitSubtorus (hb.factorInClosedSubgroup hj hcontained).val :=
  (hb.factorInClosedSubgroup hj hcontained).property.1

/-- A maximal split torus of a closed subgroup is ambient maximal if that
subgroup contains its entire ambient centralizer on every test scheme. -/
theorem IsMaximalSplitTorus.comp_of_torusCentralizer_le_range
    {a : A.toGrp ⟶ H} (ha : IsMaximalSplitTorus a)
    {j : H ⟶ G} (hj : IsClosedSubgroup j)
    (hZ : torusCentralizer (a ≫ j) ≤ SubgroupFunctor.range j) :
    IsMaximalSplitTorus (a ≫ j) := by
  let : IsClosedImmersion j.hom.hom.left := hj
  have hjrep : (SubgroupFunctor.range j).IsRepresentedBy j :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  refine ⟨ha.1.comp hj, ?_⟩
  intro B b hb f hf
  have hbRange : SubgroupFunctor.range b ≤ SubgroupFunctor.range j :=
    (range_le_torusCentralizer_of_factor (a ≫ j) b f hf).trans hZ
  let bH := (hb.factorInClosedSubgroup hj hbRange).val
  have hbH : bH ≫ j = b := hb.factorInClosedSubgroup_comp hj hbRange
  have hbHsplit : IsSplitSubtorus bH :=
    hb.isSplitSubtorus_factorInClosedSubgroup hj hbRange
  apply ha.2 B bH hbHsplit f
  apply hjrep.hom_ext
  rw [Category.assoc, hbH, hf]

/-- Maximal splitness can be tested in any closed subgroup containing the
whole ambient centralizer of the given torus. -/
theorem isMaximalSplitTorus_comp_iff_of_torusCentralizer_le_range
    (a : A.toGrp ⟶ H) (j : H ⟶ G) (hj : IsClosedSubgroup j)
    (hZ : torusCentralizer (a ≫ j) ≤ SubgroupFunctor.range j) :
    IsMaximalSplitTorus (a ≫ j) ↔ IsMaximalSplitTorus a :=
  ⟨IsMaximalSplitTorus.of_comp hj,
    fun ha => ha.comp_of_torusCentralizer_le_range hj hZ⟩

/-- A commutative subgroup is ambient maximal split exactly when its
canonical factor in a closed representative of its centralizer is maximal split. -/
theorem isMaximalSplitTorus_torusCentralizerFactor_iff
    (a : A.toGrp ⟶ G) {j : H ⟶ G}
    (hj : (torusCentralizer a).IsRepresentedBy j) (hjc : IsClosedSubgroup j) :
    IsMaximalSplitTorus (torusCentralizerFactor a hj) ↔ IsMaximalSplitTorus a := by
  constructor
  · intro ha
    have hZ : torusCentralizer (torusCentralizerFactor a hj ≫ j) ≤
        SubgroupFunctor.range j := by
      rw [torusCentralizerFactor_comp, hj.2]
    have h := ha.comp_of_torusCentralizer_le_range hjc hZ
    rwa [torusCentralizerFactor_comp] at h
  · exact fun ha => ha.isMaximalSplitTorus_torusCentralizerFactor hj hjc

/-- A torus maximal split in a closed subgroup is ambient maximal if some
ambient maximal split extension remains contained in that subgroup on all tests. -/
theorem IsMaximalSplitTorus.comp_of_maximal_extension_contained
    {a : A.toGrp ⟶ H} (ha : IsMaximalSplitTorus a)
    {j : H ⟶ G} (hj : IsClosedSubgroup j)
    {b : B.toGrp ⟶ G} (hb : IsMaximalSplitTorus b)
    (f : A.toGrp ⟶ B.toGrp) (hf : f ≫ b = a ≫ j)
    (hcontained : SubgroupFunctor.range b ≤ SubgroupFunctor.range j) :
    IsMaximalSplitTorus (a ≫ j) := by
  let : IsClosedImmersion j.hom.hom.left := hj
  have hjrep : (SubgroupFunctor.range j).IsRepresentedBy j :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  let bH := (hb.1.factorInClosedSubgroup hj hcontained).val
  have hbH : bH ≫ j = b := hb.1.factorInClosedSubgroup_comp hj hcontained
  have hfH : f ≫ bH = a := by
    apply hjrep.hom_ext
    rw [Category.assoc, hbH, hf]
  have : IsIso f := ha.2 B bH
    (hb.1.isSplitSubtorus_factorInClosedSubgroup hj hcontained) f hfH
  apply hb.of_factor (ha.1.comp hj) (inv f)
  rw [← hf, IsIso.inv_hom_id_assoc]

/-- To upgrade maximal splitness in a closed subgroup, it suffices to prove
containment there for ambient maximal split extensions of the original torus. -/
theorem IsMaximalSplitTorus.comp_of_maximal_extensions_contained
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {a : A.toGrp ⟶ H} (ha : IsMaximalSplitTorus a)
    {j : H ⟶ G} (hj : IsClosedSubgroup j)
    (hcontained : ∀ (B : CommGroupScheme (Spec (CommRingCat.of k)))
      (b : B.toGrp ⟶ G), IsMaximalSplitTorus b →
        ∀ f : A.toGrp ⟶ B.toGrp, f ≫ b = a ≫ j →
          SubgroupFunctor.range b ≤ SubgroupFunctor.range j) :
    IsMaximalSplitTorus (a ≫ j) := by
  obtain ⟨B, b, hb, f, hf⟩ := exists_maximalSplitTorus_extension G (a ≫ j) (ha.1.comp hj)
  exact ha.comp_of_maximal_extension_contained hj hb f hf (hcontained B b hb f hf)

end Field

end Langlands.GroupScheme
