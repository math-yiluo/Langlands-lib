import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.HomDescent

/-! # Base change and uniqueness of actual fppf kernel quotients -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The full actual kernel range commutes with any change of base. -/
theorem kernel_range_baseChange {S S' : Scheme.{u}} (b : S' ⟶ S)
    {G Q : GroupScheme S} (q : G ⟶ Q) :
    SubgroupFunctor.range (kernelι ((baseChange b).map q)) =
      (SubgroupFunctor.range (kernelι q)).baseChange b := by
  ext T x
  rw [mem_range_kernelι_iff, SubgroupFunctor.mem_baseChange, mem_range_kernelι_iff]
  rw [← baseChangePointsEquiv_comp]
  exact (baseChangePointsEquiv b Q T).map_eq_one_iff.symm

namespace RelativeRoot.IsFppfQuotient

/-- The represented fppf quotient predicate is stable under arbitrary base change. -/
theorem baseChange {S S' : Scheme.{u}} (b : S' ⟶ S)
    {G Q : GroupScheme S} {F : SubgroupFunctor G} {q : G ⟶ Q}
    (hq : RelativeRoot.IsFppfQuotient F q) :
    RelativeRoot.IsFppfQuotient (F.baseChange b) ((GroupScheme.baseChange b).map q) := by
  refine ⟨MorphismProperty.overPullbackMap (P := @Flat) b q.hom.hom hq.1,
    MorphismProperty.overPullbackMap (P := @Surjective) b q.hom.hom hq.2.1,
    MorphismProperty.overPullbackMap (P := @LocallyOfFinitePresentation) b q.hom.hom hq.2.2.1,
    ?_⟩
  rw [kernel_range_baseChange, hq.2.2.2]

end RelativeRoot.IsFppfQuotient

namespace FppfQuotientComparison

variable {S : Scheme.{u}} {G Q R : GroupScheme S} {F : SubgroupFunctor G}
    {q : G ⟶ Q} {r : G ⟶ R}
    (hq : RelativeRoot.IsFppfQuotient F q) (hr : RelativeRoot.IsFppfQuotient F r)

include hq hr

/-- The second quotient kills the whole kernel of the first. -/
theorem kernel_comp : kernelι q ≫ r = 0 := by
  apply Grp.hom_ext
  change (kernelι q).hom.hom ≫ r.hom.hom = 1
  apply (mem_range_kernelι_iff r _).mp
  rw [hr.2.2.2, ← hq.2.2.2]
  exact SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩

/-- The canonical map between two actual quotients of the same full kernel. -/
def hom [QuasiCompact q.hom.hom.left] : Q ⟶ R :=
  letI := hq.1
  letI := hq.2.1
  FpqcHomDescent.hom q r (kernel_comp hq hr)

@[reassoc]
theorem fac [QuasiCompact q.hom.hom.left] : q ≫ hom hq hr = r := by
  have := hq.1
  have := hq.2.1
  exact FpqcHomDescent.fac q r (kernel_comp hq hr)

omit hr in
/-- Equality of maps out of a quotient can be checked on the original source. -/
theorem hom_ext {T : GroupScheme S} {a b : Q ⟶ T} (hab : q ≫ a = q ≫ b) : a = b := by
  have := hq.1
  have := hq.2.1
  have : Epi q.hom.hom.left := Flat.epi_of_flat_of_surjective _
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply (cancel_epi q.hom.hom.left).mp
  exact congrArg (fun f => f.hom.hom.left) hab

/-- The two quotient groups are canonically isomorphic over their common source. -/
def iso [QuasiCompact q.hom.hom.left] [QuasiCompact r.hom.hom.left] : Q ≅ R where
  hom := hom hq hr
  inv := hom hr hq
  hom_inv_id := by
    apply hom_ext hq
    rw [← Category.assoc, fac, fac, Category.comp_id]
  inv_hom_id := by
    apply hom_ext hr
    rw [← Category.assoc, fac, fac, Category.comp_id]

@[reassoc]
theorem iso_fac [QuasiCompact q.hom.hom.left] [QuasiCompact r.hom.hom.left] :
    q ≫ (iso hq hr).hom = r := fac hq hr

/-- The common-source equation characterizes the comparison isomorphism. -/
theorem iso_unique [QuasiCompact q.hom.hom.left] [QuasiCompact r.hom.hom.left]
    (e : Q ≅ R) (he : q ≫ e.hom = r) : e = iso hq hr := by
  apply Iso.ext
  apply hom_ext hq
  rw [he, iso_fac]

end FppfQuotientComparison
end Langlands.GroupScheme
