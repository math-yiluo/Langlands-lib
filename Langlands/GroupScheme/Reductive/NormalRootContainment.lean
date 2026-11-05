import Langlands.GroupScheme.Dynamic.NormalSubgroupContraction
import Langlands.GroupScheme.Rational.RootSubgroupPositive
import Langlands.GroupScheme.Rational.WeightVectorUniqueness
import Langlands.GroupScheme.Rational.QuotientActionComparisonProof

/-! # Root containment from nonzero restriction to a normal subgroup's torus -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

section Base

variable {B : Scheme.{u}} {S T : CommGroupScheme B} {G : GroupScheme B}
    (f : S ⟶ T) (t : T.toGrp ⟶ G) (α : characterLattice T)

/-- A character vanishing on a subtorus makes its full root functor centralize
that subtorus, on every test scheme and every refinement. -/
theorem subgroup_le_fixedSubgroup_of_restriction_eq_zero
    (hα : f ≫ α = 0) :
    subgroup t α ≤
      (AutomorphicAction.conjugation (CommGroupScheme.groupHom f ≫ t)).fixedSubgroup := by
  rintro U g ⟨e, he, _⟩ V b z
  have hval (x : V ⟶ T.X)
      (hx : x ≫ (CommGroupScheme.groupHom α).hom.hom = 1) :
      (AutomorphicAction.conjugation t).act x (b ≫ g) =
        lift b (1 ≫ AffineLine.unitInclusion B) ≫ e := by
    rw [← lift_orbit, ← he, lift_whiskerLeft_assoc, ← Category.assoc x, hx]
  have hz : (z ≫ (CommGroupScheme.groupHom f).hom.hom) ≫
      (CommGroupScheme.groupHom α).hom.hom = 1 := by
    change z ≫ (CommGroupScheme.groupHom (f ≫ α)).hom.hom = 1
    rw [hα]
    exact MonObj.comp_one _
  have hc := (hval _ hz).trans
    ((hval 1 (MonObj.one_comp _)).symm.trans
      ((AutomorphicAction.conjugation t).act_one_left (b ≫ g)))
  simpa only [AutomorphicAction.conjugation_act, Grp.comp_hom_hom,
    Category.assoc] using hc

end Base

section Field

variable {k : Type u} [Field k]
    {S T : CommGroupScheme (Spec (CommRingCat.of k))}
    {H G U : GroupScheme (Spec (CommRingCat.of k))}
    (f : S ⟶ T) (t : T.toGrp ⟶ G) (s : S.toGrp ⟶ H) (h : H ⟶ G)
    (hS : IsSplitTorus S.toGrp)
    (hd : IsClosedSubgroup h) (hn : (SubgroupFunctor.range h).IsNormal)
    (hcomp : CommGroupScheme.groupHom f ≫ t = s ≫ h)
    (α : characterLattice T)

include hS hd hn hcomp

/-- A nonzero root character on a split torus inside a closed normal subgroup
forces the entire intrinsic root functor into that subgroup. -/
theorem subgroup_le_range_of_restriction_ne_zero (hα : f ≫ α ≠ 0) :
    subgroup t α ≤ SubgroupFunctor.range h := by
  obtain ⟨D, hD, ν, hν⟩ := hS.exists_pairing_eq_pos hα
  have hp : 0 < latticePairing T α (ν ≫ f) := by
    have heq : latticePairing T α (ν ≫ f) = latticePairing S (f ≫ α) ν := by
      simp only [latticePairing_apply, Category.assoc]
    rw [heq, hν]
    exact_mod_cast hD
  have hc : CommGroupScheme.groupHom (ν ≫ f) ≫ t =
      CommGroupScheme.groupHom ν ≫ s ≫ h := by
    change CommGroupScheme.groupHom ν ≫ CommGroupScheme.groupHom f ≫ t = _
    rw [hcomp]
  apply (subgroup_le_dynamicUnipotent t (ν ≫ f) hp).trans
  apply Dynamic.unipotent_le_range_of_normal h _ hd hn
  rw [hc]
  rintro V g ⟨x, rfl⟩
  exact SubgroupFunctor.mem_range.mpr
    ⟨x ≫ (CommGroupScheme.groupHom ν ≫ s).hom.hom, by
      change (x ≫ (CommGroupScheme.groupHom ν ≫ s).hom.hom) ≫ h.hom.hom =
        x ≫ (CommGroupScheme.groupHom ν ≫ s ≫ h).hom.hom
      simp only [Grp.comp_hom_hom]
      exact Category.assoc _ _ _⟩

/-- An outside root has zero restriction to every such split torus. -/
theorem restriction_eq_zero_of_subgroup_not_le_range
    (hα : ¬ subgroup t α ≤ SubgroupFunctor.range h) : f ≫ α = 0 := by
  by_contra hne
  exact hα (subgroup_le_range_of_restriction_ne_zero f t s h hS hd hn hcomp α hne)

/-- The first normal-root dichotomy: a root lies in the normal subgroup or
centralizes its chosen split torus. -/
theorem subgroup_le_range_or_fixedSubgroup :
    subgroup t α ≤ SubgroupFunctor.range h ∨
      subgroup t α ≤
        (AutomorphicAction.conjugation (s ≫ h)).fixedSubgroup := by
  by_cases hα : f ≫ α = 0
  · right
    rw [← hcomp]
    exact subgroup_le_fixedSubgroup_of_restriction_eq_zero f t α hα
  · exact Or.inl
      (subgroup_le_range_of_restriction_ne_zero f t s h hS hd hn hcomp α hα)

variable {j : U ⟶ G} (hU : (subgroup t α).IsRepresentedBy j)

/-- An actual representative of a root with nonzero restriction factors
through the original closed normal inclusion. -/
def normalRootLift (hα : f ≫ α ≠ 0) : U ⟶ H := by
  let : IsClosedImmersion h.hom.hom.left := hd
  exact hU.lift
    (⟨Over.mono_of_mono_left h.hom.hom, rfl⟩ :
      (SubgroupFunctor.range h).IsRepresentedBy h)
    (fun V => Subgroup.inclusion
      (subgroup_le_range_of_restriction_ne_zero f t s h hS hd hn hcomp α hα V))
    (fun _ _ => rfl)

/-- The lift's ambient composite is the supplied root inclusion. -/
theorem normalRootLift_comp (hα : f ≫ α ≠ 0) :
    normalRootLift f t s h hS hd hn hcomp α hU hα ≫ h = j := by
  let : IsClosedImmersion h.hom.hom.left := hd
  exact hU.lift_comp_eq
    (⟨Over.mono_of_mono_left h.hom.hom, rfl⟩ :
      (SubgroupFunctor.range h).IsRepresentedBy h)
    (fun V => Subgroup.inclusion
      (subgroup_le_range_of_restriction_ne_zero f t s h hS hd hn hcomp α hα V))
    (fun _ _ => rfl) (fun _ _ => rfl)

end Field

end Langlands.GroupScheme.RelativeRoot
