import Langlands.GroupScheme.Reductive.RootComponentCommutation
import Langlands.GroupScheme.Reductive.NormalRootSupport
import Langlands.GroupScheme.Reductive.NormalRootDichotomyProof
import Langlands.GroupScheme.Reductive.NormalCentralizer

/-! # Normal root support is a union of Cartan components -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RootComponentCoordinates

open Langlands.LinearAlgebra.SimplyConnectedCartanComponents

variable {M : AffinePinnedModel.{u}} (D : RootComponentCoordinates M)

local instance : M.rootDatum.IsReduced := M.fibrewiseRootDatum.isReduced

/-- Reflection in any root preserves the Cartan component of each root. -/
theorem rootComponent_reflectionPerm (r s : M.rootIndex) :
    D.rootComponent (M.rootDatum.reflectionPerm s r) = D.rootComponent r := by
  classical
  by_cases hrs : D.rootComponent r = D.rootComponent s
  · let t := M.rootDatum.reflectionPerm s r
    let j := D.rootCoordinateWitness t
    have hj : component M.basis j = D.rootComponent t := D.rootCoordinateWitness_component t
    by_contra htr
    have hjr : component M.basis j ≠ D.rootComponent r := by
      rw [hj]
      exact htr
    have hjs : component M.basis j ≠ D.rootComponent s := by rwa [← hrs]
    apply D.rootCoordinateWitness_ne_zero t
    change D.characters (M.rootDatum.root (M.rootDatum.reflectionPerm s r)) j = 0
    rw [M.rootDatum.root_reflectionPerm, M.rootDatum.reflection_apply_root,
      map_sub, map_smul, Pi.sub_apply, Pi.smul_apply,
      D.root_support r j hjr, D.root_support s j hjs, smul_zero, sub_zero]
  · rw [D.reflectionPerm_eq_of_rootComponent_ne r s hrs]

/-- A set of root indices is constant on the actual integral Cartan
components. -/
def IsComponentUnion (R : Set M.rootIndex) : Prop :=
  ∀ r s, D.rootComponent r = D.rootComponent s → (r ∈ R ↔ s ∈ R)

/-- A predicate on simple indices respecting each nonzero Cartan edge is
constant on each component quotient. -/
theorem simple_mem_iff_of_component_eq (R : Set M.rootIndex)
    (hedge : ∀ i j : M.basis.support, M.rootDatum.pairing i j ≠ 0 →
      (i.val ∈ R ↔ j.val ∈ R))
    (i j : M.basis.support) (hij : component M.basis i = component M.basis j) :
    i.val ∈ R ↔ j.val ∈ R := by
  have hrel : Relation.EqvGen
      (fun i j : M.basis.support => M.rootDatum.pairing i j ≠ 0) i j :=
    Quotient.exact hij
  clear hij
  induction hrel with
  | rel a b hab => exact hedge a b hab
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2

/-- Reflection invariance and propagation along simple Cartan edges imply
constancy on every root component. -/
theorem isComponentUnion_of_reflections_edges (R : Set M.rootIndex)
    (hreflect : ∀ r s, M.rootDatum.reflectionPerm s r ∈ R ↔ r ∈ R)
    (hedge : ∀ i j : M.basis.support, M.rootDatum.pairing i j ≠ 0 →
      (i.val ∈ R ↔ j.val ∈ R)) :
    D.IsComponentUnion R := by
  have hsimple (r : M.rootIndex) : ∀ i : M.basis.support,
      component M.basis i = D.rootComponent r → (r ∈ R ↔ i.val ∈ R) := by
    refine M.basis.induction_reflect r
      (p := fun r => ∀ i : M.basis.support,
        component M.basis i = D.rootComponent r → (r ∈ R ↔ i.val ∈ R)) ?_ ?_ ?_
    · intro r ih i hi
      rw [D.rootComponent_reflectionPerm] at hi
      exact (hreflect r r).trans (ih i hi)
    · intro r hr i hi
      rw [D.simple_component ⟨r, hr⟩] at hi
      exact simple_mem_iff_of_component_eq R hedge ⟨r, hr⟩ i hi.symm
    · intro r s ih hs i hi
      rw [D.rootComponent_reflectionPerm] at hi
      exact (hreflect r s).trans (ih i hi)
  intro r s hrs
  let i := D.rootCoordinateWitness r
  have hi : component M.basis i = D.rootComponent r := D.rootCoordinateWitness_component r
  exact (hsimple r i hi).trans (hsimple s i (hi.trans hrs)).symm

private local instance : Smooth M.group.X.hom := M.reductive.smooth

variable (k : Type u) [Field k] [Algebra M.ring k]

private local instance : IsAffineHom ((baseChange (algebraBaseMap M.ring k)).obj M.group).X.hom :=
  (M.reductive.isConnectedReductive_algebraMap k).isAffineHom

/-- Root support of an actual field subgroup functor, expressed on the
constant root indices of the pinned model. -/
def fieldNormalRootSupport
    (F : SubgroupFunctor ((baseChange (algebraBaseMap M.ring k)).obj M.group)) :
    Set M.rootIndex :=
  normalRootSupport (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) M.coordinates)
    (D.fieldTorusInclusion k)
    (CoordinateRootDatum.fieldRealization k M.rootDatum) F

/-- Actual root-subgroup containment on constant root indices is preserved
by every root reflection of a normal subgroup functor. -/
theorem fieldNormalRootSupport_reflection
    {F : SubgroupFunctor ((baseChange (algebraBaseMap M.ring k)).obj M.group)}
    (hF : F.IsNormal) (r s : M.rootIndex) :
    M.rootDatum.reflectionPerm s r ∈ D.fieldNormalRootSupport k F ↔
      r ∈ D.fieldNormalRootSupport k F := by
  have hmax := splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise
    M.coordinates M.group M.inclusion M.maximal k
  let : IsClosedImmersion (D.fieldTorusInclusion k).hom.hom.left := hmax.2.1
  have hp := M.fibrewiseRootDatum.field k
  have hstep (r s : M.rootIndex) (hr : r ∈ D.fieldNormalRootSupport k F) :
      M.rootDatum.reflectionPerm s r ∈ D.fieldNormalRootSupport k F :=
    normalRootSupport_reflection
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) M.coordinates)
      (P := CoordinateRootDatum.fieldRealization k M.rootDatum)
      (D.fieldTorusInclusion k) hp hF r s hr
  refine ⟨fun hr => ?_, hstep r s⟩
  have h := hstep (M.rootDatum.reflectionPerm s r) s hr
  simpa only [M.rootDatum.reflectionPerm_self] using h

/-- For a smooth connected closed normal subgroup of a semisimple field
fibre, containment of actual root groups is constant on each Cartan component. -/
theorem fieldNormalRootSupport_isComponentUnion [IsAlgClosed k]
    (hG : IsSemisimple ((baseChange (algebraBaseMap M.ring k)).obj M.group))
    {H : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth H.X.hom] [ConnectedSpace H.X.left]
    (h : H ⟶ (baseChange (algebraBaseMap M.ring k)).obj M.group)
    (hc : IsClosedSubgroup h) (hn : (SubgroupFunctor.range h).IsNormal) :
    D.IsComponentUnion (D.fieldNormalRootSupport k (SubgroupFunctor.range h)) := by
  let i := D.fieldTorusInclusion k
  let P := CoordinateRootDatum.fieldRealization k M.rootDatum
  have hmax : IsMaximalTorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) M.coordinates) i :=
    splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise
      M.coordinates M.group M.inclusion M.maximal k
  have hsplit : IsSplitSubtorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) M.coordinates) i := ⟨isSplitTorus_splitTorus M.coordinates, hmax.2.1⟩
  have hP : IsRootDatumOf
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) M.coordinates) i P := M.fibrewiseRootDatum.field k
  have hfix : (AutomorphicAction.conjugation h).fixedSubgroup ≤
      (SubgroupFunctor.range h).centralizer := by
    intro U x hx V f y hy
    obtain ⟨z, rfl⟩ := SubgroupFunctor.mem_range.mp hy
    exact ((mem_conjugation_fixedSubgroup_iff h x).mp hx V f z).symm
  have hprop (r s : M.rootIndex) (hrs : M.rootDatum.pairing s r ≠ 0)
      (hr : r ∈ D.fieldNormalRootSupport k (SubgroupFunctor.range h)) :
      s ∈ D.fieldNormalRootSupport k (SubgroupFunctor.range h) := by
    have hsroot : P.root s ∈ relativeRoots i := by
      rw [relativeRoots_eq_roots, ← hP.2.1]
      exact Set.mem_range_self s
    rcases semisimpleNormalRootDichotomy k _ hG
      (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) M.coordinates)
      i hsplit hmax H h hc hn (P.root s) hsroot
      with hs | hs
    · exact hs
    · have hz := hP.pairing_eq_zero_of_normalRootSupport_centralizer
        (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) M.coordinates) i
        hG.isConnectedReductive hsplit.1 hmax hn r s hr (hs.trans hfix)
      apply (hrs ?_).elim
      rw [← P.root_coroot_eq_pairing, CoordinateRootDatum.fieldRealization_root,
        CoordinateRootDatum.fieldRealization_coroot,
        CoordinateRootDatum.fieldRealization_pairing, M.rootDatum.root_coroot_eq_pairing] at hz
      exact hz
  apply D.isComponentUnion_of_reflections_edges
    (D.fieldNormalRootSupport k (SubgroupFunctor.range h))
    (D.fieldNormalRootSupport_reflection k hn)
  intro a b hab
  refine ⟨hprop a b ?_, hprop b a hab⟩
  exact fun hba => hab (M.rootDatum.pairing_eq_zero_iff'.mpr hba)

end Langlands.GroupScheme.RootComponentCoordinates
