import Langlands.GroupScheme.Dynamic.ClosedSubgroup
import Langlands.GroupScheme.Derived.Basic
import Langlands.GroupScheme.Rational.RootSubgroupPositive
import Langlands.GroupScheme.Rational.WeightVectorUniqueness
import Langlands.GroupScheme.RepresentedSubgroup

/-!
# Dynamic and relative root subgroups lie in the actual derived subgroup

The commutator with a contracting cocharacter extends over the affine line.
At zero it gives the inverse of the original point, so every closed subgroup
containing all commutators contains the dynamic identity-limit subgroup.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Dynamic

variable {S : Scheme.{u}} {G H : GroupScheme S}
    (d : H ⟶ G) (χ : (Gm S).toGrp ⟶ G)

/-- A closed subgroup containing every commutator contains every point
contracting to the identity under a cocharacter of the ambient group. -/
theorem unipotent_le_range_of_containsCommutators (hd : IsClosedSubgroup d)
    (hcomm : (SubgroupFunctor.range d).ContainsCommutators) :
    unipotent χ ≤ SubgroupFunctor.range d := by
  rintro T g ⟨e, he, he0⟩
  let a : T ⊗ (Gm S).X ⟶ G.X := snd T (Gm S).X ≫ χ.hom.hom
  let b : T ⊗ (Gm S).X ⟶ G.X := fst T (Gm S).X ≫ g
  have hc : orbit χ g * b⁻¹ ∈
      (SubgroupFunctor.range d).carrier (T ⊗ (Gm S).X) :=
    hcomm _ a b
  let r : T ⊗ AffineLine.scheme S ⟶ G.X :=
    e * (fst T (AffineLine.scheme S) ≫ g)⁻¹
  obtain ⟨c, hc⟩ := SubgroupFunctor.mem_range.mp hc
  have : IsClosedImmersion d.hom.hom.left := hd
  obtain ⟨r', hr'⟩ := AffineLine.exists_lift_of_unitInclusion d.hom.hom r c (by
    rw [hc]
    dsimp only [r, b]
    rw [MonObj.comp_mul, GrpObj.comp_inv, he, whiskerLeft_fst_assoc])
  have hi : g⁻¹ ∈ (SubgroupFunctor.range d).carrier T := by
    refine SubgroupFunctor.mem_range.mpr ⟨evalZero r', ?_⟩
    rw [← evalZero_comp, hr']
    dsimp only [r]
    rw [evalZero_mul, evalZero_inv, evalZero_fst, he0, one_mul]
  simpa only [inv_inv] using ((SubgroupFunctor.range d).carrier T).inv_mem hi

/-- The dynamic identity-limit subgroup lies in the scheme-theoretic derived
subgroup, on every test scheme. -/
theorem unipotent_le_derivedSubgroup (χ : (Gm S).toGrp ⟶ G) :
    unipotent χ ≤ derivedSubgroup G := by
  intro T g hg H d hd hcomm
  exact unipotent_le_range_of_containsCommutators d χ hd hcomm T hg

end Dynamic

namespace RelativeRoot

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G D U : GroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    {a : characterLattice T}

include hT

/-- A nonzero character of a split torus has its full relative root subgroup
inside the actual scheme-theoretic derived subgroup. -/
theorem subgroup_le_derivedSubgroup (ha : a ≠ 0) :
    subgroup i a ≤ derivedSubgroup G := by
  obtain ⟨N, hN, ν, hν⟩ := hT.exists_pairing_eq_pos ha
  have hp : 0 < latticePairing T a ν := by
    rw [hν]
    exact_mod_cast hN
  exact (subgroup_le_dynamicUnipotent i ν hp).trans
    (Dynamic.unipotent_le_derivedSubgroup _)

variable {d : D ⟶ G} (hd : IsDerivedSubgroup d)
    {j : U ⟶ G} (hU : (subgroup i a).IsRepresentedBy j)

/-- The actual factor of a represented nonzero relative root subgroup through
the supplied actual derived inclusion. -/
def derivedLift (ha : a ≠ 0) : U ⟶ D :=
  hU.lift hd.isRepresentedBy
    (fun V => Subgroup.inclusion (subgroup_le_derivedSubgroup i hT ha V))
    (fun _ _ => rfl)

/-- The root factor has the original root inclusion as ambient composite. -/
theorem derivedLift_comp (ha : a ≠ 0) :
    derivedLift i hT hd hU ha ≫ d = j :=
  hU.lift_comp_eq hd.isRepresentedBy
    (fun V => Subgroup.inclusion (subgroup_le_derivedSubgroup i hT ha V))
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- The ambient composite uniquely determines the root factor. -/
theorem derivedLift_unique (ha : a ≠ 0) (f : U ⟶ D) (hf : f ≫ d = j) :
    f = derivedLift i hT hd hU ha := by
  have : Mono d.hom.hom := hd.isRepresentedBy.1
  apply Grp.hom_ext
  apply (cancel_mono d.hom.hom).mp
  exact congrArg (fun z : U ⟶ G => z.hom.hom)
    (hf.trans (derivedLift_comp i hT hd hU ha).symm)

end RelativeRoot

end Langlands.GroupScheme
