import Langlands.GroupScheme.RelativeLevi.ParabolicLocalEquality
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport
import Langlands.GroupScheme.Descent.Data

/-! # Local equality of parabolics from an actual field-valued point -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {S S' S'' : Scheme.{u}} {G H K : GroupScheme S}

/-- Equality of ranges after a composite base change reflects to the
intermediate base if the remaining map is fpqc. -/
theorem range_baseChange_eq_of_factorization
    (b : S' ⟶ S) (c : S'' ⟶ S') (d : S'' ⟶ S) (h : c ≫ b = d)
    [QuasiCompact c] [Flat c] [Surjective c]
    (i : H ⟶ G) (j : K ⟶ G) [Mono i.hom.hom] [Mono j.hom.hom]
    (heq : range ((GroupScheme.baseChange d).map i) = range ((GroupScheme.baseChange d).map j)) :
    range ((GroupScheme.baseChange b).map i) = range ((GroupScheme.baseChange b).map j) := by
  apply range_eq_of_baseChange_eq c ((GroupScheme.baseChange b).map i) ((GroupScheme.baseChange b).map j)
  rw [← range_baseChangeHom, ← range_baseChangeHom]
  apply (range_comp_iso_eq_iff _ _ (Descent.pullbackComparison b c d h G)).mp
  simpa only [Descent.pullbackComparison_naturality, range_iso_comp] using heq

/-- Equality of subgroup ranges at any field-valued point reflects to equality
at the residue field of its image. -/
theorem residueFiber_range_eq_of_fieldPoint_range_eq
    (i : H ⟶ G) (j : K ⟶ G) [Mono i.hom.hom] [Mono j.hom.hom]
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ S)
    (heq : range ((GroupScheme.baseChange x).map i) = range ((GroupScheme.baseChange x).map j)) :
    range (RelativeLevi.residueFiberHom i (x (IsLocalRing.closedPoint k))) =
      range (RelativeLevi.residueFiberHom j (x (IsLocalRing.closedPoint k))) := by
  let s := x (IsLocalRing.closedPoint k)
  let φ : S.residueField s ⟶ CommRingCat.of k :=
    S.descResidueField (Scheme.stalkClosedPointTo x)
  have hfactor : Spec.map φ ≫ S.fromSpecResidueField s = x :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k S x
  exact range_baseChange_eq_of_factorization (S.fromSpecResidueField s)
    (Spec.map φ) x hfactor i j heq

end SubgroupFunctor

variable {S : Scheme.{u}} {G P Q : GroupScheme S}
  (i : P ⟶ G) (j : Q ⟶ G) (T : CommGroupScheme S) (t : T.toGrp ⟶ G)

/-- Conditional on Lie-containment spreading, choose a neighbourhood of the
image of a field point on which two parabolics with equal field-point fibres
and a common maximal torus agree. -/
def relativeParabolicLocalEqualityOfFieldPoint
    (hLie : RelativeParabolicLieContainmentStatement.{u})
    (hG : IsReductive G)
    (hi : IsRelativeParabolicSubgroup i) (hj : IsRelativeParabolicSubgroup j)
    (hT : RelativeTorus.IsTorus T.toGrp) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus t)
    (hti : SubgroupFunctor.range t ≤ SubgroupFunctor.range i)
    (htj : SubgroupFunctor.range t ≤ SubgroupFunctor.range j)
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ S)
    (hfib : SubgroupFunctor.range ((GroupScheme.baseChange x).map i) =
      SubgroupFunctor.range ((GroupScheme.baseChange x).map j)) :
    {V : S.Opens // x (IsLocalRing.closedPoint k) ∈ V ∧
      SubgroupFunctor.range ((GroupScheme.baseChange V.ι).map i) =
        SubgroupFunctor.range ((GroupScheme.baseChange V.ι).map j)} := by
  let : Mono i.hom.hom := hi.mono
  let : Mono j.hom.hom := hj.mono
  exact relativeParabolicLocalEquality i j T t hLie hG hi hj hT ht hmax hti htj
    (x (IsLocalRing.closedPoint k))
    (SubgroupFunctor.residueFiber_range_eq_of_fieldPoint_range_eq i j x hfib)

end Langlands.GroupScheme
