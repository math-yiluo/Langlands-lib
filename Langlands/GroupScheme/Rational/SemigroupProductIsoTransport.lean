import Langlands.GroupScheme.Rational.SemigroupProductRestriction
import Langlands.GroupScheme.Rational.SemigroupTransport
import Langlands.GroupScheme.Rational.CoordinateCotangentPullbackProof

/-! # Exact ordered semigroup products under equivariant isomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (b : AutomorphicAction S.toGrp G) (c : AutomorphicAction S.toGrp H)
    (e : G ≅ H)
    (he : CoordinateWeights.IsEquivariant b c e.hom.hom.hom)

omit [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] in
private theorem range_iso_hom_eq_top : SubgroupFunctor.range e.hom = ⊤ := by
  have hi : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 H.X :=
    ((Grp.forget _).mapIso e).inv_hom_id
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  constructor
  · exact fun _ => Subgroup.mem_top _
  · intro _
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨x ≫ e.inv.hom.hom, ?_⟩
    rw [Category.assoc, hi, Category.comp_id]

include he

/-- Equivariant group-scheme isomorphisms preserve the entire actual support,
including an occurring zero character. -/
theorem actionWeightSupport_eq_of_equivariant_iso :
    actionWeightSupport b ⊤ = actionWeightSupport c ⊤ := by
  have h := actionWeightSupport_map e.hom inferInstance b c he ⊤
  rw [SubgroupFunctor.map_top, range_iso_hom_eq_top e] at h
  exact h.symm

/-- Each exact generated semigroup subgroup is carried onto its counterpart. -/
theorem semigroupSubgroup_map_equivariant_iso (A : AddSubsemigroup (characterLattice S)) :
    (semigroupSubgroup b A).map e.hom = semigroupSubgroup c A := by
  apply semigroupSubgroup_map_eq e.hom (IsClosedSubgroup.of_iso e) b c he A
  rw [range_iso_hom_eq_top e]
  exact fun _ _ _ => Subgroup.mem_top _

/-- The canonical equivalence on exact semigroup points over every test scheme. -/
def semigroupPointsEquivOfIso (A : AddSubsemigroup (characterLattice S))
    (T : Over (Spec (CommRingCat.of k))) :
    (semigroupSubgroup b A).carrier T ≃* (semigroupSubgroup c A).carrier T :=
  semigroupSubgroupPointsEquiv e.hom (IsClosedSubgroup.of_iso e) b c he A
    (by rw [range_iso_hom_eq_top e]; exact fun _ _ _ => Subgroup.mem_top _) T

/-- The constructed point equivalence is postcomposition with the supplied iso. -/
@[simp] theorem semigroupPointsEquivOfIso_val
    (A : AddSubsemigroup (characterLattice S))
    (T : Over (Spec (CommRingCat.of k))) (x : (semigroupSubgroup b A).carrier T) :
    (semigroupPointsEquivOfIso b c e he A T x).val = x.val ≫ e.hom.hom.hom :=
  rfl

/-- The exact ordered-product property transports without changing the blocks,
their positive closures, or the order of multiplication. -/
theorem HasOrderedSemigroupProducts.map_equivariant_iso
    (hb : HasOrderedSemigroupProducts b) : HasOrderedSemigroupProducts c := by
  intro n Ψ hcover hdis hcross
  have hsupport := actionWeightSupport_eq_of_equivariant_iso b c e he
  obtain ⟨K, j, hj, hp⟩ := hb n Ψ (hcover.trans hsupport.symm) hdis hcross
  let : IsIso (orderedMultiplication j) := hp
  refine ⟨K, fun r => j r ≫ e.hom, ?_, ?_⟩
  · intro r
    have hr := (hj r).1.comp
      (show (SubgroupFunctor.range e.hom).IsRepresentedBy e.hom from ⟨inferInstance, rfl⟩)
    rw [semigroupSubgroup_map_equivariant_iso b c e he] at hr
    exact ⟨hr, (hj r).2.1.comp (IsClosedSubgroup.of_iso e),
      (hj r).2.2.1, (hj r).2.2.2⟩
  · rw [← orderedMultiplication_comp]
    infer_instance

/-- The original and transported action have exactly the same ordered-product
property, with no extra geometric or semigroup-comparison hypothesis. -/
theorem hasOrderedSemigroupProducts_iff_of_equivariant_iso :
    HasOrderedSemigroupProducts b ↔ HasOrderedSemigroupProducts c :=
  ⟨fun hb => hb.map_equivariant_iso b c e he,
    fun hc => hc.map_equivariant_iso c b e.symm
      (CoordinateWeights.isEquivariant_inv b c e he)⟩

end Langlands.GroupScheme.RelativeRoot
