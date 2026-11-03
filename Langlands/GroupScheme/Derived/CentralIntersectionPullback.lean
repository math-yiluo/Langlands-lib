import Langlands.GroupScheme.Derived.CentralIntersectionStatement
import Langlands.GroupScheme.Reductive.CenterExistenceProof
import Langlands.GroupScheme.SubgroupIntersection

/-! # The pullback representative of the centre inside a subgroup -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {D G Z : GroupScheme S}

/-- The first projection of the intersection with `z` has range the preimage of the range of `z`,
on every test scheme. -/
theorem range_subgroupIntersectionFst (d : D ⟶ G) (z : Z ⟶ G) :
    SubgroupFunctor.range (subgroupIntersectionFst d z) =
      (SubgroupFunctor.range z).comap d := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  change (∃ y : T ⟶ (subgroupIntersection d z).X,
      y ≫ (subgroupIntersectionFst d z).hom.hom = x) ↔
    ∃ w : T ⟶ Z.X, w ≫ z.hom.hom = x ≫ d.hom.hom
  let hpb := subgroupIntersection_isPullback d z
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y ≫ (subgroupIntersectionSnd d z).hom.hom, ?_⟩
    rw [Category.assoc, Category.assoc, hpb.w]
  · rintro ⟨w, hw⟩
    exact ⟨hpb.lift x w hw.symm, hpb.lift_fst _ _ _⟩

/-- The pullback of a centre representative along `d` represents the preimage of the centre. -/
theorem range_subgroupIntersectionFst_of_isSchemeTheoreticCenter (d : D ⟶ G) {z : Z ⟶ G}
    (hz : IsSchemeTheoreticCenter z) :
    SubgroupFunctor.range (subgroupIntersectionFst d z) = (center G).comap d := by
  rw [range_subgroupIntersectionFst, hz.2]

/-- The finiteness statement follows once the pullback of each centre representative along each
derived-subgroup inclusion is finite. -/
theorem derivedCentralIntersectionFiniteness_of_isFinite_subgroupIntersection
    (h : ∀ (k : Type u) [Field k] (G D Z : GroupScheme (Spec (CommRingCat.of k)))
      (d : D ⟶ G) (z : Z ⟶ G), IsConnectedReductive G → IsDerivedSubgroup d →
        IsSchemeTheoreticCenter z → IsFinite (subgroupIntersection d z).X.hom) :
    DerivedCentralIntersectionFinitenessStatement.{u} := by
  intro k _ G D d hG hd
  obtain ⟨Z, z, hz⟩ := schemeTheoreticCenterExistence k G hG
  exact ⟨subgroupIntersection d z, subgroupIntersectionFst d z,
    isClosedSubgroup_subgroupIntersectionFst d hz.1,
    range_subgroupIntersectionFst_of_isSchemeTheoreticCenter d hz,
    h k G D Z d z hG hd hz⟩

end Langlands.GroupScheme
