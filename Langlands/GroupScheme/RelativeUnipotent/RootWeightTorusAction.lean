import Langlands.GroupScheme.RelativeLevi.SplitWeightDynamicComparison
import Langlands.GroupScheme.RelativeUnipotent.RootWeightFiltration
import Langlands.GroupScheme.Reductive.LocalSplitPositiveCell
import Langlands.GroupScheme.RepresentedAction
import Langlands.GroupScheme.RelativeLevi.SplitBorelPositiveFactors

/-! # Actual torus actions on represented root-weight terms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeUnipotent

open LocalSplitCell

variable {R : Type u} [CommRing R]
  {I J : Type u} [Fintype I]
  {U G : GroupScheme (Spec (CommRingCat.of R))}
  {t : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {ch : J → I → ℤ} {fam : J → (Ga R ⟶ G)}
  (C : RootHeightChart U) (j : U ⟶ G) [Mono j.hom.hom]
  {index : Fin C.dimension → J}
  (hroot : ∀ k, C.roots (ULift.up k) ≫ j = fam (index k))
  (hu : TorusEquivariant t ch fam)

namespace RootHeightChart

include hroot hu in
/-- The torus preserves the actual range of the full root chart. -/
theorem range_isStable_torus :
    (AutomorphicAction.conjugation t).IsStable (SubgroupFunctor.range j) := by
  intro T s x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  refine SubgroupFunctor.mem_range.mpr
    ⟨orderedProduct C.roots ULift.up T
      (fun k => torusChar (ch (index k)) T s * C.coordinates T y k), ?_⟩
  rw [LocalSplitCell.orderedProduct_chart_comp C j hroot, AutomorphicAction.conjugation_act,
    ← C.orderedProduct_coordinates T y, LocalSplitCell.orderedProduct_chart_comp C j hroot,
    torus_mul_orderedProduct_mul_inv hu]
  rw [C.coordinates_orderedProduct]

/-- Conjugation by the actual ambient torus on the root-chart group. -/
def torusAction : AutomorphicAction (splitTorus (Spec (CommRingCat.of R)) I) U :=
  (AutomorphicAction.conjugation t).onRepresentedSubgroup j
    ⟨inferInstance, rfl⟩ (C.range_isStable_torus j hroot hu)

/-- The action retains its actual ambient conjugation equation on all tests. -/
theorem torusAction_comp {T : Over (Spec (CommRingCat.of R))}
    (s : T ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) (x : T ⟶ U.X) :
    (C.torusAction j hroot hu).act s x ≫ j.hom.hom =
      (s ≫ t.hom.hom) * (x ≫ j.hom.hom) * (s ≫ t.hom.hom)⁻¹ := by
  rw [torusAction, AutomorphicAction.onRepresentedSubgroup_act_comp,
    AutomorphicAction.conjugation_act]

/-- In the original ordered chart, actual torus conjugation is diagonal in
precisely the supplied root characters. -/
theorem coordinates_torusAction {T : Over (Spec (CommRingCat.of R))}
    (s : T ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) (x : T ⟶ U.X) :
    C.coordinates T ((C.torusAction j hroot hu).act s x) =
      fun k => torusChar (ch (index k)) T s * C.coordinates T x k := by
  have he : (C.torusAction j hroot hu).act s x =
      orderedProduct C.roots ULift.up T
        (fun k => torusChar (ch (index k)) T s * C.coordinates T x k) := by
    apply (cancel_mono j.hom.hom).1
    rw [C.torusAction_comp j hroot hu, LocalSplitCell.orderedProduct_chart_comp C j hroot,
      ← C.orderedProduct_coordinates T x, LocalSplitCell.orderedProduct_chart_comp C j hroot,
      torus_mul_orderedProduct_mul_inv hu]
    rw [C.coordinates_orderedProduct]
  rw [he, C.coordinates_orderedProduct]

end RootHeightChart

namespace RootWeightData

variable {C} (W : RootWeightData C)

/-- Every cutoff is stable under the full actual torus, including zero weights. -/
theorem isStable_torusAction (d : ℕ) :
    (C.torusAction j hroot hu).IsStable (W.subgroup d) := by
  intro T s x hx
  rw [W.mem_subgroup_iff] at hx ⊢
  rw [C.coordinates_torusAction j hroot hu]
  intro k hk
  change torusChar (ch (index k)) T s * C.coordinates T x k = 0
  rw [hx k hk, mul_zero]

/-- The actual torus action on the represented coordinate-space filtration term. -/
def torusAction (d : ℕ) :
    AutomorphicAction (splitTorus (Spec (CommRingCat.of R)) I) (W.groupScheme d) :=
  (C.torusAction j hroot hu).onRepresentedSubgroup (W.inclusion d)
    (W.isRepresentedBy_inclusion d) (W.isStable_torusAction j hroot hu d)

/-- The term inclusion is equivariant on every scheme test. -/
theorem torusAction_inclusion {T : Over (Spec (CommRingCat.of R))} (d : ℕ)
    (s : T ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X)
    (x : T ⟶ (W.groupScheme d).X) :
    (W.torusAction j hroot hu d).act s x ≫ (W.inclusion d).hom.hom =
      (C.torusAction j hroot hu).act s (x ≫ (W.inclusion d).hom.hom) :=
  AutomorphicAction.onRepresentedSubgroup_act_comp _ _ _ _ s x

include hroot hu in
/-- Each actual term is normalized by the full ambient torus range. -/
theorem range_inclusion_isNormalizedBy_torus (d : ℕ) :
    (SubgroupFunctor.range (W.inclusion d ≫ j)).IsNormalizedBy
      (SubgroupFunctor.range t) := by
  intro T s x hs hx
  obtain ⟨s, rfl⟩ := SubgroupFunctor.mem_range.mp hs
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  refine SubgroupFunctor.mem_range.mpr
    ⟨(W.torusAction j hroot hu d).act s x, ?_⟩
  change ((W.torusAction j hroot hu d).act s x ≫ (W.inclusion d).hom.hom) ≫
    j.hom.hom = _
  rw [W.torusAction_inclusion j hroot hu, C.torusAction_comp j hroot hu]
  rfl

/-- The original chart's coordinates of every term carry exactly their root
characters; this includes all nonreduced scheme tests. -/
theorem coordinates_torusAction_inclusion {T : Over (Spec (CommRingCat.of R))} (d : ℕ)
    (s : T ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X)
    (x : T ⟶ (W.groupScheme d).X) :
    C.coordinates T ((W.torusAction j hroot hu d).act s x ≫ (W.inclusion d).hom.hom) =
      fun k => torusChar (ch (index k)) T s *
        C.coordinates T (x ≫ (W.inclusion d).hom.hom) k := by
  rw [W.torusAction_inclusion j hroot hu, C.coordinates_torusAction j hroot hu]

end RootWeightData

end Langlands.GroupScheme.RelativeUnipotent
