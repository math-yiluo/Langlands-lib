import Langlands.GroupScheme.Reductive.PinningBaseChange
import Langlands.GroupScheme.Reductive.SplitBorelCell
import Langlands.GroupScheme.Absolute.SplitTorusDynamicDescent
import Langlands.GroupScheme.Rational.RelativeRootSignInclusionsProof
import Langlands.GroupScheme.Rational.RelativeTitsNondegeneracy

/-! # The actual chosen Borel under scalar extension -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitPinning

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    [Algebra.IsAlgebraic k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

local notation "b" => algebraBaseMap k K

local instance pinnedBorelBaseChangeIsAffineHom : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom b)
  infer_instance

/-- Pulling the full integral root datum and its base back preserves root height. -/
theorem baseChange_height (a : p.rootIndex) :
    (p.baseChange (F := K)).base.height a = p.base.height a := by
  classical
  obtain ⟨c, -, -, hc⟩ := p.base.exists_root_eq_sum_int a
  have hroot : (p.baseChange (F := K)).rootDatum.root a =
      ∑ j ∈ (p.baseChange (F := K)).base.support,
        c j • (p.baseChange (F := K)).rootDatum.root j := by
    change characterLattice.baseChange b p.torus (p.rootDatum.root a) =
      ∑ j ∈ p.baseChangeBase.support,
        c j • characterLattice.baseChange b p.torus (p.rootDatum.root j)
    rw [baseChangeBase_support, hc, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_zsmul]
  rw [RootPairing.Base.height_eq_sum hroot, RootPairing.Base.height_eq_sum hc]
  change (∑ j ∈ p.baseChangeBase.support, c j) = ∑ j ∈ p.base.support, c j
  rw [baseChangeBase_support]

/-- The two independently chosen positive cocharacters have identical positive
root pairings after scalar extension. -/
theorem baseChange_positiveCocharacter_pos_iff (a : p.rootIndex) :
    0 < latticePairing (p.baseChange (F := K)).torus
        ((p.baseChange (F := K)).rootDatum.root a)
        (cocharacterLattice.baseChange b p.torus p.positiveCocharacter) ↔
      0 < latticePairing (p.baseChange (F := K)).torus
        ((p.baseChange (F := K)).rootDatum.root a)
        (p.baseChange (F := K)).positiveCocharacter := by
  have hleft : latticePairing (p.baseChange (F := K)).torus
        ((p.baseChange (F := K)).rootDatum.root a)
        (cocharacterLattice.baseChange b p.torus p.positiveCocharacter) =
      latticePairing p.torus (p.rootDatum.root a) p.positiveCocharacter :=
    latticePairing_baseChange b p.torus _ _
  rw [hleft, p.latticePairing_root_positiveCocharacter,
    (p.baseChange (F := K)).latticePairing_root_positiveCocharacter, p.baseChange_height]
  exact (mul_pos_iff_of_pos_left p.positiveScale_pos).trans
    (mul_pos_iff_of_pos_left (p.baseChange (F := K)).positiveScale_pos).symm

/-- The actual pullback of the old negative dynamic parabolic is the new
negative dynamic parabolic on every relative scheme test. -/
theorem parabolic_baseChange_opposite_positiveGm :
    Dynamic.parabolic (Dynamic.baseChangeCocharacter b
      (Dynamic.oppositeCocharacter p.positiveGm)) =
      Dynamic.parabolic (Dynamic.oppositeCocharacter (p.baseChange (F := K)).positiveGm) := by
  have hcochar : Dynamic.baseChangeCocharacter b
        (Dynamic.oppositeCocharacter p.positiveGm) =
      CommGroupScheme.groupHom
        (cocharacterLattice.baseChange b p.torus (-p.positiveCocharacter)) ≫
          (GroupScheme.baseChange b).map p.inclusion := by
    change Dynamic.baseChangeCocharacter b
        (Dynamic.oppositeCocharacter
          (CommGroupScheme.groupHom p.positiveCocharacter ≫ p.inclusion)) = _
    rw [← groupHom_neg_comp_eq_oppositeCocharacter,
      Dynamic.baseChangeCocharacter_comp, ← cocharacterLattice.groupHom_baseChange_dynamic]
  rw [hcochar]
  change Dynamic.parabolic _ = Dynamic.parabolic
    (Dynamic.oppositeCocharacter
      (CommGroupScheme.groupHom (p.baseChange (F := K)).positiveCocharacter ≫
        (p.baseChange (F := K)).inclusion))
  rw [← groupHom_neg_comp_eq_oppositeCocharacter]
  have hsign (α : characterLattice (p.baseChange (F := K)).torus)
      (hα : α ∈ relativeRoots (p.baseChange (F := K)).inclusion) :
      0 ≤ latticePairing (p.baseChange (F := K)).torus α
          (cocharacterLattice.baseChange b p.torus (-p.positiveCocharacter)) ↔
        0 ≤ latticePairing (p.baseChange (F := K)).torus α
          (-(p.baseChange (F := K)).positiveCocharacter) := by
    obtain ⟨a, rfl⟩ : ∃ a, (p.baseChange (F := K)).rootDatum.root a = α := by
      rw [← Set.mem_range, (p.baseChange (F := K)).isRootDatum.2.1]
      exact hα
    simpa only [map_neg, neg_nonneg, not_lt] using
      not_congr (p.baseChange_positiveCocharacter_pos_iff (K := K) a)
  have h := relativeRootSignInclusions K ((GroupScheme.baseChange b).obj G)
    (p.baseChange (F := K)).isConnectedReductive (p.baseChange (F := K)).torus
    (p.baseChange (F := K)).inclusion
    ((p.baseChange (F := K)).isMaximalTorus.isMaximalSplitTorus
      (p.baseChange (F := K)).isSplitTorus)
  apply le_antisymm
  · exact (h _ _).1.mpr fun α hα => (hsign α hα).mp
  · exact (h _ _).1.mpr fun α hα => (hsign α hα).mpr

/-- The original Borel's actual pullback inclusion represents the Borel selected
from the pulled-back pinning. -/
theorem isRepresentedBy_baseChange_negativeBorelHom :
    (Dynamic.parabolic
      (Dynamic.oppositeCocharacter (p.baseChange (F := K)).positiveGm)).IsRepresentedBy
        ((GroupScheme.baseChange b).map p.negativeBorelHom) := by
  have h := p.isRepresentedBy_negativeBorelHom.baseChange b
  rwa [← Dynamic.parabolic_baseChange, p.parabolic_baseChange_opposite_positiveGm] at h

/-- An actual inclusion-preserving comparison, despite independent choices of
positive cocharacters in the two pinnings. -/
def negativeBorelBaseChangeIso :
    (GroupScheme.baseChange b).obj p.negativeBorel ≅
      (p.baseChange (F := K)).negativeBorel :=
  p.isRepresentedBy_baseChange_negativeBorelHom.isoOfIsRepresentedBy
    (p.baseChange (F := K)).isRepresentedBy_negativeBorelHom

theorem negativeBorelBaseChangeIso_hom_comp :
    (p.negativeBorelBaseChangeIso (K := K)).hom ≫
        (p.baseChange (F := K)).negativeBorelHom =
      (GroupScheme.baseChange b).map p.negativeBorelHom :=
  p.isRepresentedBy_baseChange_negativeBorelHom.isoOfIsRepresentedBy_hom_comp
    (p.baseChange (F := K)).isRepresentedBy_negativeBorelHom

/-- The comparison identifies the subgroup ranges on all relative tests. -/
theorem range_baseChange_negativeBorelHom :
    SubgroupFunctor.range ((GroupScheme.baseChange b).map p.negativeBorelHom) =
      SubgroupFunctor.range (p.baseChange (F := K)).negativeBorelHom := by
  rw [← p.negativeBorelBaseChangeIso_hom_comp]
  exact SubgroupFunctor.range_iso_comp (p.negativeBorelBaseChangeIso (K := K)) _

end Langlands.GroupScheme.SplitPinning
