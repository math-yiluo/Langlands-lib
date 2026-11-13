import Langlands.GroupScheme.Quaternionic.OrdinaryOrthogonalGeometryStatement
import Langlands.GroupScheme.Quaternionic.QuaternionicMoritaIsometryStatement
import Langlands.GroupScheme.Quaternionic.SpinCoverReduction
import Langlands.GroupScheme.Quaternionic.SpinCoverProperties
import Langlands.GroupScheme.Quaternionic.IsometrySplitRank
import Langlands.LocalField.ValuativeInfinite

/-! # Reduction of local quaternionic spin groups to two geometric statements -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Quaternionic

/-- The ordinary orthogonal and Morita statements descend smoothness and absolute
almost simplicity to the actual quaternionic connected isometry group. -/
theorem FirstKindInvolution.smooth_and_isAbsolutelyAlmostSimple_of_geometry
    (hordinary : OrdinaryOrthogonalGeometryStatement.{u})
    (hmorita : QuaternionicMoritaIsometryStatement.{u})
    {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
    [Algebra.IsCentral K D] [FiniteDimensional K D]
    (σ : FirstKindInvolution K D) (hD : Module.finrank K D = 4)
    (hσ : Module.finrank K σ.symmetricSubspace = 3)
    (m : ℕ) (hm : 3 ≤ m) (q : σ.QuadraticForms (Fin m))
    (hq : σ.IsNondegenerateQuadratic q) :
    ∃ hsm : Smooth (σ.isometryGroup q).X.hom,
      letI := hsm
      IsAbsolutelyAlmostSimple (σ.connectedIsometryGroup q) := by
  obtain ⟨Q, hQ, ⟨e⟩⟩ := hmorita K D hD σ hσ m q hq
  obtain ⟨hsm, hH⟩ := hordinary (AlgebraicClosure K) m hm Q hQ
  let := hsm
  exact IdentityComponent.smooth_and_isAbsolutelyAlmostSimple_of_fieldExtension_iso e hH

/-- The two published geometric propositions suffice for the exact local spin
rank-one proposition. This implication does not assert either geometric input. -/
def LocalSpinRankOneReductionStatement : Prop :=
  OrdinaryOrthogonalGeometryStatement.{u} →
    QuaternionicMoritaIsometryStatement.{u} →
      LocalSpinRankOneStatement.{u}

/-- Descent, semisimple cover existence and the published rank comparison prove
the reduction without a characteristic restriction. -/
theorem localSpinRankOneReduction : LocalSpinRankOneReductionStatement.{u} := by
  intro hordinary hmorita K _ _ _ _ D _ _ _ _ hD σ hσ m hm q hq hi
  let : Infinite K := Langlands.LocalField.infinite_of_isNonarchimedeanLocalField K
  have hm3 : 3 ≤ m := by
    rcases hm with rfl | rfl <;> omega
  obtain ⟨hsm, hG⟩ :=
    σ.smooth_and_isAbsolutelyAlmostSimple_of_geometry hordinary hmorita hD hσ m hm3 q hq
  let := hsm
  refine ⟨σ.exists_isSpinCover_of_isSemisimple q hG.1.isSemisimple, ?_⟩
  intro S π hπ
  exact hπ.properties_of_connectedIsometryGroup hG.1
    (σ.splitRank_connectedIsometryGroup_eq_one q hq hi)

end Langlands.GroupScheme.Quaternionic
