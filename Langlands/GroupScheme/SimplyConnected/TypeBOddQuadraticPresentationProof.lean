import Langlands.GroupScheme.SimplyConnected.TypeBOddQuadraticPresentationStatement
import Langlands.GroupScheme.SimplyConnected.TypeBVectorQuotient
import Langlands.GroupScheme.OddOrthogonalForm.GroupDescent
import Langlands.GroupScheme.OddOrthogonalForm.Regularity
import Langlands.GroupScheme.CentralIsogeny.Transport
import Langlands.GroupScheme.Rational.CentralIsogenySplitRank

/-! # The actual odd quadratic presentation in type B -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open OddOrthogonalForm
open Quaternionic.FirstKindInvolution
open Quaternionic.ScalarNormOnePoints (reindexForm reindexGroupIso radicalFree_reindexForm
  finrank_polarKer_reindexForm)

/-- The actual odd quadratic presentation of simply connected type-B groups,
over every ground field and with its full scheme-theoretic central isogeny. -/
theorem typeBOddQuadraticPresentation : TypeBOddQuadraticPresentationStatement.{u} := by
  classical
  intro K _ G _ _ d n e hn hsc _has hB
  have hn₂ : 2 ≤ n := by omega
  let R := d.typeBVectorQuotientRecovery n e hn₂ hsc hB
  have : IsAffine R.obj.X.left := R.isAffine
  have : IsAffineHom R.obj.X.hom := inferInstance
  obtain ⟨N, _, _, _, _, ⟨φ⟩⟩ := exists_galois_localIso K R.obj n R.iso
  let a : OddOrthogonalMatrix.Index (Fin n) ≃ Fin (2 * n + 1) :=
    Fintype.equivFinOfCardEq (by
      simp only [OddOrthogonalMatrix.Index, Fintype.card_sum, Fintype.card_unique, Fintype.card_fin]
      omega)
  let D := descendedMatrix φ hn₂
  let q := reindexForm a D
  have hq : (scalar K).IsRadicalFreeQuadratic q :=
    radicalFree_reindexForm a D (radicalFree_descendedForm φ hn₂)
  have hpolar : Module.finrank K (LinearMap.ker ((scalar K).polar q).vecMulLinear) =
      (if (2 : K) = 0 then 1 else 0) :=
    (finrank_polarKer_reindexForm a D).trans (finrank_polarKer_descendedForm φ hn₂)
  let c : R.obj ≅ (scalar K).normOneIsometryGroup q :=
    descendedGroupIso φ hn₂ ≪≫ reindexGroupIso a D
  have hπ : IsCentralIsogeny (R.hom ≫ c.hom) := R.isCentralIsogeny.comp_iso c
  refine ⟨q, hq, hpolar, ?_, R.hom ≫ c.hom, hπ⟩
  rw [hπ.splitRank_eq, splitRank_normOneIsometryGroup_eq q hq]

end Langlands.GroupScheme
