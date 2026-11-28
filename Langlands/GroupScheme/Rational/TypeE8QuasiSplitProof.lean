import Langlands.GroupScheme.Rational.NumberFieldTypeE8TotallyComplexInputs
import Langlands.GroupScheme.Rational.QuasiSplitInnerFormExistenceProof
import Langlands.GroupScheme.LocalGroupIsoBaseChangeRecovery
import Langlands.GroupScheme.SimplyConnected.CenterCharacterCartan
import Langlands.GroupScheme.SimplyConnected.TrivialCenterCharacters
import Langlands.GroupScheme.Reductive.TitsIndexCartanIsoComparison
import Langlands.GroupScheme.Reductive.TitsIndexExistenceProof
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleFactorDescentProperties
import Langlands.GroupScheme.Rational.QuasiSplitSplittingReduction
import Langlands.GroupScheme.Reductive.GeometricSimplyConnected
import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.LinearAlgebra.CartanENumbering

/-! # Groups of type `E_8` are quasi-split when the quasi-split ones have trivial cocycles -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- **Quasi-splitness in type `E_8` from the cohomology of the quasi-split forms**
(Platonov–Rapinchuk, Proposition 6.16(A)). -/
theorem typeE8QuasiSplitOfQuasiSplitCohomology :
    TypeE8QuasiSplitOfQuasiSplitCohomologyStatement.{u} := by
  intro K _ G _ _ d e hsc habs hE8 hvan
  obtain ⟨Q⟩ := quasiSplitInnerFormExistence K G hsc.isSemisimple.isConnectedReductive
  apply Q.isQuasiSplit_of_isTrivial
  have hR : IsConnectedReductive Q.model := Q.isAdjointQuotient.isConnectedReductive
  let : IsAffineHom Q.model.X.hom := hR.isAffineHom
  let : Smooth Q.model.X.hom := hR.smooth
  let φ := Q.localIso.toBaseChangeIso
  have hscM : IsSimplyConnected Q.model :=
    (isSimplyConnected_fieldExtension_iff (K := Q.carrier) Q.model).mp
      (IsSimplyConnected.of_iso φ ((isSimplyConnected_fieldExtension_iff G).mpr hsc))
  have habsM : IsAbsolutelyAlmostSimple Q.model :=
    IsAbsolutelyAlmostSimple.of_fieldExtension (K := Q.carrier)
      (IsAbsolutelyAlmostSimple.of_iso φ
        (IsAbsolutelyAlmostSimple.baseChange_of_algebraicExtension habs))
  obtain ⟨dM⟩ := titsIndexExistence K Q.model hscM.isSemisimple
  obtain ⟨v, hv⟩ := dM.exists_cartanEquiv_of_separableClosureIso d
    (separableClosureIsoOfBaseChangeIso φ)
  let eM := v.trans e
  have hE8M : ∀ a b, dM.cartan a b = CartanMatrix.E 8 (eM a) (eM b) :=
    fun a b => (hv a b).symm.trans (hE8 (v a) (v b))
  have hc := dM.natCard_centerCharacter_eq_cartanDet hscM eM (CartanMatrix.E 8) hE8M
  rw [CartanMatrix.E₈_det] at hc
  have hsub := (Nat.card_eq_one_iff_unique.mp hc).1
  have : IsIso Q.quotient :=
    Q.isAdjointQuotient.isIso_of_killsCenter_id (dM.killsCenter_id hsub)
  obtain ⟨f, hf⟩ := hvan Q.model dM eM hscM habsM hE8M Q.isQuasiSplit Q.carrier
    (Q.cocycle.map (inv Q.quotient))
  refine ⟨f ≫ Q.quotient.hom.hom, fun a b => ?_⟩
  have hinv : (inv Q.quotient).hom.hom ≫ Q.quotient.hom.hom = 𝟙 _ := by
    rw [← Grp.comp_hom_hom, IsIso.inv_hom_id, Grp.id_hom_hom]
  calc Q.cocycle.toFun a b =
        (Q.cocycle.toFun a b ≫ (inv Q.quotient).hom.hom) ≫ Q.quotient.hom.hom := by
        rw [Category.assoc, hinv, Category.comp_id]
    _ = ((a ≫ f) * (b ≫ f)⁻¹) ≫ Q.quotient.hom.hom := by
        rw [← hf a b]
        rfl
    _ = (a ≫ f ≫ Q.quotient.hom.hom) * (b ≫ f ≫ Q.quotient.hom.hom)⁻¹ := by
        rw [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, Category.assoc]

end Langlands.GroupScheme
