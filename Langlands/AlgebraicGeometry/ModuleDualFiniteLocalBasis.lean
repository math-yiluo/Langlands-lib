import Langlands.AlgebraicGeometry.FiniteLocalBasisStatements
import Langlands.AlgebraicGeometry.ModuleDualLocalFree

/-! # Finite local bases and rank of the actual internal dual -/

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Scheme.Modules

noncomputable section

variable {X : AlgebraicGeometry.Scheme.{u}} {M : X.Modules}

/-- Dual generators use the same cover and the same finite basis index types. -/
def dualLocalGeneratorsData (q : SheafOfModules.LocalGeneratorsData.{u} M)
    [hfree : q.IsLocallyFreeData] [hq : q.IsFiniteType] :
    SheafOfModules.LocalGeneratorsData.{u} (dual M) where
  I := q.I
  X := q.X
  coversTop := q.coversTop
  generators i := by
    letI := hq.isFiniteType i
    letI := hfree.isIso i
    exact {
      I := (q.generators i).I
      s := ((dual M).over (q.X i)).freeHomEquiv
        (dualLocalFreeIso (asIso (q.generators i).π)).hom
      epi := by
        simpa only [Equiv.symm_apply_apply] using
          (inferInstance : Epi (dualLocalFreeIso (asIso (q.generators i).π)).hom) }

lemma dualLocalGeneratorsData_isLocallyFreeData
    (q : SheafOfModules.LocalGeneratorsData.{u} M)
    [hfree : q.IsLocallyFreeData] [hq : q.IsFiniteType] :
    (dualLocalGeneratorsData q).IsLocallyFreeData where
  isIso i := by
    let := hq.isFiniteType i
    let := hfree.isIso i
    change IsIso (((dual M).over (q.X i)).freeHomEquiv.symm
      (((dual M).over (q.X i)).freeHomEquiv
        (dualLocalFreeIso (asIso (q.generators i).π)).hom))
    simpa only [Equiv.symm_apply_apply] using
      (inferInstance : IsIso (dualLocalFreeIso (asIso (q.generators i).π)).hom)

lemma dualLocalGeneratorsData_isFiniteType
    (q : SheafOfModules.LocalGeneratorsData.{u} M)
    [q.IsLocallyFreeData] [hq : q.IsFiniteType] :
    (dualLocalGeneratorsData q).IsFiniteType where
  isFiniteType i := by
    refine ⟨?_⟩
    change Finite (q.generators i).I
    exact (hq.isFiniteType i).finite

/-- The internal dual preserves the existence of one finite local basis witness. -/
theorem dual_hasFiniteLocalBasis
    (h : ∃ q : SheafOfModules.LocalGeneratorsData.{u} M,
      q.IsLocallyFreeData ∧ q.IsFiniteType) :
    ∃ q : SheafOfModules.LocalGeneratorsData.{u} (dual M),
      q.IsLocallyFreeData ∧ q.IsFiniteType := by
  obtain ⟨q, hfree, hfinite⟩ := h
  let : q.IsLocallyFreeData := hfree
  let : q.IsFiniteType := hfinite
  exact ⟨dualLocalGeneratorsData q, dualLocalGeneratorsData_isLocallyFreeData q,
    dualLocalGeneratorsData_isFiniteType q⟩

/-- The internal dual preserves every specified finite local rank. -/
theorem isLocallyFreeOfRank_dual {n : ℕ} (h : IsLocallyFreeOfRank M n) :
    IsLocallyFreeOfRank (dual M) n := by
  obtain ⟨q, hfree, hrank⟩ := h
  let : q.IsLocallyFreeData := hfree
  let : q.IsFiniteType := {
    isFiniteType := fun i => {
      finite := Finite.of_equiv (Fin n) (hrank i).some.symm } }
  exact ⟨dualLocalGeneratorsData q, dualLocalGeneratorsData_isLocallyFreeData q, hrank⟩

/-- Exact combined preservation statement for the actual internal dual. -/
theorem dualFiniteLocalBasisRank : DualFiniteLocalBasisRankStatement.{u} := by
  intro X M
  exact ⟨dual_hasFiniteLocalBasis, fun _ => isLocallyFreeOfRank_dual⟩

end

end Langlands.Scheme.Modules
