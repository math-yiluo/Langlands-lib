import Langlands.ClassField.Global.CommonGaloisOverfield
import Langlands.ClassField.Global.IdeleRegularExtension

/-! # The subgroup of regular idele-class cohomology classes -/

noncomputable section

namespace Langlands.ClassField.Global

universe u

variable (F E : Type u) [Field F] [Field E] [NumberField F] [NumberField E]
  [Algebra F E] [IsGalois F E]

/-- An idele-class cohomology class is regular if its inflation to some finite
Galois overfield is represented by an idele cohomology class. -/
def IsRegularIdeleClass (c : relativeIdeleClassCohomology F E 2) : Prop :=
  ∃ (L : Type u) (_ : Field L) (_ : NumberField L) (_ : Algebra F L)
    (_ : Algebra E L) (_ : IsScalarTower F E L) (_ : IsGalois F L),
    c ∈ ideleClassRegularSubgroup F E L

omit [NumberField F] in
/-- A representative in any specified extension witnesses regularity. -/
theorem isRegularIdeleClass_of_mem {L : Type u} [Field L] [NumberField L]
    [Algebra F L] [Algebra E L] [IsScalarTower F E L] [IsGalois F L]
    {c : relativeIdeleClassCohomology F E 2} (hc : c ∈ ideleClassRegularSubgroup F E L) :
    IsRegularIdeleClass F E c :=
  ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hc⟩

/-- Two regular classes have a common finite Galois extension in which both
inflations are represented by idele cohomology. -/
theorem isRegularIdeleClass_common_extension {c d : relativeIdeleClassCohomology F E 2}
    (hc : IsRegularIdeleClass F E c) (hd : IsRegularIdeleClass F E d) :
    ∃ (M : Type u) (_ : Field M) (_ : NumberField M) (_ : Algebra F M)
      (_ : Algebra E M) (_ : IsScalarTower F E M) (_ : IsGalois F M),
      c ∈ ideleClassRegularSubgroup F E M ∧ d ∈ ideleClassRegularSubgroup F E M := by
  rcases hc with ⟨L₁, _, _, _, _, _, _, hc⟩
  rcases hd with ⟨L₂, _, _, _, _, _, _, hd⟩
  let M := commonGaloisOverfield F E L₁ L₂
  exact ⟨M.carrier, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance,
    ideleClassRegularSubgroup_le F E L₁ M.carrier hc,
    ideleClassRegularSubgroup_le F E L₂ M.carrier hd⟩

/-- The regular classes form an additive subgroup of the actual idele-class `H²`. -/
def regularIdeleClassSubgroup : AddSubgroup (relativeIdeleClassCohomology F E 2) where
  carrier := IsRegularIdeleClass F E
  zero_mem' := isRegularIdeleClass_of_mem F E (L := E)
    (ideleClassRegularSubgroup F E E).zero_mem
  add_mem' := by
    intro c d hc hd
    rcases isRegularIdeleClass_common_extension F E hc hd with
      ⟨M, _, _, _, _, _, _, hc, hd⟩
    exact isRegularIdeleClass_of_mem F E ((ideleClassRegularSubgroup F E M).add_mem hc hd)
  neg_mem' := by
    intro c hc
    rcases hc with ⟨L, _, _, _, _, _, _, hc⟩
    exact isRegularIdeleClass_of_mem F E ((ideleClassRegularSubgroup F E L).neg_mem hc)

@[simp]
theorem mem_regularIdeleClassSubgroup_iff (c : relativeIdeleClassCohomology F E 2) :
    c ∈ regularIdeleClassSubgroup F E ↔ IsRegularIdeleClass F E c := Iff.rfl

/-- Regularity in a specified overfield implies regularity. -/
theorem ideleClassRegularSubgroup_le_regularIdeleClassSubgroup
    (L : Type u) [Field L] [NumberField L] [Algebra F L] [Algebra E L]
    [IsScalarTower F E L] [IsGalois F L] :
    ideleClassRegularSubgroup F E L ≤ regularIdeleClassSubgroup F E :=
  fun _ hc => isRegularIdeleClass_of_mem F E hc

/-- Classes already represented by ideles are regular. -/
theorem quotient_range_le_regularIdeleClassSubgroup :
    (ideleQuotientCohomologyMap F E 2).hom.toAddMonoidHom.range ≤
      regularIdeleClassSubgroup F E :=
  (quotient_range_le_ideleClassRegularSubgroup F E E).trans
    (ideleClassRegularSubgroup_le_regularIdeleClassSubgroup F E E)

end Langlands.ClassField.Global
