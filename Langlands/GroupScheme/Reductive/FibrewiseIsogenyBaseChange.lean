import Langlands.GroupScheme.Reductive.FibrewiseIsogenyReduction
import Langlands.GroupScheme.Descent.Data
import Langlands.AbelianScheme.MultiplicationSign

/-! # Fibrewise isogenies at field-valued points and under base change -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

variable {S T U : Scheme.{u}} {G H : GroupScheme S}

/-- The specified homomorphism is an isogeny at every field-valued point of the base. -/
def IsFieldwiseIsogeny (f : G ⟶ H) : Prop :=
  ∀ (k : Type u) [Field k] (b : Spec (CommRingCat.of k) ⟶ S),
    IsIsogeny ((baseChange b).map f)

/-- Isogenies of a specified map agree under the direct/iterated pullback comparison. -/
theorem isogeny_baseChange_comp_iff (b : T ⟶ S) (c : U ⟶ T) (f : G ⟶ H) :
    IsIsogeny ((baseChange c).map ((baseChange b).map f)) ↔
      IsIsogeny ((baseChange (c ≫ b)).map f) := by
  let eG := Descent.pullbackComparison b c (c ≫ b) rfl G
  let eH := Descent.pullbackComparison b c (c ≫ b) rfl H
  constructor
  · intro h
    have ht := ((isIsogeny_of_isIso eG.inv).comp h).comp
      (isIsogeny_of_isIso eH.hom)
    change IsIsogeny ((eG.inv ≫
      (baseChange c).map ((baseChange b).map f)) ≫ eH.hom) at ht
    rw [Category.assoc, Descent.pullbackComparison_naturality,
      Iso.inv_hom_id_assoc] at ht
    exact ht
  · intro h
    have ht := ((isIsogeny_of_isIso eG.hom).comp h).comp
      (isIsogeny_of_isIso eH.inv)
    change IsIsogeny ((eG.hom ≫ (baseChange (c ≫ b)).map f) ≫ eH.inv) at ht
    rw [← Descent.pullbackComparison_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id] at ht
    exact ht

/-- Residue-field isogenies give an isogeny at every actual field-valued point. -/
theorem IsFibrewiseIsogeny.isFieldwiseIsogeny {f : G ⟶ H}
    (hf : IsFibrewiseIsogeny f) : IsFieldwiseIsogeny f := by
  intro k _ b
  let s := b (IsLocalRing.closedPoint k)
  let φ : S.residueField s ⟶ CommRingCat.of k :=
    S.descResidueField (Scheme.stalkClosedPointTo b)
  have h := (isogeny_baseChange_comp_iff
    (S.fromSpecResidueField s) (Spec.map φ) f).mp ((hf s).baseChange (Spec.map φ))
  have hfactor : Spec.map φ ≫ S.fromSpecResidueField s = b :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k S b
  rwa [hfactor] at h

/-- Field-valued points and residue-field fibres give equivalent isogeny conditions. -/
theorem isFieldwiseIsogeny_iff_isFibrewiseIsogeny (f : G ⟶ H) :
    IsFieldwiseIsogeny f ↔ IsFibrewiseIsogeny f := by
  exact ⟨fun hf s => hf (S.residueField s) (S.fromSpecResidueField s),
    fun hf => hf.isFieldwiseIsogeny⟩

/-- Every isogeny is fieldwise an isogeny. -/
theorem IsIsogeny.isFieldwiseIsogeny {f : G ⟶ H} (hf : IsIsogeny f) :
    IsFieldwiseIsogeny f := by
  intro k _ b
  exact hf.baseChange b

/-- The field-valued-point condition is preserved by every scheme base change. -/
theorem IsFieldwiseIsogeny.baseChange {f : G ⟶ H} (hf : IsFieldwiseIsogeny f)
    (b : T ⟶ S) : IsFieldwiseIsogeny ((baseChange b).map f) := by
  intro k _ c
  exact (isogeny_baseChange_comp_iff b c f).mpr (hf k (c ≫ b))

/-- Fibrewise isogenies are preserved by arbitrary scheme base change. -/
theorem IsFibrewiseIsogeny.baseChange {f : G ⟶ H} (hf : IsFibrewiseIsogeny f)
    (b : T ⟶ S) : IsFibrewiseIsogeny ((baseChange b).map f) :=
  (isFieldwiseIsogeny_iff_isFibrewiseIsogeny _).mp
    (hf.isFieldwiseIsogeny.baseChange b)

end Langlands.GroupScheme
