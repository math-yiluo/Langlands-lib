import Langlands.Geometry.FormalGroup.DeligneDeterminantSubsheaf
import Langlands.Geometry.FormalGroup.DeligneAdmissibleBaseChange
import Langlands.Geometry.FormalGroup.DeligneValuedReframe

/-! # Actual determinant subobjects in Deligne admissibility -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory _root_.AlgebraicGeometry

namespace Langlands.DeligneFormalSpace

variable {O : Type u} [CommRing O] {d : ℕ} [NeZero d] {π : O}
  {F : Type u} [Field F] [Algebra O F] {S S' : Scheme.{u}}
  {φ : O →+* Γ(S, ⊤)}

namespace SheafPreDatum

variable (D : SheafPreDatum d π F φ) (hπ : algebraMap O F π ≠ 0)

/-- Equality of the actual determinant subobjects survives every scheme base change. -/
theorem DeterminantSubsheavesNormalized.pullback
    (h : D.DeterminantSubsheavesNormalized hπ) (f : S' ⟶ S) :
    (D.pullback f).DeterminantSubsheavesNormalized hπ :=
  ((D.pullback f).determinantSubsheavesNormalized_iff hπ).mpr
    (DeterminantNormalized.pullback D hπ
      ((D.determinantSubsheavesNormalized_iff hπ).mp h) f)

/-- The three source conditions, with (c) an equality of actual sheaf subobjects. -/
def SubsheafAdmissible : Prop :=
  D.ConstantOnPiZeroLoci ∧ D.ResidueFibreInjective ∧
    D.DeterminantSubsheavesNormalized hπ

/-- The existing admissibility predicate is exactly the actual three-condition predicate. -/
theorem subsheafAdmissible_iff :
    D.SubsheafAdmissible hπ ↔ D.Admissible hπ := by
  unfold SubsheafAdmissible Admissible
  rw [D.determinantSubsheavesNormalized_iff hπ]

/-- All three source conditions in the actual subsheaf formulation survive base change. -/
theorem SubsheafAdmissible.pullback (h : D.SubsheafAdmissible hπ) (f : S' ⟶ S) :
    (D.pullback f).SubsheafAdmissible hπ :=
  ⟨ConstantOnPiZeroLoci.pullback D f h.1,
    D.residueFibreInjective_pullback f h.2.1,
    DeterminantSubsheavesNormalized.pullback D hπ h.2.2 f⟩

/-- Every determinant-corrected shift and reframe preserves the actual conditions. -/
theorem subsheafAdmissible_shiftReframe_iff (p : shiftReframeSubgroup (d := d) hπ) :
    (D.shiftReframe hπ p.val.1 p.val.2.toAdd).SubsheafAdmissible hπ ↔
      D.SubsheafAdmissible hπ := by
  rw [subsheafAdmissible_iff, subsheafAdmissible_iff]
  exact D.admissible_shiftReframe_iff hπ p

end SheafPreDatum

namespace SheafDatum

variable (hπ : algebraMap O F π ≠ 0)

/-- An existing admissible object satisfies the literal equality of determinant subobjects. -/
theorem determinantSubsheavesNormalized
    (D : SheafDatum (d := d) (π := π) (φ := φ) hπ) :
    D.val.DeterminantSubsheavesNormalized hπ :=
  (D.val.determinantSubsheavesNormalized_iff hπ).mpr D.property.2.2

/-- Existing admissible representatives satisfy all three source conditions as subsheaves. -/
theorem subsheafAdmissible (D : SheafDatum (d := d) (π := π) (φ := φ) hπ) :
    D.val.SubsheafAdmissible hπ :=
  (D.val.subsheafAdmissible_iff hπ).mpr D.property

/-- Source conditions with actual determinant subobjects construct an existing admissible object. -/
def ofSubsheafAdmissible (D : SheafPreDatum d π F φ) (h : D.SubsheafAdmissible hπ) :
    SheafDatum (d := d) (π := π) (φ := φ) hπ :=
  ⟨D, (D.subsheafAdmissible_iff hπ).mp h⟩

@[simp]
theorem ofSubsheafAdmissible_val
    (D : SheafPreDatum d π F φ) (h : D.SubsheafAdmissible hπ) :
    (ofSubsheafAdmissible hπ D h).val = D := rfl

/-- The new constructor commutes with the established admissible base change. -/
theorem pullback_ofSubsheafAdmissible (f : S' ⟶ S)
    (D : SheafPreDatum d π F φ) (h : D.SubsheafAdmissible hπ) :
    pullback hπ f (ofSubsheafAdmissible hπ D h) =
      ofSubsheafAdmissible hπ (D.pullback f)
        (SheafPreDatum.SubsheafAdmissible.pullback D hπ h f) :=
  Subtype.ext rfl

end SheafDatum

namespace SheafPreDatum

variable [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O F]

/-- The full DVR-normalized general linear operation preserves the actual source conditions. -/
theorem subsheafAdmissible_normalizedReframe_iff
    (D : SheafPreDatum d π F φ) (hπ : Irreducible π)
    (g : (Fin d → F) ≃ₗ[F] (Fin d → F)) :
    (D.shiftReframe (coefficientUniformizer_ne_zero (F := F) hπ) g
      (-(coefficientOrder O F (LinearEquiv.det g)).toAdd)).SubsheafAdmissible
        (coefficientUniformizer_ne_zero (F := F) hπ) ↔
      D.SubsheafAdmissible (coefficientUniformizer_ne_zero (F := F) hπ) := by
  rw [subsheafAdmissible_iff, subsheafAdmissible_iff]
  exact D.admissible_normalizedReframe_iff hπ g

end SheafPreDatum

end Langlands.DeligneFormalSpace
