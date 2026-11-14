import Langlands.Geometry.FormalGroup.DeligneDeterminantBaseChange
import Langlands.Geometry.FormalGroup.DeligneConstantLocusBaseChange
import Langlands.Geometry.FormalGroup.DeligneResidueFibreBaseChange
import Langlands.Geometry.FormalGroup.DeligneFourDataCoherence

/-! # Actual pullback of admissible Deligne data and their isomorphism classes -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory _root_.AlgebraicGeometry

namespace Langlands.DeligneFormalSpace

variable {O : Type u} [CommRing O] {d : ℕ} [NeZero d] {π : O}
  {F : Type u} [Field F] [Algebra O F] {S S' S'' : Scheme.{u}}
  {φ : O →+* Γ(S, ⊤)}

namespace SheafPreDatum

/-- All three actual admissibility conditions are preserved by arbitrary scheme base change. -/
theorem admissible_pullback (D : SheafPreDatum d π F φ)
    (hπ : algebraMap O F π ≠ 0) (h : D.Admissible hπ) (f : S' ⟶ S) :
    (D.pullback f).Admissible hπ :=
  ⟨SheafPreDatum.ConstantOnPiZeroLoci.pullback D f h.1,
    D.residueFibreInjective_pullback f h.2.1,
    SheafPreDatum.DeterminantNormalized.pullback D hπ h.2.2 f⟩

end SheafPreDatum

namespace SheafDatum

variable (hπ : algebraMap O F π ≠ 0)

/-- Actual pullback of an admissible eta,T,u,r datum, with its three proved conditions. -/
def pullback (f : S' ⟶ S) (D : SheafDatum (d := d) (π := π) (φ := φ) hπ) :
    SheafDatum (d := d) (π := π) (φ := pulledGlobalScalar f φ) hπ :=
  ⟨D.val.pullback f, D.val.admissible_pullback hπ D.property f⟩

@[simp]
theorem pullback_val (f : S' ⟶ S) (D : SheafDatum (d := d) (π := π) (φ := φ) hπ) :
    (pullback hπ f D).val = D.val.pullback f := rfl

namespace IsoClass

/-- Pullback on actual admissible classes is independent of the chosen representative. -/
def pullback (f : S' ⟶ S) :
    IsoClass (d := d) (π := π) (φ := φ) hπ →
      IsoClass (d := d) (π := π) (φ := pulledGlobalScalar f φ) hπ :=
  Quotient.map (SheafDatum.pullback hπ f)
    (fun _ _ ⟨e⟩ => ⟨SheafPreDatum.pullbackIso f e⟩)

@[simp]
theorem pullback_mk (f : S' ⟶ S) (D : SheafDatum (d := d) (π := π) (φ := φ) hπ) :
    pullback hπ f (mk hπ D) = mk hπ (SheafDatum.pullback hπ f D) := rfl

/-- Forgetting admissibility commutes with the actual pullback on classes. -/
@[simp]
theorem toPreliminary_pullback (f : S' ⟶ S)
    (x : IsoClass (d := d) (π := π) (φ := φ) hπ) :
    toPreliminary hπ (pullback hπ f x) =
      SheafPreDatum.IsoClass.pullback f (toPreliminary hπ x) := by
  induction x using Quotient.inductionOn with
  | h D => rfl

/-- Identity pullback acts as the identity on actual admissible classes. -/
@[simp]
theorem pullback_id (x : IsoClass (d := d) (π := π) (φ := φ) hπ) :
    pullback hπ (𝟙 S) x = x := by
  induction x using Quotient.inductionOn with
  | h D => exact Quotient.sound ⟨D.val.pullbackIdIso⟩

/-- Successive pullbacks equal pullback along the composite on actual admissible classes. -/
theorem pullback_comp (f : S' ⟶ S) (g : S'' ⟶ S')
    (x : IsoClass (d := d) (π := π) (φ := φ) hπ) :
    pullback hπ g (pullback hπ f x) = pullback hπ (g ≫ f) x := by
  induction x using Quotient.inductionOn with
  | h D => exact Quotient.sound ⟨D.val.pullbackCompIso f g⟩

end IsoClass

end SheafDatum

end Langlands.DeligneFormalSpace
