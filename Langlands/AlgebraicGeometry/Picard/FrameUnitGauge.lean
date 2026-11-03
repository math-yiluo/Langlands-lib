import Langlands.AlgebraicGeometry.Picard.DualNumberAffineFrames
import Langlands.AlgebraicGeometry.Picard.CocycleLineBundleFrame

/-! # Changing local frames by units -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard.CocycleGluing

variable {X : Scheme.{u}} {M : X.Modules} {ι : Type u} {T : ι → X.Opens}

/-- Change each frame by the inverse of its specified local unit. -/
def unitGaugeFrames (e : ∀ i, Γ(M, T i)) (a : ∀ i, Γ(X, T i)ˣ) :
    ∀ i, Γ(M, T i) :=
  fun i => (((a i)⁻¹ : Γ(X, T i)ˣ) : Γ(X, T i)) • e i

/-- The transitions after changing each frame by an inverse unit. -/
def unitGaugeCocycle (g : ∀ i j, Γ(X, T i ⊓ T j)ˣ) (a : ∀ i, Γ(X, T i)ˣ) :
    ∀ i j, Γ(X, T i ⊓ T j)ˣ :=
  fun i j =>
    Units.map (X.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ≤ T i)).op).hom.toMonoidHom
      (a i) * g i j *
    (Units.map (X.presheaf.map (homOfLE (inf_le_right : T i ⊓ T j ≤ T j)).op).hom.toMonoidHom
      (a j))⁻¹

theorem unitGaugeFrames_isFrame (e : ∀ i, Γ(M, T i))
    (he : ∀ i, Scheme.Modules.IsFrameOn (e i) (T i))
    (a : ∀ i, Γ(X, T i)ˣ) (i : ι) :
    Scheme.Modules.IsFrameOn (unitGaugeFrames e a i) (T i) :=
  DualNumberThickening.isFrameOn_smul_unit (e i) (he i) (a i)⁻¹

/-- The unit formula agrees with the transition relation for the changed frames. -/
theorem isTransition_unitGaugeFrames {e : ∀ i, Γ(M, T i)}
    {g : ∀ i j, Γ(X, T i ⊓ T j)ˣ} (htrans : IsTransition e g)
    (a : ∀ i, Γ(X, T i)ˣ) :
    IsTransition (unitGaugeFrames e a) (unitGaugeCocycle g a) := by
  intro i j
  let ai := Units.map
    (X.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ≤ T i)).op).hom.toMonoidHom (a i)
  let aj := Units.map
    (X.presheaf.map (homOfLE (inf_le_right : T i ⊓ T j ≤ T j)).op).hom.toMonoidHom (a j)
  have hunit : aj⁻¹ * g i j = (ai * g i j * aj⁻¹) * ai⁻¹ := by
    symm
    calc
      (ai * g i j * aj⁻¹) * ai⁻¹ = (ai * ai⁻¹) * (aj⁻¹ * g i j) := by ac_rfl
      _ = aj⁻¹ * g i j := by rw [mul_inv_cancel, one_mul]
  have hval := congrArg (fun z : Γ(X, T i ⊓ T j)ˣ => (z : Γ(X, T i ⊓ T j))) hunit
  simp only [Units.val_mul] at hval
  simp only [unitGaugeFrames, Scheme.Modules.map_smul, htrans i j, smul_smul]
  apply congrArg (fun r : Γ(X, T i ⊓ T j) =>
    r • M.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ≤ T i)).op (e i))
  change ((aj⁻¹ : Γ(X, T i ⊓ T j)ˣ) : Γ(X, T i ⊓ T j)) * (g i j : Γ(X, T i ⊓ T j)) =
    ((ai * g i j * aj⁻¹ : Γ(X, T i ⊓ T j)ˣ) : Γ(X, T i ⊓ T j)) *
      ((ai⁻¹ : Γ(X, T i ⊓ T j)ˣ) : Γ(X, T i ⊓ T j))
  exact hval

/-- The canonical frame cocycle of the changed frames is the unit gauge
of the original canonical frame cocycle. -/
theorem frameCocycle_unitGaugeFrames (e : ∀ i, Γ(M, T i))
    (he : ∀ i, Scheme.Modules.IsFrameOn (e i) (T i)) (a : ∀ i, Γ(X, T i)ˣ) :
    frameCocycle (unitGaugeFrames e a) (unitGaugeFrames_isFrame e he a) =
      unitGaugeCocycle (frameCocycle e he) a :=
  IsTransition.unique (unitGaugeFrames_isFrame e he a)
    (isTransition_frameCocycle (unitGaugeFrames_isFrame e he a))
    (isTransition_unitGaugeFrames (isTransition_frameCocycle he) a)

end Langlands.AlgebraicGeometry.Picard.CocycleGluing
