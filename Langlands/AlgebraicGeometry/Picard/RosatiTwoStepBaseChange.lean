import Langlands.AlgebraicGeometry.Picard.RosatiBaseChange

/-! # Rosati trace transport through an arbitrary intermediate field -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Preservation of the fixed geometric trace by two successive actual pullbacks. -/
def GeometricTracePreservedByTwoStepBaseChange
    {k K C : Type u} [Field k] [Field K] [Field C]
    (b : Spec (.of K) ⟶ Spec (.of k)) (c : Spec (.of C) ⟶ Spec (.of K))
    (A : AbelianScheme (Spec (.of k))) : Prop :=
  ∀ f : End0 A,
    geometricEndomorphismTrace ((baseChange c).obj ((baseChange b).obj A))
        (rationalBaseChangeHom c (rationalBaseChangeHom b f)) =
      geometricEndomorphismTrace A f

/-- Only the endpoints need to be geometric fields for two-step trace transport. -/
theorem geometricEndomorphismTrace_twoStep_baseChange_of_comparison
    (hcomparison : GeometricEndomorphismTraceComparisonStatement.{u})
    {k K C : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    [Field K] [Field C] [IsAlgClosed C] [CharZero C]
    (b : Spec (.of K) ⟶ Spec (.of k)) (c : Spec (.of C) ⟶ Spec (.of K))
    (A : AbelianScheme (Spec (.of k))) :
    GeometricTracePreservedByTwoStepBaseChange b c A := by
  intro f
  apply (algebraMap ℚ ℚ_[2]).injective
  rw [(hcomparison C ((baseChange c).obj ((baseChange b).obj A)) 2).2.2,
    (hcomparison k A 2).2.2]
  change primeEndomorphismTraceAt ((baseChange c).obj ((baseChange b).obj A))
      (Over.mk (𝟙 _)) 2 (rationalBaseChangeHom c (rationalBaseChangeHom b f)) =
    primeEndomorphismTraceAt A (Over.mk (𝟙 _)) 2 f
  rw [primeEndomorphismTraceAt_baseChange, primeEndomorphismTraceAt_baseChange]
  have hunit : IsUnit (2 : Γ(Spec (.of k), ⊤)) := by
    simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr (by norm_num : (2 : k) ≠ 0)).map
      (Scheme.ΓSpecIso (.of k)).inv.hom
  exact primeEndomorphismTraceAt_geometric A (((𝟙 _) ≫ c) ≫ b) (𝟙 _) 2 hunit f

end Langlands.AbelianScheme

namespace Langlands.AbelianScheme.Rosati

variable (hcomparison : GeometricEndomorphismTraceComparisonStatement.{u})
  (P : Prerequisites.{u})
  {k K C : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  [Field K] [Field C] [IsAlgClosed C] [CharZero C]
  (b : Spec (.of K) ⟶ Spec (.of k)) (c : Spec (.of C) ⟶ Spec (.of K))
  {A : AbelianScheme (Spec (.of k))}
  (W : DualData A) (W₁ : DualData ((baseChange b).obj A))
  (W₂ : DualData ((baseChange c).obj ((baseChange b).obj A)))
  (hadd : W.Additivity P) (hadd₁ : W₁.Additivity P) (hadd₂ : W₂.Additivity P)
  (lam : A ⟶ W.dual P)
  [hinv : HasRationalInverse P W lam]
  [hinv₁ : HasRationalInverse P W₁ (DualData.baseChangeMap P b W W₁ lam)]
  [hinv₂ : HasRationalInverse P W₂
    (DualData.baseChangeMap P c W₁ W₂ (DualData.baseChangeMap P b W W₁ lam))]

include hcomparison hadd₁ in
/-- The actual trace form transports through any intermediate field, conditional
on the existing rational trace comparison at the geometric endpoints. -/
theorem traceForm_twoStep_baseChange_of_comparison (a d : End0 A) :
    @traceForm P C _ ((baseChange c).obj ((baseChange b).obj A)) W₂ hadd₂
      (DualData.baseChangeMap P c W₁ W₂ (DualData.baseChangeMap P b W W₁ lam)) hinv₂
      (rationalBaseChangeHom c (rationalBaseChangeHom b a))
      (rationalBaseChangeHom c (rationalBaseChangeHom b d)) =
      @traceForm P k _ A W hadd lam hinv a d := by
  rw [traceForm_apply, traceForm_apply,
    involution_baseChange P c W₁ W₂ hadd₁ hadd₂,
    involution_baseChange P b W W₁ hadd hadd₁]
  change geometricEndomorphismTrace ((baseChange c).obj ((baseChange b).obj A))
    ((rationalBaseChangeEnd c ((baseChange b).obj A)) ((rationalBaseChangeEnd b A) a) *
      (rationalBaseChangeEnd c ((baseChange b).obj A))
        ((rationalBaseChangeEnd b A) (involution P W hadd lam d))) = _
  rw [← map_mul, ← map_mul]
  exact geometricEndomorphismTrace_twoStep_baseChange_of_comparison hcomparison b c A _

end Langlands.AbelianScheme.Rosati
