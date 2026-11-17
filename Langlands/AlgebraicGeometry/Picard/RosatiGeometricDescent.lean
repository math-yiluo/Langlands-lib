import Langlands.AlgebraicGeometry.Picard.RosatiDualDataBaseChange
import Langlands.AlgebraicGeometry.Picard.RosatiAmplePresentationPositiveStatement
import Langlands.AbelianScheme.RationalBaseChangeFaithfulness
import Langlands.AbelianScheme.GeometricTraceRationalLiftTransfer
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Descent of actual integral Rosati positivity from ample presentations -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AbelianScheme

/-- A nonzero actual integral homomorphism remains nonzero after any field extension. -/
theorem baseChange_map_ne_zero_field
    {k K : Type u} [Field k] [Field K]
    (b : Spec (.of K) ⟶ Spec (.of k))
    {A B : AbelianScheme (Spec (.of k))} {f : A ⟶ B} (hf : f ≠ 0) :
    (baseChange b).map f ≠ 0 := by
  have : Surjective b := ⟨fun x => ⟨Classical.choice inferInstance, Subsingleton.elim _ _⟩⟩
  let : (baseChange b).Additive := baseChange_additive b
  intro h
  apply hf
  apply baseChange_map_injective_of_faithful_over b
  exact h.trans ((baseChange b).mapAddHom.map_zero).symm

namespace Rosati

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

section Transport

variable (P : Prerequisites.{u})
  {k K L C : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  [Field K] [Field L] [Field C] [IsAlgClosed C]
  (s : Spec (.of K) ⟶ Spec (.of k))
  (b : Spec (.of L) ⟶ Spec (.of K)) (c : Spec (.of C) ⟶ Spec (.of L))
  {A : AbelianScheme (Spec (.of k))}
  (W : DualData A) (W₀ : DualData ((baseChange s).obj A))
  (W₁ : DualData ((baseChange b).obj ((baseChange s).obj A)))
  (W₂ : DualData ((baseChange c).obj ((baseChange b).obj ((baseChange s).obj A))))
  (hadd : W.Additivity P) (hadd₀ : W₀.Additivity P)
  (hadd₁ : W₁.Additivity P) (hadd₂ : W₂.Additivity P)
  (lam : A ⟶ W.dual P)
  [hinv : HasRationalInverse P W lam]
  [hinv₀ : HasRationalInverse P W₀ (DualData.baseChangeMap P s W W₀ lam)]
  [hinv₁ : HasRationalInverse P W₁
    (DualData.baseChangeMap P b W₀ W₁ (DualData.baseChangeMap P s W W₀ lam))]
  [hinv₂ : HasRationalInverse P W₂
    (DualData.baseChangeMap P c W₁ W₂
      (DualData.baseChangeMap P b W₀ W₁ (DualData.baseChangeMap P s W W₀ lam)))]

local notation "A₀" => Functor.obj (baseChange s) A
local notation "A₁" => Functor.obj (baseChange b) A₀
local notation "A₂" => Functor.obj (baseChange c) A₁
local notation "lam₀" => DualData.baseChangeMap P s W W₀ lam
local notation "lam₁" => DualData.baseChangeMap P b W₀ W₁ lam₀
local notation "lam₂" => DualData.baseChangeMap P c W₁ W₂ lam₁

include hadd₀ hadd₁ in
/-- Strict integral positivity at the final geometric field descends through
three actual field pullbacks. The intermediate fields are arbitrary. -/
theorem integralDiagonalPositive_of_threeStep_baseChange
    (hpos : @IntegralDiagonalPositive C _ A₂ P W₂ hadd₂ lam₂ hinv₂) :
    @IntegralDiagonalPositive k _ A P W hadd lam hinv := by
  intro f hf
  let f₀ : A₀ ⟶ A₀ := (baseChange s).map f
  let f₁ : A₁ ⟶ A₁ := (baseChange b).map f₀
  let f₂ : A₂ ⟶ A₂ := (baseChange c).map f₁
  have hf₀ : f₀ ≠ 0 := baseChange_map_ne_zero_field s hf
  have hf₁ : f₁ ≠ 0 := baseChange_map_ne_zero_field b hf₀
  have hf₂ : f₂ ≠ 0 := baseChange_map_ne_zero_field c hf₁
  have hp := hpos f₂ hf₂
  let F : End0 A →ₗ[ℚ] End0 A₂ :=
    (rationalBaseChangeHom c).comp
      ((rationalBaseChangeHom b).comp (rationalBaseChangeHom s))
  have hprime (a : End0 A) :
      primeEndomorphismTrace A₂ 2 (F a) = primeEndomorphismTrace A 2 a := by
    change primeEndomorphismTraceAt A₂ (Over.mk (𝟙 _)) 2
      (rationalBaseChangeHom c (rationalBaseChangeHom b (rationalBaseChangeHom s a))) =
      primeEndomorphismTraceAt A (Over.mk (𝟙 _)) 2 a
    rw [primeEndomorphismTraceAt_baseChange, primeEndomorphismTraceAt_baseChange,
      primeEndomorphismTraceAt_baseChange]
    have hunit : IsUnit (2 : Γ(Spec (.of k), ⊤)) := by
      simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr (by norm_num : (2 : k) ≠ 0)).map
        (Scheme.ΓSpecIso (.of k)).inv.hom
    exact primeEndomorphismTraceAt_geometric A ((((𝟙 _) ≫ c) ≫ b) ≫ s) (𝟙 _) 2 hunit a
  let a₂ : End0 A₂ := homToHom0 f₂
  have htrace : GeometricTraceCompatibleLinearMap A A₂ F :=
    geometricTraceCompatibleLinearMap_of_target_ne_zero A A₂ F hprime
      (a₂ * @involution _ A₂ P W₂ hadd₂ lam₂ hinv₂ a₂) (ne_of_gt hp)
  have hform (a d : End0 A) :
      @traceForm P C _ A₂ W₂ hadd₂ lam₂ hinv₂ (F a) (F d) =
        @traceForm P k _ A W hadd lam hinv a d := by
    change @traceForm P C _ A₂ W₂ hadd₂ lam₂ hinv₂
      (rationalBaseChangeHom c (rationalBaseChangeHom b (rationalBaseChangeHom s a)))
      (rationalBaseChangeHom c (rationalBaseChangeHom b (rationalBaseChangeHom s d))) = _
    rw [traceForm_apply, traceForm_apply,
      involution_baseChange P c W₁ W₂ hadd₁ hadd₂,
      involution_baseChange P b W₀ W₁ hadd₀ hadd₁,
      involution_baseChange P s W W₀ hadd hadd₀]
    change geometricEndomorphismTrace A₂
      ((rationalBaseChangeEnd c A₁) ((rationalBaseChangeEnd b A₀)
        ((rationalBaseChangeEnd s A) a)) *
       (rationalBaseChangeEnd c A₁) ((rationalBaseChangeEnd b A₀)
        ((rationalBaseChangeEnd s A) (@involution _ A P W hadd lam hinv d)))) = _
    rw [← map_mul, ← map_mul, ← map_mul]
    exact htrace _
  rw [← hform (homToHom0 f) (homToHom0 f)]
  change 0 < @traceForm P C _ A₂ W₂ hadd₂ lam₂ hinv₂
    (rationalBaseChangeHom c (rationalBaseChangeHom b (rationalBaseChangeHom s (homToHom0 f))))
    (rationalBaseChangeHom c (rationalBaseChangeHom b (rationalBaseChangeHom s (homToHom0 f))))
  simpa only [homToHom0_apply, rationalBaseChangeHom_tmul] using hp

end Transport

/-- Integral positivity for every actual geometric polarization, with precisely
the original Rosati witnesses and rational-inverse instance. -/
def GeometricPolarizationIntegralPositiveStatement : Prop :=
  ∀ (P : Prerequisites.{u})
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (A : AbelianScheme (Spec (.of k)))
    (W : DualData A) (hadd : W.Additivity P) (lam : A ⟶ W.dual P)
    [hinv : HasRationalInverse P W lam],
    W.IsPolarization P lam → @IntegralDiagonalPositive k _ A P W hadd lam hinv

/-- An ample-presentation positivity theorem suffices for every actual geometric
polarization. No general rational trace-comparison premise is needed. -/
theorem geometricPolarizationIntegralPositive_of_amplePresentation
    (hample : AmplePresentationIntegralPositiveStatement.{u}) :
    GeometricPolarizationIntegralPositiveStatement.{u} := by
  intro P k _ _ _ A W hadd lam hinv hpol
  let s : Spec (.of k) ⟶ Spec (.of k) := 𝟙 _
  let A₀ := (baseChange s).obj A
  let W₀ : DualData A₀ := W.baseChange P s
  let hadd₀ : W₀.Additivity P := W₀.fieldAdditivity P
  let lam₀ : A₀ ⟶ W₀.dual P := DualData.baseChangeMap P s W W₀ lam
  let hinv₀ : HasRationalInverse P W₀ lam₀ := hasRationalInverse_baseChange P s W W₀ lam
  have h₀ : HasFieldAmpleMumfordPresentation P.preservation P.square P.universality k
      A₀ W₀.hasDual (groupHom lam₀).hom.hom := by
    rw [DualData.baseChangeMap_hom]
    exact hpol.2 k s
  obtain ⟨K, instK, i, h₁⟩ := h₀
  let : Field K := instK
  let : CharZero K := charZero_of_injective_ringHom i.injective
  let b : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom i)
  let A₁ := (baseChange b).obj A₀
  let W₁ : DualData A₁ := W₀.baseChange P b
  let hadd₁ : W₁.Additivity P := W₁.fieldAdditivity P
  let lam₁ : A₁ ⟶ W₁.dual P := DualData.baseChangeMap P b W₀ W₁ lam₀
  let hinv₁ : HasRationalInverse P W₁ lam₁ := @hasRationalInverse_baseChange P _ _ b A₀ W₀ W₁ lam₀ hinv₀
  have hamp₁ : HasAmpleMumfordPresentation P.preservation P.square A₁ W₁.hasDual
      (groupHom lam₁).hom.hom := by
    rw [DualData.baseChangeMap_hom]
    exact h₁
  let C := AlgebraicClosure K
  let c : Spec (.of C) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K C))
  let A₂ := (baseChange c).obj A₁
  let W₂ : DualData A₂ := W₁.baseChange P c
  let hadd₂ : W₂.Additivity P := W₂.fieldAdditivity P
  let lam₂ : A₂ ⟶ W₂.dual P := DualData.baseChangeMap P c W₁ W₂ lam₁
  let hinv₂ : HasRationalInverse P W₂ lam₂ := @hasRationalInverse_baseChange P _ _ c A₁ W₁ W₂ lam₁ hinv₁
  have hamp₂ : HasAmpleMumfordPresentation P.preservation P.square A₂ W₂.hasDual
      (groupHom lam₂).hom.hom :=
    W₁.hasAmpleMumfordPresentation_baseChange P c lam₁ hamp₁
  exact integralDiagonalPositive_of_threeStep_baseChange P s b c W W₀ W₁ W₂
    hadd hadd₀ hadd₁ hadd₂ lam (hinv := hinv) (hinv₀ := hinv₀) (hinv₁ := hinv₁)
    (hinv₂ := hinv₂) (hample P C A₂ W₂ hadd₂ lam₂ (hinv := hinv₂) hamp₂)

end Rosati
end Langlands.AbelianScheme
