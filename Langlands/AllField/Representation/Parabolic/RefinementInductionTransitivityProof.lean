import Langlands.Representation.Parabolic.RefinementInductionTransitivityProof
import Langlands.AllField.Representation.Parabolic.RefinementTransitivityStatement
/-! Natural normalized induction in stages on the actual refinement spaces. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000

namespace Langlands.AllField.Parabolic
open Langlands.Parabolic hiding NormalizedRefinementInductionTransitivityClause normalizedRefinementInductionTransitivity
open Langlands.AllField.Parabolic

open _root_.CategoryTheory
open Langlands.GeneralLinear
open Langlands.Geometric

universe uF uV

variable {F : Type uF} [Field F]
  (T : LocalFieldData F) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (refinedLevi F B S) V)

private abbrev Inner :=
  letI := T.topology
  letI := T.leviTopologicalGroup B
  Induction.SmoothFunctions (refinedParabolic F B S)
  (twist (T.refinedParabolicHalfModulus B S)
    (σ.comp (refinedLeviProjection F B S)))

private abbrev Iterated :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  Induction.SmoothFunctions (B.parabolic F)
  (twist (T.parabolicHalfModulus B)
    ((T.normalizedRefinedInduced B S σ).comp (B.leviProjection F)))

private abbrev Direct :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  Induction.SmoothFunctions (composedParabolic F B S)
  (T.composedInducingRepresentation B S σ)

private theorem direct_cov (f : Direct T B S σ)
    (q : composedParabolic F B S) (g : GeneralLinear n F) :
    f.val.val (q.val * g) =
      (T.composedLeviHalfModulus B S (composedLeviProjection F B S q) : ℂ) •
        σ (composedLeviProjection F B S q) (f.val.val g) :=
  f.val.property q g

private theorem iterated_cov (f : Iterated T B S σ)
    (q : B.parabolic F) (g : GeneralLinear n F)
    (m : B.Levi F) :
    (f.val.val (q.val * g)).val.val m =
      (T.leviHalfModulus B (B.leviProjection F q) : ℂ) •
        (f.val.val g).val.val (m * B.leviProjection F q) := by
  exact congrArg (fun h : Inner T B S σ => h.val.val m) (f.val.property q g)

private theorem composed_half (q : composedParabolic F B S) :
    T.composedLeviHalfModulus B S (composedLeviProjection F B S q) =
      T.leviHalfModulus B
        (preimageProjection F B (refinedParabolic F B S) q).val *
      T.refinedLeviHalfModulus B S (composedLeviProjection F B S q) := by
  rw [T.composedLeviHalfModulus_eq]
  change T.refinedOuterHalfModulus B S
      (refinedLeviProjection F B S
        (preimageProjection F B (refinedParabolic F B S) q)) * _ = _
  rw [T.refinedOuterHalfModulus_projection]

private def forward (f : Iterated T B S σ) : Direct T B S σ := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  letI := T.leviTopologicalGroup B
  let K := Classical.choose f.property
  have hK := Classical.choose_spec f.property
  refine Induction.smoothFunctionOf _ _ (fun g => (f.val.val g).val.val 1) ?_ K ?_
  · intro q g
    change (f.val.val (q.val * g)).val.val 1 =
      (T.composedLeviHalfModulus B S (composedLeviProjection F B S q) : ℂ) •
        σ (composedLeviProjection F B S q) ((f.val.val g).val.val 1)
    have hf := iterated_cov T B S σ f
      (preimageInParabolic F B (refinedParabolic F B S) q) g 1
    change (f.val.val (q.val * g)).val.val 1 = _ at hf
    rw [hf]
    rw [one_mul]
    have h := (f.val.val g).val.property
      (preimageProjection F B (refinedParabolic F B S) q) 1
    change (f.val.val g).val.val (_ * 1) =
      (T.refinedLeviHalfModulus B S (composedLeviProjection F B S q) : ℂ) •
        σ (composedLeviProjection F B S q) ((f.val.val g).val.val 1) at h
    rw [mul_one] at h
    change (T.leviHalfModulus B
      (preimageProjection F B (refinedParabolic F B S) q).val : ℂ) •
      (f.val.val g).val.val
        (preimageProjection F B (refinedParabolic F B S) q).val = _
    rw [composed_half T B S q, Units.val_mul, mul_smul]
    exact congrArg (fun v : V => (T.leviHalfModulus B
      (preimageProjection F B (refinedParabolic F B S) q).val : ℂ) • v) h
  · intro k g
    exact congrArg (fun h : Induction.EquivariantFunctions _ _ =>
      (h.val g).val.val 1) (hK k)

private theorem direct_section (f : Direct T B S σ)
    (q : refinedParabolic F B S) (g : GeneralLinear n F) :
    f.val.val (B.leviEmbedding F q.val * g) =
      ((T.leviHalfModulus B q.val : ℂ) *
        (T.refinedLeviHalfModulus B S (refinedLeviProjection F B S q) : ℂ)) •
      σ (refinedLeviProjection F B S q) (f.val.val g) := by
  have h := direct_cov T B S σ f
    (preimageSection F B (refinedParabolic F B S) q) g
  have hp : composedLeviProjection F B S
      (preimageSection F B (refinedParabolic F B S) q) =
      refinedLeviProjection F B S q :=
    congrArg (refinedLeviProjection F B S)
      (preimageProjection_section F B (refinedParabolic F B S) q)
  rw [composed_half T B S, hp,
    preimageProjection_section F B (refinedParabolic F B S) q] at h
  exact h

/-- Direct induction is invariant under the outer radical, so removing the
outer unipotent part preserves evaluation. -/
private theorem direct_outer (f : Direct T B S σ)
    (q : B.parabolic F) (g : GeneralLinear n F) :
    f.val.val (q.val * g) =
      f.val.val (B.leviEmbedding F (B.leviProjection F q) * g) := by
  let u := B.unipotentPart F q
  have h := direct_cov T B S σ f
    (radicalInPreimage F B (refinedParabolic F B S) u)
    (B.leviEmbedding F (B.leviProjection F q) * g)
  have hproj : composedLeviProjection F B S
      (radicalInPreimage F B (refinedParabolic F B S) u) = 1 := by
    exact (congrArg (refinedLeviProjection F B S)
      (preimageProjection_radical F B (refinedParabolic F B S) u)).trans
      (map_one _)
  rw [hproj, map_one, Units.val_one, map_one, Module.End.one_apply, one_smul] at h
  change f.val.val
    ((q.val * (B.leviEmbedding F (B.leviProjection F q))⁻¹) *
      (B.leviEmbedding F (B.leviProjection F q) * g)) = _ at h
  simpa only [mul_assoc, inv_mul_cancel_left] using h

private def inverseValue (f : Direct T B S σ) (g : GeneralLinear n F)
    (m : B.Levi F) : V :=
  (T.leviHalfModulus B m : ℂ)⁻¹ • f.val.val (B.leviEmbedding F m * g)

private theorem inverseValue_cov (f : Direct T B S σ) (g : GeneralLinear n F)
    (q : refinedParabolic F B S) (m : B.Levi F) :
    inverseValue T B S σ f g (q.val * m) =
      (T.refinedLeviHalfModulus B S (refinedLeviProjection F B S q) : ℂ) •
        σ (refinedLeviProjection F B S q) (inverseValue T B S σ f g m) := by
  unfold inverseValue
  rw [(B.leviEmbedding F).map_mul, mul_assoc, direct_section T B S σ f q]
  rw [map_mul, Units.val_mul, map_smul, smul_smul, smul_smul]
  congr 1
  have hq := Units.ne_zero (T.leviHalfModulus B q.val)
  have hm := Units.ne_zero (T.leviHalfModulus B m)
  field_simp

/-- A direct stabilizer pulls back through conjugation and the Levi embedding;
intersecting the character kernel also fixes the inverse-half scalar. -/
private theorem inverseValue_smooth (f : Direct T B S σ) (g : GeneralLinear n F) :
    letI := T.topology
    ∃ K : OpenSubgroup (B.Levi F), ∀ (k : K) (m : B.Levi F),
      inverseValue T B S σ f g (m * k.val) = inverseValue T B S σ f g m := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  obtain ⟨K, hK⟩ := f.property
  let c : B.Levi F →* GeneralLinear n F := {
    toFun := fun m => g⁻¹ * B.leviEmbedding F m * g
    map_one' := by simp
    map_mul' := by intro a b; simp [map_mul, mul_assoc] }
  have hc : Continuous c :=
    (continuous_const.mul (B.leviEmbeddingContinuous F).continuous).mul_const g
  let H : OpenSubgroup (B.Levi F) :=
    ⟨(T.leviHalfModulus B).ker, T.isOpen_ker_leviHalfModulus B⟩
  refine ⟨K.comap c hc ⊓ H, ?_⟩
  intro k m
  have hk : c k.val ∈ K := k.property.1
  have hχ : T.leviHalfModulus B k.val = 1 := k.property.2
  have hf := congrArg (fun h : Induction.EquivariantFunctions _ _ =>
    h.val (B.leviEmbedding F m * g)) (hK ⟨c k.val, hk⟩)
  change f.val.val ((B.leviEmbedding F m * g) *
    (g⁻¹ * B.leviEmbedding F k.val * g)) = _ at hf
  simp only [mul_assoc, mul_inv_cancel_left] at hf
  simp only [inverseValue, map_mul, hχ, mul_one]
  rw [mul_assoc, hf]

private def inverseInner (f : Direct T B S σ) (g : GeneralLinear n F) :
    Inner T B S σ := by
  letI := T.topology
  letI := T.leviTopologicalGroup B
  let K := Classical.choose (inverseValue_smooth T B S σ f g)
  exact Induction.smoothFunctionOf _ _ (inverseValue T B S σ f g)
    (inverseValue_cov T B S σ f g) K
    (Classical.choose_spec (inverseValue_smooth T B S σ f g))

private theorem inverseValue_outer (f : Direct T B S σ)
    (q : B.parabolic F) (g : GeneralLinear n F) (m : B.Levi F) :
    inverseValue T B S σ f (q.val * g) m =
      (T.leviHalfModulus B (B.leviProjection F q) : ℂ) •
        inverseValue T B S σ f g (m * B.leviProjection F q) := by
  have h := direct_outer T B S σ f (B.leviInParabolic F m * q) g
  have hp : B.leviProjection F (B.leviInParabolic F m * q) =
      m * B.leviProjection F q := by
    rw [map_mul, B.leviProjection_section]
  rw [hp] at h
  change f.val.val ((B.leviEmbedding F m * q.val) * g) = _ at h
  rw [mul_assoc] at h
  unfold inverseValue
  rw [h, (T.leviHalfModulus B).map_mul, Units.val_mul, smul_smul]
  congr 1
  have hm := Units.ne_zero (T.leviHalfModulus B m)
  have hq := Units.ne_zero (T.leviHalfModulus B (B.leviProjection F q))
  field_simp

private def inverse (f : Direct T B S σ) : Iterated T B S σ := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  letI := T.leviTopologicalGroup B
  let K := Classical.choose f.property
  have hK := Classical.choose_spec f.property
  refine Induction.smoothFunctionOf _ _ (inverseInner T B S σ f) ?_ K ?_
  · intro q g
    apply Subtype.ext
    apply Subtype.ext
    funext m
    exact inverseValue_outer T B S σ f q g m
  · intro k g
    apply Subtype.ext
    apply Subtype.ext
    funext m
    change inverseValue T B S σ f (g * k.val) m = inverseValue T B S σ f g m
    have hf := congrArg (fun h : Induction.EquivariantFunctions _ _ =>
      h.val (B.leviEmbedding F m * g)) (hK k)
    change f.val.val ((B.leviEmbedding F m * g) * k.val) = _ at hf
    unfold inverseValue
    rw [← mul_assoc, hf]

private theorem forward_eval (f : Iterated T B S σ) (g : GeneralLinear n F) :
    (forward T B S σ f).val.val g = (f.val.val g).val.val 1 := rfl

private theorem inverse_eval (f : Direct T B S σ) (g : GeneralLinear n F)
    (m : B.Levi F) :
    ((inverse T B S σ f).val.val g).val.val m =
      (T.leviHalfModulus B m : ℂ)⁻¹ • f.val.val (B.leviEmbedding F m * g) := rfl

private theorem forward_inverse (f : Direct T B S σ) :
    forward T B S σ (inverse T B S σ f) = f := by
  apply Subtype.ext
  apply Subtype.ext
  funext g
  rw [forward_eval, inverse_eval]
  simp only [map_one, Units.val_one, inv_one, one_mul, one_smul]

private theorem inverse_forward (f : Iterated T B S σ) :
    inverse T B S σ (forward T B S σ f) = f := by
  apply Subtype.ext
  apply Subtype.ext
  funext g
  apply Subtype.ext
  apply Subtype.ext
  funext m
  rw [inverse_eval, forward_eval]
  have h := iterated_cov T B S σ f (B.leviInParabolic F m) g 1
  rw [B.leviProjection_section, one_mul] at h
  change (f.val.val (B.leviEmbedding F m * g)).val.val 1 = _ at h
  rw [h, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]

private def transitivityEquiv :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedParabolicInduced B (T.normalizedRefinedInduced B S σ)).Equiv
      (T.normalizedComposedInduced B S σ) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  letI := T.leviTopologicalGroup B
  exact {
    toLinearEquiv := {
      toFun := forward T B S σ
      invFun := inverse T B S σ
      left_inv := inverse_forward T B S σ
      right_inv := forward_inverse T B S σ
      map_add' := by intro f h; ext g; rfl
      map_smul' := by intro c f; ext g; rfl }
    isIntertwining' := by intro g; ext f x; rfl }

private def transitivityIso :
    letI := T.topology
    (T.normalizedRefinedInductionFunctor.{uF, uV} B S ⋙
      T.normalizedParabolicInductionFunctor B) ≅
      T.normalizedComposedInductionFunctor.{uF, uV} B S := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  letI := T.leviTopologicalGroup B
  refine NatIso.ofComponents
    (fun A => SmoothRep.mkIso (transitivityEquiv T B S A.representation)) ?_
  intro A A' f
  ext φ
  rfl

/-- Evaluation at the inner identity gives natural normalized induction in stages
for the actual composed parabolic of every block refinement. -/
theorem normalizedRefinementInductionTransitivity
    (F : Type uF) [Field F] (T : LocalFieldData F)
    {n : ℕ} (B : BlockShape n) (S : BlockRefinement B) :
    NormalizedRefinementInductionTransitivityClause.{uF, uV} F T B S := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  let := T.leviTopologicalGroup B
  refine ⟨transitivityIso T B S, ?_, ?_⟩
  · intro A f g
    rfl
  · intro A f g m
    rfl

end Langlands.AllField.Parabolic
