import Langlands.Representation.Induction.Parabolic
import Langlands.Representation.Jacquet.Parabolic

/-! Evaluation at the identity turns a nonzero intertwiner into a normalized
parabolic induction into a nonzero intertwiner out of the normalized Jacquet
module. -/

noncomputable section

open scoped NNReal

namespace Langlands.CuspidalSupport

open GeneralLinear

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}
  (B : BlockShape n) {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {X : Representation ℂ (GeneralLinear n F.Carrier) V}
  {σ : Representation ℂ (B.Levi F.Carrier) W}

/-- The vector `f v (1)`, as a linear function of `v`. -/
def inducedEvaluation
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      X.IntertwiningMap (T.normalizedParabolicInduced B σ)) : V →ₗ[ℂ] W :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  { toFun := fun v => Induction.eval (B.parabolic F.Carrier)
      (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier))) (f v) 1
    map_add' := fun v w => by
      change (f (v + w)).1.1 1 = _
      rw [map_add]
      rfl
    map_smul' := fun c v => by
      change (f (c • v)).1.1 1 = _
      rw [map_smul]
      rfl }

/-- Equivariance: evaluating the image of a translate at `1` is evaluating the
image at the translating element. -/
theorem inducedEvaluation_translate
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      X.IntertwiningMap (T.normalizedParabolicInduced B σ))
    (g : GeneralLinear n F.Carrier) (v : V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    inducedEvaluation T B f (X g v) =
      Induction.eval (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier))) (f v) g := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  have h := Representation.IntertwiningMap.isIntertwining _ _ f g v
  have hh := congrArg (fun φ => Induction.eval (B.parabolic F.Carrier)
    (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier))) φ 1) h
  change (f (X g v)).1.1 1 = (f v).1.1 (1 * g) at hh
  change (f (X g v)).1.1 1 = (f v).1.1 g
  simpa only [one_mul] using hh

/-- Covariance: an element of the parabolic acts through its Levi part, twisted
by the half modulus. -/
theorem inducedEvaluation_parabolic
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      X.IntertwiningMap (T.normalizedParabolicInduced B σ))
    (q : B.parabolic F.Carrier) (v : V) :
    inducedEvaluation T B f (X q v) =
      ((NNReal.sqrt (T.leviModulus B (B.leviProjection F.Carrier q) : ℝ≥0) : ℝ) : ℂ) •
        σ (B.leviProjection F.Carrier q) (inducedEvaluation T B f v) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  rw [inducedEvaluation_translate]
  have h := T.normalizedParabolicInduced_covariant B σ (f v) q 1
  rw [mul_one] at h
  exact h

/-- The unipotent radical acts trivially after evaluation. -/
theorem inducedEvaluation_unipotent
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      X.IntertwiningMap (T.normalizedParabolicInduced B σ))
    (u : B.unipotentRadical F.Carrier) (v : V) :
    inducedEvaluation T B f (X (u : B.parabolic F.Carrier) v) = inducedEvaluation T B f v := by
  rw [inducedEvaluation_parabolic]
  have hu : B.leviProjection F.Carrier u = 1 := u.property
  rw [hu, map_one, Units.val_one, NNReal.sqrt_one, NNReal.coe_one, Complex.ofReal_one,
    one_smul, map_one, Module.End.one_apply]

/-- A block-diagonal Levi element acts by `δ_P(m)^(1/2) σ(m)` after evaluation. -/
theorem inducedEvaluation_levi
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      X.IntertwiningMap (T.normalizedParabolicInduced B σ))
    (m : B.Levi F.Carrier) (v : V) :
    inducedEvaluation T B f (X (B.leviEmbedding F.Carrier m) v) =
      (T.leviHalfModulus B m : ℂ) • σ m (inducedEvaluation T B f v) := by
  have h := inducedEvaluation_parabolic T B f (B.leviInParabolic F.Carrier m) v
  rw [BlockShape.leviInParabolic_val, BlockShape.leviProjection_section] at h
  rw [h, T.leviHalfModulus_apply]

/-- Evaluation at the identity, descended to the normalized Jacquet module. -/
def jacquetEvaluation
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      X.IntertwiningMap (T.normalizedParabolicInduced B σ)) :
    (T.normalizedJacquet B X).IntertwiningMap σ where
  toLinearMap := Jacquet.lift (X.comp (B.parabolic F.Carrier).subtype)
    (B.unipotentRadical F.Carrier) (inducedEvaluation T B f)
    (fun u => LinearMap.ext fun v => inducedEvaluation_unipotent T B f u v)
  isIntertwining' m := by
    apply Representation.Coinvariants.hom_ext
    refine LinearMap.ext fun v => ?_
    change Jacquet.lift (X.comp (B.parabolic F.Carrier).subtype) (B.unipotentRadical F.Carrier)
        (inducedEvaluation T B f)
        (fun u => LinearMap.ext fun w => inducedEvaluation_unipotent T B f u w)
        (T.normalizedJacquet B X m (B.jacquetMk X v)) =
      σ m (inducedEvaluation T B f v)
    rw [T.normalizedJacquet_mk_eq_inv_halfModulus B X m v, Units.smul_def, map_smul]
    change ((T.leviHalfModulus B m)⁻¹ : ℂˣ).val •
        inducedEvaluation T B f (X (B.leviEmbedding F.Carrier m) v) = _
    rw [inducedEvaluation_levi, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_smul]

@[simp]
theorem jacquetEvaluation_mk
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      X.IntertwiningMap (T.normalizedParabolicInduced B σ)) (v : V) :
    jacquetEvaluation T B f (B.jacquetMk X v) = inducedEvaluation T B f v := rfl

/-- The descended evaluation of a nonzero intertwiner is nonzero. -/
theorem jacquetEvaluation_ne_zero
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      X.IntertwiningMap (T.normalizedParabolicInduced B σ)) (hf : f ≠ 0) :
    jacquetEvaluation T B f ≠ 0 := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro h
  apply hf
  apply Representation.IntertwiningMap.ext
  refine LinearMap.ext fun v => ?_
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have hx := congrArg (fun g : (T.normalizedJacquet B X).IntertwiningMap σ =>
    g (B.jacquetMk X (X x v))) h
  simp only [jacquetEvaluation_mk, inducedEvaluation_translate] at hx
  exact hx

/-- A nonzero intertwiner into a normalized parabolic induction gives a nonzero
intertwiner from the normalized Jacquet module to the inducing representation. -/
theorem exists_ne_zero_normalizedJacquet_hom
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      X.IntertwiningMap (T.normalizedParabolicInduced B σ)) (hf : f ≠ 0) :
    ∃ g : (T.normalizedJacquet B X).IntertwiningMap σ, g ≠ 0 :=
  ⟨jacquetEvaluation T B f, jacquetEvaluation_ne_zero T B f hf⟩

end Langlands.CuspidalSupport
