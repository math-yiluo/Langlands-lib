import Langlands.Representation.CuspidalSupport.InducedJacquetEvaluation
import Langlands.Representation.Geometric.RefinementFunctors

/-!
# Natural normalized first adjointness

For a smooth representation `X` of `GL_n` and any representation `σ` of a
standard block Levi, evaluation at the identity identifies intertwiners
`X → i_P σ` with intertwiners `r_P X → σ`. The same holds for a standard
parabolic of a product Levi. Both identifications are natural in `X` and `σ`.
-/

noncomputable section

open scoped NNReal

namespace Langlands.Parabolic.FirstAdjointness

open GeneralLinear Geometric

universe uF uV uW uX

section Standard

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}
  (B : BlockShape n) {V : Type uV} {W : Type uW} {X : Type uX}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X]

/-- A parabolic element acts on Jacquet classes through its Levi part. -/
theorem jacquetMk_parabolic (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (q : B.parabolic F.Carrier) (v : V) :
    B.jacquetMk ρ (ρ q v) =
      B.jacquetMk ρ (ρ (B.leviEmbedding F.Carrier (B.leviProjection F.Carrier q)) v) := by
  have h := Jacquet.mk_apply_subgroup (ρ.comp (B.parabolic F.Carrier).subtype)
    (B.unipotentRadical F.Carrier) (B.unipotentPart F.Carrier q)
    (ρ (B.leviEmbedding F.Carrier (B.leviProjection F.Carrier q)) v)
  rw [← h]
  congr 1
  change ρ q v = ρ ((q * (B.leviInParabolic F.Carrier (B.leviProjection F.Carrier q))⁻¹ :
    B.parabolic F.Carrier) : GeneralLinear n F.Carrier)
      (ρ (B.leviInParabolic F.Carrier (B.leviProjection F.Carrier q) :
        GeneralLinear n F.Carrier) v)
  rw [← Module.End.mul_apply, ← map_mul, ← Subgroup.coe_mul, inv_mul_cancel_right]

/-- Undo the inverse half-modulus of the normalized Jacquet action. -/
theorem jacquetMk_levi (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (m : B.Levi F.Carrier) (v : V) :
    B.jacquetMk ρ (ρ (B.leviEmbedding F.Carrier m) v) =
      (T.leviHalfModulus B m : ℂ) • T.normalizedJacquet B ρ m (B.jacquetMk ρ v) := by
  rw [T.normalizedJacquet_mk_eq_inv_halfModulus, Units.smul_def, smul_smul,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

variable {ρ : Representation ℂ (GeneralLinear n F.Carrier) V}
  {σ : Representation ℂ (B.Levi F.Carrier) W}

/-- A Levi intertwiner from the normalized Jacquet module, composed with the
quotient map, is covariant for the parabolic with the positive half modulus. -/
theorem jacquet_covariant (A : (T.normalizedJacquet B ρ).IntertwiningMap σ)
    (q : B.parabolic F.Carrier) (v : V) :
    A (B.jacquetMk ρ (ρ q v)) =
      (T.parabolicHalfModulus B q : ℂ) •
        σ (B.leviProjection F.Carrier q) (A (B.jacquetMk ρ v)) := by
  rw [jacquetMk_parabolic, jacquetMk_levi T, map_smul,
    Representation.IntertwiningMap.isIntertwining]
  rfl

/-- The covariant orbit functions of a Jacquet intertwiner, before restricting
to smooth vectors. -/
def orbitMap (A : (T.normalizedJacquet B ρ).IntertwiningMap σ) :
    ρ.IntertwiningMap (Induction.equivariantAction (B.parabolic F.Carrier)
      (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier)))) where
  toLinearMap :=
    { toFun := fun v => ⟨fun g => A (B.jacquetMk ρ (ρ g v)), by
        intro q g
        change A (B.jacquetMk ρ (ρ ((q : GeneralLinear n F.Carrier) * g) v)) =
          (T.parabolicHalfModulus B q : ℂ) •
            σ (B.leviProjection F.Carrier q) (A (B.jacquetMk ρ (ρ g v)))
        rw [map_mul, Module.End.mul_apply]
        exact jacquet_covariant T B A q (ρ g v)⟩
      map_add' := by intros; ext g; simp
      map_smul' := by intros; ext g; simp }
  isIntertwining' g := by
    ext v x
    change A (B.jacquetMk ρ (ρ x (ρ g v))) = A (B.jacquetMk ρ (ρ (x * g) v))
    rw [map_mul, Module.End.mul_apply]

/-- The Frobenius intertwiner into normalized induction. -/
def frobenius (hρ : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      IsSmooth ρ)
    (A : (T.normalizedJacquet B ρ).IntertwiningMap σ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ρ.IntertwiningMap (T.normalizedParabolicInduced B σ) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  smoothLift hρ (orbitMap T B A)

@[simp]
theorem frobenius_eval (hρ : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      IsSmooth ρ)
    (A : (T.normalizedJacquet B ρ).IntertwiningMap σ) (v : V) (g : GeneralLinear n F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier)))
        (frobenius T B hρ A v) g =
      A (B.jacquetMk ρ (ρ g v)) := rfl

/-- Standard normalized first adjointness for a smooth source. -/
def equiv (hρ : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      IsSmooth ρ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (ρ.IntertwiningMap (T.normalizedParabolicInduced B σ)) ≃ₗ[ℂ]
      ((T.normalizedJacquet B ρ).IntertwiningMap σ) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  { toFun := CuspidalSupport.jacquetEvaluation T B
    invFun := frobenius T B hρ
    left_inv f := by
      ext v g
      change CuspidalSupport.inducedEvaluation T B f (ρ g v) = _
      exact CuspidalSupport.inducedEvaluation_translate T B f g v
    right_inv A := by
      apply Representation.IntertwiningMap.ext
      apply Representation.Coinvariants.hom_ext
      ext v
      change A (B.jacquetMk ρ (ρ 1 v)) = A (B.jacquetMk ρ v)
      rw [map_one, Module.End.one_apply]
    map_add' f g := by
      apply Representation.IntertwiningMap.ext
      apply Representation.Coinvariants.hom_ext
      ext v
      rfl
    map_smul' c f := by
      apply Representation.IntertwiningMap.ext
      apply Representation.Coinvariants.hom_ext
      ext v
      rfl }

theorem equiv_apply_mk (hρ : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      IsSmooth ρ)
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      ρ.IntertwiningMap (T.normalizedParabolicInduced B σ)) (v : V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    equiv T B hρ f (B.jacquetMk ρ v) =
      Induction.eval (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier))) (f v) 1 :=
  rfl

/-- Naturality in the inducing representation. -/
theorem equiv_inducedMap (hρ : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      IsSmooth ρ)
    {τ : Representation ℂ (B.Levi F.Carrier) X} (c : σ.IntertwiningMap τ)
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      ρ.IntertwiningMap (T.normalizedParabolicInduced B σ)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    equiv T B hρ ((T.normalizedParabolicInducedMap B c).comp f) =
      c.comp (equiv T B hρ f) := by
  apply Representation.IntertwiningMap.ext
  apply Representation.Coinvariants.hom_ext
  ext v
  rfl

/-- Naturality in the smooth source. -/
theorem equiv_comp {ρ' : Representation ℂ (GeneralLinear n F.Carrier) X}
    (hρ : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      IsSmooth ρ)
    (hρ' : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      IsSmooth ρ')
    (h : ρ'.IntertwiningMap ρ)
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      ρ.IntertwiningMap (T.normalizedParabolicInduced B σ)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    equiv T B hρ' (f.comp h) = (equiv T B hρ f).comp (T.normalizedJacquetMap B h) := by
  apply Representation.IntertwiningMap.ext
  apply Representation.Coinvariants.hom_ext
  ext v
  rfl

end Standard

section Refined

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}
  (B : BlockShape n) (S : BlockRefinement B) {V : Type uV} {W : Type uW} {X : Type uX}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X]

/-- A refined parabolic element acts on refined Jacquet classes through its
refined Levi part. -/
theorem refinedJacquetMk_parabolic (ρ : Representation ℂ (B.Levi F.Carrier) V)
    (q : refinedParabolic F.Carrier B S) (v : V) :
    refinedJacquetMk B S ρ (ρ q.val v) =
      refinedJacquetMk B S ρ (ρ (refinedLeviProjection F.Carrier B S q).val v) := by
  have hu := (mem_refinedUnipotentRadical F.Carrier B S _).mp
    (refinedUnipotentPart F.Carrier B S q).property
  have h := Jacquet.mk_apply_subgroup ρ (refinedUnipotent F.Carrier B S)
    ⟨_, hu⟩ (ρ (refinedLeviProjection F.Carrier B S q).val v)
  rw [← h]
  congr 1
  change ρ q.val v = ρ (q * (refinedLeviSection F.Carrier B S
      (refinedLeviProjection F.Carrier B S q))⁻¹).val
    (ρ (refinedLeviSection F.Carrier B S (refinedLeviProjection F.Carrier B S q)).val v)
  rw [← Module.End.mul_apply, ← map_mul, ← Subgroup.coe_mul, inv_mul_cancel_right]

/-- Undo the inverse half-modulus of the normalized refined Jacquet action. -/
theorem refinedJacquetMk_levi (ρ : Representation ℂ (B.Levi F.Carrier) V)
    (m : refinedLevi F.Carrier B S) (v : V) :
    refinedJacquetMk B S ρ (ρ m.val v) =
      (T.refinedLeviHalfModulus B S m : ℂ) •
        T.normalizedRefinedJacquet B S ρ m (refinedJacquetMk B S ρ v) := by
  rw [T.normalizedRefinedJacquet_mk, T.refinedLeviInverseHalfModulus_eq_inv,
    MonoidHom.inv_apply, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

variable {ρ : Representation ℂ (B.Levi F.Carrier) V}
  {σ : Representation ℂ (refinedLevi F.Carrier B S) W}

/-- A refined Levi intertwiner from the normalized refined Jacquet module,
composed with the quotient map, is covariant for the refined parabolic with the
positive half modulus. -/
theorem refinedJacquet_covariant (A : (T.normalizedRefinedJacquet B S ρ).IntertwiningMap σ)
    (q : refinedParabolic F.Carrier B S) (v : V) :
    A (refinedJacquetMk B S ρ (ρ q.val v)) =
      (T.refinedParabolicHalfModulus B S q : ℂ) •
        σ (refinedLeviProjection F.Carrier B S q) (A (refinedJacquetMk B S ρ v)) := by
  rw [refinedJacquetMk_parabolic, refinedJacquetMk_levi T, map_smul,
    Representation.IntertwiningMap.isIntertwining]
  rfl

/-- The covariant orbit functions of a refined Jacquet intertwiner, before
restricting to smooth vectors. -/
def refinedOrbitMap (A : (T.normalizedRefinedJacquet B S ρ).IntertwiningMap σ) :
    ρ.IntertwiningMap (Induction.equivariantAction (refinedParabolic F.Carrier B S)
      (twist (T.refinedParabolicHalfModulus B S)
        (σ.comp (refinedLeviProjection F.Carrier B S)))) where
  toLinearMap :=
    { toFun := fun v => ⟨fun g => A (refinedJacquetMk B S ρ (ρ g v)), by
        intro q g
        change A (refinedJacquetMk B S ρ (ρ (q.val * g) v)) =
          (T.refinedParabolicHalfModulus B S q : ℂ) •
            σ (refinedLeviProjection F.Carrier B S q) (A (refinedJacquetMk B S ρ (ρ g v)))
        rw [map_mul, Module.End.mul_apply]
        exact refinedJacquet_covariant T B S A q (ρ g v)⟩
      map_add' := by intros; ext g; simp
      map_smul' := by intros; ext g; simp }
  isIntertwining' g := by
    ext v x
    change A (refinedJacquetMk B S ρ (ρ x (ρ g v))) = A (refinedJacquetMk B S ρ (ρ (x * g) v))
    rw [map_mul, Module.End.mul_apply]

/-- The refined Frobenius intertwiner into normalized refined induction. -/
def refinedFrobenius (hρ : letI := T.topology
      letI := T.leviTopologicalGroup B
      IsSmooth ρ)
    (A : (T.normalizedRefinedJacquet B S ρ).IntertwiningMap σ) :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    ρ.IntertwiningMap (T.normalizedRefinedInduced B S σ) :=
  letI := T.topology
  letI := T.leviTopologicalGroup B
  smoothLift hρ (refinedOrbitMap T B S A)

@[simp]
theorem refinedFrobenius_eval (hρ : letI := T.topology
      letI := T.leviTopologicalGroup B
      IsSmooth ρ)
    (A : (T.normalizedRefinedJacquet B S ρ).IntertwiningMap σ) (v : V) (g : B.Levi F.Carrier) :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    Induction.eval (refinedParabolic F.Carrier B S)
        (twist (T.refinedParabolicHalfModulus B S)
          (σ.comp (refinedLeviProjection F.Carrier B S)))
        (refinedFrobenius T B S hρ A v) g =
      A (refinedJacquetMk B S ρ (ρ g v)) := rfl

/-- The vector `f v (1)`, as a linear function of `v`. -/
def refinedInducedEvaluation
    (f : letI := T.topology
      letI := T.leviTopologicalGroup B
      ρ.IntertwiningMap (T.normalizedRefinedInduced B S σ)) : V →ₗ[ℂ] W :=
  letI := T.topology
  letI := T.leviTopologicalGroup B
  { toFun := fun v => Induction.eval (refinedParabolic F.Carrier B S)
      (twist (T.refinedParabolicHalfModulus B S)
        (σ.comp (refinedLeviProjection F.Carrier B S))) (f v) 1
    map_add' := fun v w => by
      change (f (v + w)).1.1 1 = _
      rw [map_add]
      rfl
    map_smul' := fun c v => by
      change (f (c • v)).1.1 1 = _
      rw [map_smul]
      rfl }

/-- Evaluating the image of a translate at `1` is evaluating the image at the
translating element. -/
theorem refinedInducedEvaluation_translate
    (f : letI := T.topology
      letI := T.leviTopologicalGroup B
      ρ.IntertwiningMap (T.normalizedRefinedInduced B S σ))
    (g : B.Levi F.Carrier) (v : V) :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    refinedInducedEvaluation T B S f (ρ g v) =
      Induction.eval (refinedParabolic F.Carrier B S)
        (twist (T.refinedParabolicHalfModulus B S)
          (σ.comp (refinedLeviProjection F.Carrier B S))) (f v) g := by
  let := T.topology
  let := T.leviTopologicalGroup B
  have h := Representation.IntertwiningMap.isIntertwining _ _ f g v
  have hh := congrArg (fun φ => Induction.eval (refinedParabolic F.Carrier B S)
    (twist (T.refinedParabolicHalfModulus B S)
      (σ.comp (refinedLeviProjection F.Carrier B S))) φ 1) h
  change (f (ρ g v)).1.1 1 = (f v).1.1 (1 * g) at hh
  change (f (ρ g v)).1.1 1 = (f v).1.1 g
  simpa only [one_mul] using hh

/-- A refined parabolic element acts through its refined Levi part, twisted by
the positive half modulus. -/
theorem refinedInducedEvaluation_parabolic
    (f : letI := T.topology
      letI := T.leviTopologicalGroup B
      ρ.IntertwiningMap (T.normalizedRefinedInduced B S σ))
    (q : refinedParabolic F.Carrier B S) (v : V) :
    refinedInducedEvaluation T B S f (ρ q.val v) =
      (T.refinedParabolicHalfModulus B S q : ℂ) •
        σ (refinedLeviProjection F.Carrier B S q) (refinedInducedEvaluation T B S f v) := by
  let := T.topology
  let := T.leviTopologicalGroup B
  rw [refinedInducedEvaluation_translate]
  have h := (f v).1.property q 1
  rw [mul_one] at h
  exact h

/-- The refined unipotent radical acts trivially after evaluation. -/
theorem refinedInducedEvaluation_unipotent
    (f : letI := T.topology
      letI := T.leviTopologicalGroup B
      ρ.IntertwiningMap (T.normalizedRefinedInduced B S σ))
    (u : refinedUnipotent F.Carrier B S) (v : V) :
    refinedInducedEvaluation T B S f (ρ u v) = refinedInducedEvaluation T B S f v := by
  let q : refinedParabolic F.Carrier B S :=
    ⟨u.val, refinedUnipotent_le_parabolic F.Carrier B S u.property⟩
  have hq : refinedLeviProjection F.Carrier B S q = 1 :=
    (mem_refinedUnipotentRadical F.Carrier B S q).mpr u.property
  have h := refinedInducedEvaluation_parabolic T B S f q v
  rw [T.refinedParabolicHalfModulus_apply, hq, map_one, Units.val_one, one_smul, map_one,
    Module.End.one_apply] at h
  exact h

/-- A refined Levi element acts by the positive half modulus times `σ` after
evaluation. -/
theorem refinedInducedEvaluation_levi
    (f : letI := T.topology
      letI := T.leviTopologicalGroup B
      ρ.IntertwiningMap (T.normalizedRefinedInduced B S σ))
    (m : refinedLevi F.Carrier B S) (v : V) :
    refinedInducedEvaluation T B S f (ρ m.val v) =
      (T.refinedLeviHalfModulus B S m : ℂ) • σ m (refinedInducedEvaluation T B S f v) := by
  have h := refinedInducedEvaluation_parabolic T B S f (refinedLeviSection F.Carrier B S m) v
  rw [refinedLeviSection_val, T.refinedParabolicHalfModulus_section,
    refinedLeviProjection_section] at h
  exact h

/-- Evaluation at the identity, descended to the normalized refined Jacquet
module. -/
def refinedJacquetEvaluation
    (f : letI := T.topology
      letI := T.leviTopologicalGroup B
      ρ.IntertwiningMap (T.normalizedRefinedInduced B S σ)) :
    (T.normalizedRefinedJacquet B S ρ).IntertwiningMap σ where
  toLinearMap := Jacquet.lift ρ (refinedUnipotent F.Carrier B S)
    (refinedInducedEvaluation T B S f)
    (fun u => LinearMap.ext fun v => refinedInducedEvaluation_unipotent T B S f u v)
  isIntertwining' m := by
    apply Representation.Coinvariants.hom_ext
    refine LinearMap.ext fun v => ?_
    change Jacquet.lift ρ (refinedUnipotent F.Carrier B S) (refinedInducedEvaluation T B S f)
        (fun u => LinearMap.ext fun w => refinedInducedEvaluation_unipotent T B S f u w)
        (T.normalizedRefinedJacquet B S ρ m (refinedJacquetMk B S ρ v)) =
      σ m (refinedInducedEvaluation T B S f v)
    rw [T.normalizedRefinedJacquet_mk, map_smul]
    change (T.refinedLeviInverseHalfModulus B S m : ℂ) •
        refinedInducedEvaluation T B S f (ρ m.val v) = _
    rw [refinedInducedEvaluation_levi, smul_smul, T.refinedLeviInverseHalfModulus_eq_inv,
      MonoidHom.inv_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

@[simp]
theorem refinedJacquetEvaluation_mk
    (f : letI := T.topology
      letI := T.leviTopologicalGroup B
      ρ.IntertwiningMap (T.normalizedRefinedInduced B S σ)) (v : V) :
    refinedJacquetEvaluation T B S f (refinedJacquetMk B S ρ v) =
      refinedInducedEvaluation T B S f v := rfl

/-- Refined normalized first adjointness for a smooth source. -/
def refinedEquiv (hρ : letI := T.topology
      letI := T.leviTopologicalGroup B
      IsSmooth ρ) :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    (ρ.IntertwiningMap (T.normalizedRefinedInduced B S σ)) ≃ₗ[ℂ]
      ((T.normalizedRefinedJacquet B S ρ).IntertwiningMap σ) :=
  letI := T.topology
  letI := T.leviTopologicalGroup B
  { toFun := refinedJacquetEvaluation T B S
    invFun := refinedFrobenius T B S hρ
    left_inv f := by
      ext v g
      change refinedInducedEvaluation T B S f (ρ g v) = _
      exact refinedInducedEvaluation_translate T B S f g v
    right_inv A := by
      apply Representation.IntertwiningMap.ext
      apply Representation.Coinvariants.hom_ext
      ext v
      change A (refinedJacquetMk B S ρ (ρ 1 v)) = A (refinedJacquetMk B S ρ v)
      rw [map_one, Module.End.one_apply]
    map_add' f g := by
      apply Representation.IntertwiningMap.ext
      apply Representation.Coinvariants.hom_ext
      ext v
      rfl
    map_smul' c f := by
      apply Representation.IntertwiningMap.ext
      apply Representation.Coinvariants.hom_ext
      ext v
      rfl }

theorem refinedEquiv_apply_mk (hρ : letI := T.topology
      letI := T.leviTopologicalGroup B
      IsSmooth ρ)
    (f : letI := T.topology
      letI := T.leviTopologicalGroup B
      ρ.IntertwiningMap (T.normalizedRefinedInduced B S σ)) (v : V) :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    refinedEquiv T B S hρ f (refinedJacquetMk B S ρ v) =
      Induction.eval (refinedParabolic F.Carrier B S)
        (twist (T.refinedParabolicHalfModulus B S)
          (σ.comp (refinedLeviProjection F.Carrier B S))) (f v) 1 :=
  rfl

/-- Naturality in the inducing representation. -/
theorem refinedEquiv_inducedMap (hρ : letI := T.topology
      letI := T.leviTopologicalGroup B
      IsSmooth ρ)
    {τ : Representation ℂ (refinedLevi F.Carrier B S) X} (c : σ.IntertwiningMap τ)
    (f : letI := T.topology
      letI := T.leviTopologicalGroup B
      ρ.IntertwiningMap (T.normalizedRefinedInduced B S σ)) :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    refinedEquiv T B S hρ ((T.normalizedRefinedInducedMap B S c).comp f) =
      c.comp (refinedEquiv T B S hρ f) := by
  apply Representation.IntertwiningMap.ext
  apply Representation.Coinvariants.hom_ext
  ext v
  rfl

/-- Naturality in the smooth source. -/
theorem refinedEquiv_comp {ρ' : Representation ℂ (B.Levi F.Carrier) X}
    (hρ : letI := T.topology
      letI := T.leviTopologicalGroup B
      IsSmooth ρ)
    (hρ' : letI := T.topology
      letI := T.leviTopologicalGroup B
      IsSmooth ρ')
    (h : ρ'.IntertwiningMap ρ)
    (f : letI := T.topology
      letI := T.leviTopologicalGroup B
      ρ.IntertwiningMap (T.normalizedRefinedInduced B S σ)) :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    refinedEquiv T B S hρ' (f.comp h) =
      (refinedEquiv T B S hρ f).comp (T.normalizedRefinedJacquetMap B S h) := by
  apply Representation.IntertwiningMap.ext
  apply Representation.Coinvariants.hom_ext
  ext v
  rfl

end Refined

end Langlands.Parabolic.FirstAdjointness
