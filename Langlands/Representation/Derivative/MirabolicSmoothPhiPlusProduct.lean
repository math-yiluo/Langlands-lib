import Langlands.Representation.Derivative.MirabolicSmoothPhiPlusAdjunction
import Langlands.Representation.Mirabolic.LeftMixedProductSuccessor

/-!
# Left mixed products and the smooth plus functor

Zelevinsky (1980), §5.3: for `ρ` on `GL_k` and `σ` on `P_(n+1)`, the left mixed
product `ρ × Φ̂⁺(σ)` embeds into `Φ̂⁺(ρ × σ)`. The embedding is
`(phiHatPlusAdjunction).symm B`, where `B : Φ⁻(ρ × Φ̂⁺(σ)) → ρ × σ` descends the
value map `b(f)(y) = |det y|^(-1/2) • (id ⊗ ev₁)(f(successor y))`.
-/

noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace Langlands.Derivative.Mirabolic

open GeneralLinear GeneralLinear.Mirabolic GeneralLinear.Mirabolic.MixedProduct HarmonicAnalysis

universe uV uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-! ## Evaluation at a point -/

section EvalAt

variable (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ)

/-- Evaluation at `x`, as a linear map `Φ̂⁺(σ) → σ`. -/
def phiHatPlusEvalAt :
    letI := T.topology
    (σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) → mirabolic (n + 1) F.Carrier →
      (phiHatPlus T ψ n).obj σ →ₗ[ℂ] σ := by
  letI := T.topology
  exact fun σ x =>
    { toFun := fun φ => phiHatPlusNormalizedEval T ψ n σ φ x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem phiHatPlusEvalAt_apply :
    letI := T.topology
    ∀ (σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) (x : mirabolic (n + 1) F.Carrier)
      (φ : (phiHatPlus T ψ n).obj σ),
      phiHatPlusEvalAt T ψ n σ x φ = phiHatPlusNormalizedEval T ψ n σ φ x := by
  intros
  rfl

theorem phiHatPlusEvalAt_action :
    letI := T.topology
    ∀ (σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) (x g : mirabolic (n + 1) F.Carrier)
      (φ : (phiHatPlus T ψ n).obj σ),
      phiHatPlusEvalAt T ψ n σ x (((phiHatPlus T ψ n).obj σ).representation g φ) =
        phiHatPlusEvalAt T ψ n σ (x * g) φ := by
  intros
  rfl

theorem phiHatPlusEvalAt_one_successor :
    letI := T.topology
    ∀ (σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) (g : mirabolic n F.Carrier)
      (φ : (phiHatPlus T ψ n).obj σ),
      phiHatPlusEvalAt T ψ n σ 1 (((phiHatPlus T ψ n).obj σ).representation (successor g) φ) =
        (phiPlusCharacter T n g : ℂ) • σ.representation g (phiHatPlusEvalAt T ψ n σ 1 φ) := by
  let := T.topology
  intro σ g φ
  rw [phiHatPlusEvalAt_action, one_mul, phiHatPlusEvalAt_apply, phiHatPlusEvalAt_apply]
  have h := phiHatPlusNormalizedEval_successor_mul T ψ n σ φ g 1
  rw [mul_one] at h
  exact h

theorem phiHatPlusEvalAt_one_radical :
    letI := T.topology
    ∀ (σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) (u : radical (n + 1) F.Carrier)
      (φ : (phiHatPlus T ψ n).obj σ),
      phiHatPlusEvalAt T ψ n σ 1
          (((phiHatPlus T ψ n).obj σ).representation (u : mirabolic (n + 1) F.Carrier) φ) =
        (theta ψ n u : ℂ) • phiHatPlusEvalAt T ψ n σ 1 φ := by
  let := T.topology
  intro σ u φ
  rw [phiHatPlusEvalAt_action, one_mul, phiHatPlusEvalAt_apply, phiHatPlusEvalAt_apply]
  have h := phiHatPlusNormalizedEval_radical_mul T ψ n σ φ u 1
  rw [mul_one] at h
  exact h

/-- `(id ⊗ ev₁) ∘ (L ⊗ Φ̂⁺σ(successor g)) = |det g|^(1/2) • (L ⊗ σ(g)) ∘ (id ⊗ ev₁)`. -/
theorem lTensor_evalAt_one_map_successor {V : Type*} [AddCommGroup V] [Module ℂ V] :
    letI := T.topology
    ∀ (σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) (L : V →ₗ[ℂ] V)
      (g : mirabolic n F.Carrier) (t : V ⊗[ℂ] (phiHatPlus T ψ n).obj σ),
      (phiHatPlusEvalAt T ψ n σ 1).lTensor V
          (TensorProduct.map L (((phiHatPlus T ψ n).obj σ).representation (successor g)) t) =
        (phiPlusCharacter T n g : ℂ) •
          TensorProduct.map L (σ.representation g) ((phiHatPlusEvalAt T ψ n σ 1).lTensor V t) := by
  let := T.topology
  intro σ L g t
  induction t with
  | tmul v φ =>
    rw [TensorProduct.map_tmul, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul,
      TensorProduct.map_tmul, phiHatPlusEvalAt_one_successor, TensorProduct.tmul_smul]
  | add t t' ht ht' => simp only [map_add, ht, ht', smul_add]

/-- `(id ⊗ ev₁) ∘ (1 ⊗ Φ̂⁺σ(u)) = θ(u) • (id ⊗ ev₁)` on radical elements. -/
theorem lTensor_evalAt_one_map_radical {V : Type*} [AddCommGroup V] [Module ℂ V] :
    letI := T.topology
    ∀ (σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) (u : radical (n + 1) F.Carrier)
      (t : V ⊗[ℂ] (phiHatPlus T ψ n).obj σ),
      (phiHatPlusEvalAt T ψ n σ 1).lTensor V
          (TensorProduct.map 1
            (((phiHatPlus T ψ n).obj σ).representation (u : mirabolic (n + 1) F.Carrier)) t) =
        (theta ψ n u : ℂ) • (phiHatPlusEvalAt T ψ n σ 1).lTensor V t := by
  let := T.topology
  intro σ u t
  induction t with
  | tmul v φ =>
    rw [TensorProduct.map_tmul, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul,
      phiHatPlusEvalAt_one_radical, Module.End.one_apply, TensorProduct.tmul_smul]
  | add t t' ht ht' => simp only [map_add, ht, ht', smul_add]

/-- `(id ⊗ ev₁) ∘ (1 ⊗ Φ̂⁺σ(z)) = id ⊗ ev_z`. -/
theorem lTensor_evalAt_one_map {V : Type*} [AddCommGroup V] [Module ℂ V] :
    letI := T.topology
    ∀ (σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) (z : mirabolic (n + 1) F.Carrier)
      (t : V ⊗[ℂ] (phiHatPlus T ψ n).obj σ),
      (phiHatPlusEvalAt T ψ n σ 1).lTensor V
          (TensorProduct.map 1 (((phiHatPlus T ψ n).obj σ).representation z) t) =
        (phiHatPlusEvalAt T ψ n σ z).lTensor V t := by
  let := T.topology
  intro σ z t
  induction t with
  | tmul v φ =>
    rw [TensorProduct.map_tmul, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul,
      phiHatPlusEvalAt_action, one_mul, Module.End.one_apply]
  | add t t' ht ht' => simp only [map_add, ht, ht']

end EvalAt

/-! ## The character identity -/

section Scalar

variable (T : F.TopologicalData) {k n : ℕ}

/-- `|det h|^(-1/2) · χ_L^(k,n+1)(a, successor p) · |det p|^(1/2) = χ_L^(k,n)(a, p)`. -/
theorem phiMinusCharacter_mul_leftLeviCharacter_successor (h : leftSubgroup k n F.Carrier) :
    (phiMinusCharacter T (k + n) (h : mirabolic (k + n) F.Carrier) : ℂ) *
        ((T.leftLeviCharacter k (n + 1)
            ((leftProjection h).1, successor (leftProjection h).2) : ℂ) *
          (phiPlusCharacter T n (leftProjection h).2 : ℂ)) =
      (T.leftLeviCharacter k n (leftProjection h) : ℂ) := by
  rw [T.leftLeviCharacter_apply, T.leftLeviCharacter_apply, coe_realPowerCharacter,
    coe_realPowerCharacter]
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
  rw [T.determinantNorm_leftSubgroup h, T.determinantNorm_successor, Units.val_mul, NNReal.coe_mul]
  set A : ℝ := ((T.determinantNorm k (leftProjection h).1 : NNReal) : ℝ) with hAdef
  set P : ℝ := ((T.determinantNorm (n + 1) (leftProjection h).2.val : NNReal) : ℝ) with hPdef
  have hA : 0 < A := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
  have hP : 0 < P := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  have e1 : A ^ (((n + 1 + 1 : ℕ) : ℝ) / 2) = A ^ (1 / 2 : ℝ) * A ^ (((n + 1 : ℕ) : ℝ) / 2) := by
    rw [← Real.rpow_add hA]
    congr 1
    push_cast
    ring
  have e3 : A ^ (-(1 / 2 : ℝ)) * A ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hA]
    norm_num
  have e4 : P ^ (-(1 / 2 : ℝ)) * P ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hP]
    norm_num
  rw [e1, Real.mul_rpow hA.le hP.le]
  calc A ^ (-(1 / 2 : ℝ)) * P ^ (-(1 / 2 : ℝ)) *
        (A ^ (1 / 2 : ℝ) * A ^ (((n + 1 : ℕ) : ℝ) / 2) * P ^ (-((k : ℝ) / 2)) * P ^ (1 / 2 : ℝ))
      = (A ^ (-(1 / 2 : ℝ)) * A ^ (1 / 2 : ℝ)) * (P ^ (-(1 / 2 : ℝ)) * P ^ (1 / 2 : ℝ)) *
          (A ^ (((n + 1 : ℕ) : ℝ) / 2) * P ^ (-((k : ℝ) / 2))) := by ring
    _ = _ := by rw [e3, e4, one_mul, one_mul]

end Scalar

/-! ## The value map `ρ × Φ̂⁺(σ) → ρ × σ` -/

section Product

variable (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) {k n : ℕ}

/-- Covariance of a case (II) function along the successor embedding:
`f(successor(h y)) = χ_L(a, successor p) • (ρ(a) ⊗ τ(successor p))(f(successor y))`,
where `(a, p) = leftProjection h`. -/
theorem leftMixedEval_successor_mul
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier))
    (f : letI := T.topology; (T.leftMixedProductFunctor k (n + 1)).obj X)
    (h : leftSubgroup k n F.Carrier) (y : mirabolic (k + n) F.Carrier) :
    letI := T.topology
    T.leftMixedEval X f (successor ((h : mirabolic (k + n) F.Carrier) * y)) =
      (T.leftLeviCharacter k (n + 1) ((leftProjection h).1, successor (leftProjection h).2) : ℂ) •
        TensorProduct.map (X.1.representation (leftProjection h).1)
          (X.2.representation (successor (leftProjection h).2))
          (T.leftMixedEval X f (successor y)) := by
  let := T.topology
  have hfst : (leftProjection (leftSuccessor h)).1 = (leftProjection h).1 :=
    congrArg Prod.fst (leftProjection_leftSuccessor h)
  have hsnd : (leftProjection (leftSuccessor h)).2 = successor (leftProjection h).2 :=
    congrArg Prod.snd (leftProjection_leftSuccessor h)
  have hχ : (T.leftLeviCharacter k (n + 1) (leftProjection (leftSuccessor h)) : ℂ) =
      T.leftLeviCharacter k (n + 1) ((leftProjection h).1, successor (leftProjection h).2) := by
    rw [leftProjection_leftSuccessor]
  have hc := T.leftMixedEval_covariant X f (leftSuccessor h) (successor y)
  rw [leftInducingRepresentation_apply, hχ, hfst, hsnd] at hc
  exact (congrArg (T.leftMixedEval X f)
    (map_mul successor (h : mirabolic (k + n) F.Carrier) y)).trans hc

/-- The source `ρ × Φ̂⁺(σ)`, a representation of `P_(k+n+2)`. -/
abbrev leftPhiHatSource
    (ρ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear k F.Carrier))
    (σ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (mirabolic n F.Carrier)) :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (k + n + 1) F.Carrier) :=
  letI := T.topology
  (T.leftMixedProductFunctor k (n + 1)).obj (ρ, (phiHatPlus T ψ n).obj σ)

/-- `y ↦ |det y|^(-1/2) • (id ⊗ ev₁)(f(successor y))`, a function `P_(k+n+1) → ρ ⊗ σ`. -/
def leftPhiHatValue
    (ρ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear k F.Carrier))
    (σ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (mirabolic n F.Carrier))
    (f : leftPhiHatSource T ψ ρ σ) (y : mirabolic (k + n) F.Carrier) : ρ ⊗[ℂ] σ :=
  letI := T.topology
  (phiMinusCharacter T (k + n) y : ℂ) •
    (phiHatPlusEvalAt T ψ n σ 1).lTensor ρ
      (T.leftMixedEval (ρ, (phiHatPlus T ψ n).obj σ) f (successor y))

theorem leftPhiHatValue_apply
    (ρ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear k F.Carrier))
    (σ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (mirabolic n F.Carrier))
    (f : leftPhiHatSource.{uV, uF} T ψ ρ σ) (y : mirabolic (k + n) F.Carrier) :
    leftPhiHatValue.{uV, uF} T ψ ρ σ f y =
      (phiMinusCharacter T (k + n) y : ℂ) •
        (phiHatPlusEvalAt T ψ n σ 1).lTensor ρ
          (T.leftMixedEval (ρ, (phiHatPlus T ψ n).obj σ) f (successor y)) :=
  rfl

/-- The algebraic part of `leftPhiHatValue_covariant`. -/
theorem leftPhiHatValue_covariant_aux
    (ρ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear k F.Carrier))
    (σ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (mirabolic n F.Carrier))
    (f : leftPhiHatSource.{uV, uF} T ψ ρ σ) (h : leftSubgroup k n F.Carrier)
    (y : mirabolic (k + n) F.Carrier) :
    letI := T.topology
    ((phiMinusCharacter T (k + n) (h : mirabolic (k + n) F.Carrier) : ℂ) *
          (phiMinusCharacter T (k + n) y : ℂ)) •
        (phiHatPlusEvalAt T ψ n σ 1).lTensor ρ
          ((T.leftLeviCharacter k (n + 1) ((leftProjection h).1, successor (leftProjection h).2) :
              ℂ) •
            TensorProduct.map (ρ.representation (leftProjection h).1)
              (((phiHatPlus T ψ n).obj σ).representation (successor (leftProjection h).2))
              (T.leftMixedEval (ρ, (phiHatPlus T ψ n).obj σ) f (successor y))) =
      (T.leftLeviCharacter k n (leftProjection h) : ℂ) •
        leftInducingRepresentation ρ.representation σ.representation h
          (leftPhiHatValue.{uV, uF} T ψ ρ σ f y) := by
  let := T.topology
  simp only [leftPhiHatValue_apply.{uV, uF}]
  simp only [LinearMap.map_smul, lTensor_evalAt_one_map_successor,
    leftInducingRepresentation_apply, smul_smul]
  congr 1
  linear_combination (phiMinusCharacter T (k + n) y : ℂ) *
    phiMinusCharacter_mul_leftLeviCharacter_successor T h

/-- The value map is covariant for the case (II) subgroup of `P_(k+n+1)`. -/
theorem leftPhiHatValue_covariant
    (ρ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear k F.Carrier))
    (σ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (mirabolic n F.Carrier))
    (f : leftPhiHatSource.{uV, uF} T ψ ρ σ) (h : leftSubgroup k n F.Carrier)
    (y : mirabolic (k + n) F.Carrier) :
    letI := T.topology
    leftPhiHatValue.{uV, uF} T ψ ρ σ f ((h : mirabolic (k + n) F.Carrier) * y) =
      (T.leftLeviCharacter k n (leftProjection h) : ℂ) •
        leftInducingRepresentation ρ.representation σ.representation h
          (leftPhiHatValue.{uV, uF} T ψ ρ σ f y) := by
  let := T.topology
  have hc : (phiMinusCharacter T (k + n) ((h : mirabolic (k + n) F.Carrier) * y) : ℂ) =
      (phiMinusCharacter T (k + n) (h : mirabolic (k + n) F.Carrier) : ℂ) *
        (phiMinusCharacter T (k + n) y : ℂ) :=
    congrArg Units.val (map_mul (phiMinusCharacter T (k + n)) _ _)
  exact (congrArg₂ (fun (a : ℂ) b => a • (phiHatPlusEvalAt T ψ n σ 1).lTensor ρ b) hc
    (leftMixedEval_successor_mul T (ρ, (phiHatPlus T ψ n).obj σ) f h y)).trans
    (leftPhiHatValue_covariant_aux.{uV, uF} T ψ ρ σ f h y)

/-- `ν(1, p) = 1` on the radical part of the case (II) subgroup. -/
theorem leftLeviCharacter_leftRadical (u : radical (k + (n + 1)) F.Carrier) :
    (T.leftLeviCharacter k (n + 1) (leftProjection (leftRadical u)) : ℂ) = 1 := by
  have hν : T.determinantNorm (n + 1 + 1) (leftProjection (leftRadical u)).2.val = 1 :=
    T.determinantNorm_radical' (⟨_, leftProjection_leftRadical_snd_mem u⟩ : radical (n + 1) F.Carrier)
  rw [T.leftLeviCharacter_apply, leftProjection_leftRadical_fst, map_one, hν]
  simp

/-- Radical elements of `P_(k+n+2)` act on the value map through `θ`. -/
theorem leftPhiHatValue_radical
    (ρ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear k F.Carrier))
    (σ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (mirabolic n F.Carrier))
    (f : leftPhiHatSource.{uV, uF} T ψ ρ σ) (u : radical (k + n + 1) F.Carrier)
    (y : mirabolic (k + n) F.Carrier) :
    letI := T.topology
    leftPhiHatValue.{uV, uF} T ψ ρ σ
        ((leftPhiHatSource.{uV, uF} T ψ ρ σ).representation (u : mirabolic (k + n + 1) F.Carrier) f) y =
      (T.mirabolicTheta ψ (k + n) u : ℂ) • leftPhiHatValue.{uV, uF} T ψ ρ σ f y := by
  let := T.topology
  let w := Jacquet.Localization.conjugate (radical (k + n + 1) F.Carrier)
    (successorSubgroup (k + n) F.Carrier) successorSubgroup_le_normalizer (successorEquiv y) u
  have hw : successor y * (u : mirabolic (k + n + 1) F.Carrier) =
      ((leftRadical (k := k) (n := n + 1) w : leftSubgroup k (n + 1) F.Carrier) :
        mirabolic (k + (n + 1)) F.Carrier) * successor y := by
    change successor y * (u : mirabolic (k + n + 1) F.Carrier) =
      successor y * (u : mirabolic (k + n + 1) F.Carrier) * (successor y)⁻¹ * successor y
    group
  have hθ : theta ψ n ⟨(leftProjection (leftRadical (k := k) (n := n + 1) w)).2,
      leftProjection_leftRadical_snd_mem (k := k) (n := n + 1) w⟩ = T.mirabolicTheta ψ (k + n) u :=
    (theta_leftProjection_leftRadical (k := k) (n := n) ψ w).trans (theta_isInvariant ψ (k + n) _ u)
  have hrad := lTensor_evalAt_one_map_radical T ψ n σ (V := ρ)
    ⟨(leftProjection (leftRadical (k := k) (n := n + 1) w)).2,
      leftProjection_leftRadical_snd_mem (k := k) (n := n + 1) w⟩
    (T.leftMixedEval (ρ, (phiHatPlus T ψ n).obj σ) f (successor y))
  rw [hθ] at hrad
  rw [leftPhiHatValue_apply.{uV, uF}, leftPhiHatValue_apply.{uV, uF}]
  change (phiMinusCharacter T (k + n) y : ℂ) •
      (phiHatPlusEvalAt T ψ n σ 1).lTensor ρ
        (T.leftMixedEval (ρ, (phiHatPlus T ψ n).obj σ) f
          (successor y * (u : mirabolic (k + n + 1) F.Carrier))) = _
  rw [hw, T.leftMixedEval_covariant, leftLeviCharacter_leftRadical]
  -- `rw [one_smul]` would compare `1` with the character values by unfolding real powers.
  simp only [one_smul, leftInducingRepresentation_apply, leftProjection_leftRadical_fst, map_one]
  dsimp only at hrad
  rw [hrad]
  exact smul_comm _ _ _

/-- The value map is invariant under an open subgroup of right translations. -/
theorem leftPhiHatValue_exists_openSubgroup
    (ρ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear k F.Carrier))
    (σ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (mirabolic n F.Carrier))
    (f : leftPhiHatSource.{uV, uF} T ψ ρ σ) :
    letI := T.topology
    ∃ K : OpenSubgroup (mirabolic (k + n) F.Carrier), ∀ (u : K) (y : mirabolic (k + n) F.Carrier),
      leftPhiHatValue.{uV, uF} T ψ ρ σ f (y * (u : mirabolic (k + n) F.Carrier)) =
        leftPhiHatValue.{uV, uF} T ψ ρ σ f y := by
  let := T.topology
  obtain ⟨K₀, hK₀⟩ := T.leftMixedEval_exists_openSubgroup (ρ, (phiHatPlus T ψ n).obj σ) f
  let Kc : OpenSubgroup (mirabolic (k + n) F.Carrier) :=
    { toSubgroup := (phiMinusCharacter T (k + n)).ker
      isOpen' := isOpen_ker_phiMinusCharacter T (k + n) }
  refine ⟨K₀.comap successor continuous_successor ⊓ Kc, fun u y => ?_⟩
  have hu := OpenSubgroup.mem_inf.mp u.2
  have hu₁ : successor (u : mirabolic (k + n) F.Carrier) ∈ K₀ := OpenSubgroup.mem_comap.mp hu.1
  have hu₂ : phiMinusCharacter T (k + n) (u : mirabolic (k + n) F.Carrier) = 1 :=
    MonoidHom.mem_ker.mp hu.2
  have hc : (phiMinusCharacter T (k + n) (y * (u : mirabolic (k + n) F.Carrier)) : ℂ) =
      phiMinusCharacter T (k + n) y :=
    congrArg Units.val (((map_mul (phiMinusCharacter T (k + n)) _ _).trans
      (congrArg (phiMinusCharacter T (k + n) y * ·) hu₂)).trans (mul_one _))
  have hs : T.leftMixedEval (ρ, (phiHatPlus T ψ n).obj σ) f
      (successor (y * (u : mirabolic (k + n) F.Carrier))) =
      T.leftMixedEval (ρ, (phiHatPlus T ψ n).obj σ) f (successor y) :=
    (congrArg (T.leftMixedEval (ρ, (phiHatPlus T ψ n).obj σ) f) (map_mul successor _ _)).trans
      (hK₀ ⟨_, hu₁⟩ (successor y))
  exact congrArg₂ (fun (a : ℂ) b => a • (phiHatPlusEvalAt T ψ n σ 1).lTensor ρ b) hc hs

/-- The value map has compact support modulo the case (II) subgroup. -/
theorem leftPhiHatValue_isCompact
    (ρ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear k F.Carrier))
    (σ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (mirabolic n F.Carrier))
    (f : leftPhiHatSource.{uV, uF} T ψ ρ σ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + n + 1)
    IsCompact (Induction.quotientSupport (leftSubgroup k n F.Carrier)
      (leftPhiHatValue.{uV, uF} T ψ ρ σ f)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (k + n + 1)
  have := T.compactSpace_leftQuotient k n
  obtain ⟨K, hK⟩ := leftPhiHatValue_exists_openSubgroup.{uV, uF} T ψ ρ σ f
  exact Induction.isCompact_quotientSupport_of_covariant (leftSubgroup k n F.Carrier)
    (twist (T.leftCharacter k n).toMonoidHom
      (leftInducingRepresentation ρ.representation σ.representation))
    (leftPhiHatValue.{uV, uF} T ψ ρ σ f) (leftPhiHatValue_covariant.{uV, uF} T ψ ρ σ f) K hK

/-- The linear map `ρ × Φ̂⁺(σ) → ρ × σ` given by the value map. -/
def leftPhiHatMap
    (ρ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear k F.Carrier))
    (σ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (mirabolic n F.Carrier)) :
    leftPhiHatSource.{uV, uF} T ψ ρ σ →ₗ[ℂ]
      (letI := T.topology; (T.leftMixedProductFunctor k n).obj (ρ, σ)) := by
  letI := T.topology
  exact
    { toFun := fun f => T.leftMixedMk (ρ, σ) (leftPhiHatValue.{uV, uF} T ψ ρ σ f)
        (leftPhiHatValue_covariant.{uV, uF} T ψ ρ σ f)
        (leftPhiHatValue_exists_openSubgroup.{uV, uF} T ψ ρ σ f).choose
        (leftPhiHatValue_exists_openSubgroup.{uV, uF} T ψ ρ σ f).choose_spec
        (leftPhiHatValue_isCompact.{uV, uF} T ψ ρ σ f)
      map_add' := fun f g => by
        apply T.leftMixedEval_injective (ρ, σ)
        funext y
        change (phiMinusCharacter T (k + n) y : ℂ) • (phiHatPlusEvalAt T ψ n σ 1).lTensor ρ
            (T.leftMixedEval (ρ, (phiHatPlus T ψ n).obj σ) f (successor y) +
              T.leftMixedEval (ρ, (phiHatPlus T ψ n).obj σ) g (successor y)) =
          leftPhiHatValue.{uV, uF} T ψ ρ σ f y + leftPhiHatValue.{uV, uF} T ψ ρ σ g y
        rw [map_add, smul_add]
        rfl
      map_smul' := fun a f => by
        apply T.leftMixedEval_injective (ρ, σ)
        funext y
        change (phiMinusCharacter T (k + n) y : ℂ) • (phiHatPlusEvalAt T ψ n σ 1).lTensor ρ
            (a • T.leftMixedEval (ρ, (phiHatPlus T ψ n).obj σ) f (successor y)) =
          a • leftPhiHatValue.{uV, uF} T ψ ρ σ f y
        rw [map_smul]
        exact smul_comm _ _ _ }

theorem leftPhiHatMap_eval
    (ρ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear k F.Carrier))
    (σ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (mirabolic n F.Carrier))
    (f : leftPhiHatSource.{uV, uF} T ψ ρ σ) (y : mirabolic (k + n) F.Carrier) :
    T.leftMixedEval (ρ, σ) (leftPhiHatMap.{uV, uF} T ψ ρ σ f) y =
      leftPhiHatValue.{uV, uF} T ψ ρ σ f y :=
  rfl

/-- Radical elements act on the image through `θ`. -/
theorem leftPhiHatMap_radical
    (ρ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear k F.Carrier))
    (σ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (mirabolic n F.Carrier))
    (u : radical (k + n + 1) F.Carrier) (f : leftPhiHatSource.{uV, uF} T ψ ρ σ) :
    letI := T.topology
    leftPhiHatMap.{uV, uF} T ψ ρ σ
        ((leftPhiHatSource.{uV, uF} T ψ ρ σ).representation
          (u : mirabolic (k + n + 1) F.Carrier) f) =
      (T.mirabolicTheta ψ (k + n) u : ℂ) • leftPhiHatMap.{uV, uF} T ψ ρ σ f := by
  let := T.topology
  apply T.leftMixedEval_injective (ρ, σ)
  funext y
  exact leftPhiHatValue_radical.{uV, uF} T ψ ρ σ f u y

/-- `|det h|^(-1/2) • b(successor h • f) = h • b(f)`. -/
theorem leftPhiHatMap_successor
    (ρ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear k F.Carrier))
    (σ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (mirabolic n F.Carrier))
    (h : mirabolic (k + n) F.Carrier) (f : leftPhiHatSource.{uV, uF} T ψ ρ σ) :
    letI := T.topology
    (phiMinusCharacter T (k + n) h : ℂ) •
        leftPhiHatMap.{uV, uF} T ψ ρ σ
          ((leftPhiHatSource.{uV, uF} T ψ ρ σ).representation (successor h) f) =
      ((T.leftMixedProductFunctor k n).obj (ρ, σ)).representation h
        (leftPhiHatMap.{uV, uF} T ψ ρ σ f) := by
  let := T.topology
  apply T.leftMixedEval_injective (ρ, σ)
  funext y
  change (phiMinusCharacter T (k + n) h : ℂ) • ((phiMinusCharacter T (k + n) y : ℂ) •
      (phiHatPlusEvalAt T ψ n σ 1).lTensor ρ
        (T.leftMixedEval (ρ, (phiHatPlus T ψ n).obj σ) f (successor y * successor h))) =
    (phiMinusCharacter T (k + n) (y * h) : ℂ) •
      (phiHatPlusEvalAt T ψ n σ 1).lTensor ρ
        (T.leftMixedEval (ρ, (phiHatPlus T ψ n).obj σ) f (successor (y * h)))
  rw [smul_smul]
  exact congrArg₂ (fun (a : ℂ) b => a • (phiHatPlusEvalAt T ψ n σ 1).lTensor ρ b)
    ((mul_comm _ _).trans
      (congrArg Units.val (map_mul (phiMinusCharacter T (k + n)) y h)).symm)
    (congrArg (T.leftMixedEval (ρ, (phiHatPlus T ψ n).obj σ) f) (map_mul successor y h).symm)

/-- The descent of the value map to `Φ⁻(ρ × Φ̂⁺(σ)) → ρ × σ`. -/
def leftPhiHatDescent
    (ρ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear k F.Carrier))
    (σ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (mirabolic n F.Carrier)) :
    letI := T.topology
    ((phiMinus T ψ (k + n)).obj (leftPhiHatSource.{uV, uF} T ψ ρ σ)).representation.IntertwiningMap
      ((T.leftMixedProductFunctor k n).obj (ρ, σ)).representation := by
  letI := T.topology
  exact
    { toLinearMap := Jacquet.Localization.lift (leftPhiHatSource.{uV, uF} T ψ ρ σ).representation
        (radical (k + n + 1) F.Carrier) (T.mirabolicTheta ψ (k + n))
        (leftPhiHatMap.{uV, uF} T ψ ρ σ) (leftPhiHatMap_radical.{uV, uF} T ψ ρ σ)
      isIntertwining' := fun h => by
        apply Jacquet.Localization.hom_ext
        apply LinearMap.ext
        intro v
        change Jacquet.Localization.lift (leftPhiHatSource.{uV, uF} T ψ ρ σ).representation
            (radical (k + n + 1) F.Carrier) (T.mirabolicTheta ψ (k + n))
            (leftPhiHatMap.{uV, uF} T ψ ρ σ) (leftPhiHatMap_radical.{uV, uF} T ψ ρ σ)
            (((phiMinus T ψ (k + n)).obj (leftPhiHatSource.{uV, uF} T ψ ρ σ)).representation h
              (phiMinusQuotient T ψ (k + n) (leftPhiHatSource.{uV, uF} T ψ ρ σ) v)) =
          ((T.leftMixedProductFunctor k n).obj (ρ, σ)).representation h
            (leftPhiHatMap.{uV, uF} T ψ ρ σ v)
        rw [phiMinus_action]
        exact (map_smul _ _ _).trans (leftPhiHatMap_successor.{uV, uF} T ψ ρ σ h v) }

/-- Ze80 §5.3: the intertwiner `ρ × Φ̂⁺(σ) → Φ̂⁺(ρ × σ)` adjoint to `leftPhiHatDescent`. -/
def leftPhiHatEmbedding
    (ρ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear k F.Carrier))
    (σ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (mirabolic n F.Carrier)) :
    letI := T.topology
    (leftPhiHatSource.{uV, uF} T ψ ρ σ).representation.IntertwiningMap
      ((phiHatPlus T ψ (k + n)).obj ((T.leftMixedProductFunctor k n).obj (ρ, σ))).representation :=
  letI := T.topology
  (phiHatPlusAdjunction T ψ (k + n) (leftPhiHatSource.{uV, uF} T ψ ρ σ)
    ((T.leftMixedProductFunctor k n).obj (ρ, σ))).symm (leftPhiHatDescent.{uV, uF} T ψ ρ σ)

/-- The value of the embedding at `x` is the value map of the translate `x • f`. -/
theorem leftPhiHatEmbedding_eval
    (ρ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear k F.Carrier))
    (σ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (mirabolic n F.Carrier))
    (f : leftPhiHatSource.{uV, uF} T ψ ρ σ) (x : mirabolic (k + n + 1) F.Carrier) :
    letI := T.topology
    phiHatPlusNormalizedEval T ψ (k + n) ((T.leftMixedProductFunctor k n).obj (ρ, σ))
        (leftPhiHatEmbedding.{uV, uF} T ψ ρ σ f) x =
      leftPhiHatMap.{uV, uF} T ψ ρ σ
        ((leftPhiHatSource.{uV, uF} T ψ ρ σ).representation x f) :=
  rfl

/-- A vector of `ρ × Φ̂⁺(σ)` all of whose values die under `id ⊗ ev₁` is zero. -/
theorem leftPhiHatSource_eq_zero
    (ρ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear k F.Carrier))
    (σ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (mirabolic n F.Carrier))
    (f : leftPhiHatSource.{uV, uF} T ψ ρ σ)
    (hf : ∀ x : mirabolic (k + (n + 1)) F.Carrier,
      (phiHatPlusEvalAt T ψ n σ 1).lTensor ρ
        (T.leftMixedEval (ρ, (phiHatPlus T ψ n).obj σ) f x) = 0) :
    f = 0 := by
  let := T.topology
  apply T.leftMixedEval_injective (ρ, (phiHatPlus T ψ n).obj σ)
  funext x
  have hz : ∀ z : mirabolic (n + 1) F.Carrier,
      (phiHatPlusEvalAt T ψ n σ z).lTensor ρ
        (T.leftMixedEval (ρ, (phiHatPlus T ψ n).obj σ) f x) = 0 := by
    intro z
    have h := hf ((leftMatrix (1 : GeneralLinear k F.Carrier) z 0 :
      mirabolic (k + (n + 1)) F.Carrier) * x)
    rw [T.leftMixedEval_leftMatrix_mul, LinearMap.map_smul, map_one ρ.representation,
      lTensor_evalAt_one_map] at h
    exact (smul_eq_zero.mp h).resolve_left (Units.ne_zero _)
  have h0 : T.leftMixedEval (ρ, (phiHatPlus T ψ n).obj σ) f x = 0 := by
    apply MixedProductTensor.eq_zero_of_forall_dual_rTensor
    intro g
    apply phiHatPlusNormalizedEval_injective T ψ n σ
    funext z
    change phiHatPlusEvalAt T ψ n σ z _ = phiHatPlusEvalAt T ψ n σ z 0
    rw [map_zero, ← MixedProductTensor.lid_rTensor_lTensor, hz z, map_zero, map_zero]
  rw [h0]
  rfl

/-- The embedding `ρ × Φ̂⁺(σ) → Φ̂⁺(ρ × σ)` is injective. -/
theorem leftPhiHatEmbedding_injective
    (ρ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear k F.Carrier))
    (σ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (mirabolic n F.Carrier)) :
    Function.Injective (leftPhiHatEmbedding.{uV, uF} T ψ ρ σ) := by
  let := T.topology
  refine (injective_iff_map_eq_zero (leftPhiHatEmbedding.{uV, uF} T ψ ρ σ)).mpr fun f hf => ?_
  apply leftPhiHatSource_eq_zero.{uV, uF} T ψ ρ σ f
  intro x
  have h : leftPhiHatValue.{uV, uF} T ψ ρ σ
      ((leftPhiHatSource.{uV, uF} T ψ ρ σ).representation x f) 1 = 0 := by
    rw [← leftPhiHatMap_eval.{uV, uF}, ← leftPhiHatEmbedding_eval.{uV, uF}, hf]
    change T.leftMixedEval (ρ, σ) (phiHatPlusEvalAt T ψ (k + n)
      ((T.leftMixedProductFunctor k n).obj (ρ, σ)) x 0) 1 = 0
    rw [map_zero]
    rfl
  simp only [leftPhiHatValue_apply.{uV, uF}, map_one, Units.val_one, one_smul] at h
  rw [← one_mul x]
  exact h

/-- The embedding as a morphism of smooth representations. -/
def leftPhiHatEmbeddingHom
    (ρ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear k F.Carrier))
    (σ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (mirabolic n F.Carrier)) :
    letI := T.topology
    leftPhiHatSource.{uV, uF} T ψ ρ σ ⟶
      (phiHatPlus T ψ (k + n)).obj ((T.leftMixedProductFunctor k n).obj (ρ, σ)) :=
  letI := T.topology
  SmoothRep.ofHom (leftPhiHatEmbedding.{uV, uF} T ψ ρ σ)

/-- Ze80 §5.3: `ρ × Φ̂⁺(σ) ↪ Φ̂⁺(ρ × σ)`. -/
theorem mono_leftPhiHatEmbeddingHom
    (ρ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear k F.Carrier))
    (σ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (mirabolic n F.Carrier)) :
    letI := T.topology
    Mono (leftPhiHatEmbeddingHom.{uV, uF} T ψ ρ σ) := by
  let := T.topology
  exact (SmoothRep.mono_iff_injective _).mpr (leftPhiHatEmbedding_injective.{uV, uF} T ψ ρ σ)

end Product

end Langlands.Derivative.Mirabolic
