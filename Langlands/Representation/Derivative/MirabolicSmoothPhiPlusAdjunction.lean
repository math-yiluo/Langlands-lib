import Langlands.Representation.Derivative.MirabolicSmoothPhiPlus

/-!
# The adjunctions `Φ⁻ ⊣ Φ̂⁺` and `Ψ⁻ ⊣ Ψ⁺`

Bernstein–Zelevinsky (1977), §3.2(b,c), for the published determinant-normalized
`Φ⁻`, `Ψ⁻`, `Ψ⁺` and the smooth `Φ̂⁺`. Each adjunction is an actual complex-linear
equivalence of intertwiner spaces, natural in both arguments:

* `Hom(A, Φ̂⁺ σ) ≃ Hom(Φ⁻ A, σ)`, sending `Φ` to `q(v) ↦ Φ(v)(1)`;
* `Hom(A, Ψ⁺ θ) ≃ Hom(Ψ⁻ A, θ)`, sending `f` to `q(v) ↦ f(v)`.

The inverse of the first sends `B` to `v ↦ (x ↦ B(q(x • v)))`. The two normalizing
characters `|det|^(-1/2)` and `|det|^(1/2)` cancel. No exactness is used or stated.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative.Mirabolic

open GeneralLinear GeneralLinear.Mirabolic HarmonicAnalysis

universe uA uB uV uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-! ## Cancellation of the normalizing characters -/

theorem phiMinusCharacter_mul_phiPlusCharacter_apply (T : F.TopologicalData) (n : ℕ)
    (g : mirabolic n F.Carrier) :
    (phiMinusCharacter T n g : ℂ) * (phiPlusCharacter T n g : ℂ) = 1 := by
  have h := congrArg (fun χ : mirabolic n F.Carrier →* ℂˣ => ((χ g : ℂˣ) : ℂ))
    (phiPlusCharacter_mul_phiMinusCharacter T n)
  simp only [MonoidHom.mul_apply, MonoidHom.one_apply, Units.val_mul, Units.val_one] at h
  rw [mul_comm]
  exact h

theorem psiMinusCharacter_mul_psiPlusCharacter_apply (T : F.TopologicalData) (n : ℕ)
    (g : Langlands.GeneralLinear n F.Carrier) :
    (psiMinusCharacter T n g : ℂ) * (psiPlusCharacter T n g : ℂ) = 1 := by
  have h := congrArg (fun χ : Langlands.GeneralLinear n F.Carrier →* ℂˣ => ((χ g : ℂˣ) : ℂ))
    (psiPlusCharacter_mul_psiMinusCharacter T n)
  simp only [MonoidHom.mul_apply, MonoidHom.one_apply, Units.val_mul, Units.val_one] at h
  rw [mul_comm]
  exact h

/-! ## `Φ⁻ ⊣ Φ̂⁺` -/

section PhiAdjunction

variable (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ)

/-- Evaluation at `1` of an intertwiner into `Φ̂⁺(σ)`, before descent to `Φ⁻`. -/
def phiHatPlusEvalOne :
    letI := T.topology
    (A : SmoothRep.{0, uF, uA} ℂ (mirabolic (n + 1) F.Carrier)) →
      (σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) →
      A.representation.IntertwiningMap ((phiHatPlus T ψ n).obj σ).representation →
        A →ₗ[ℂ] σ := by
  letI := T.topology
  exact fun A σ Φ =>
    { toFun := fun v => phiHatPlusNormalizedEval T ψ n σ (Φ v) 1
      map_add' := fun v w => by
        rw [map_add]
        rfl
      map_smul' := fun c v => by
        rw [map_smul]
        rfl }

theorem phiHatPlusEvalOne_apply :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uA} ℂ (mirabolic (n + 1) F.Carrier))
      (σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (Φ : A.representation.IntertwiningMap ((phiHatPlus T ψ n).obj σ).representation) (v : A),
      phiHatPlusEvalOne T ψ n A σ Φ v = phiHatPlusNormalizedEval T ψ n σ (Φ v) 1 := by
  intros
  rfl

/-- Equivariance turns evaluation of a translate into evaluation at the point. -/
theorem phiHatPlusEvalOne_translate :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uA} ℂ (mirabolic (n + 1) F.Carrier))
      (σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (Φ : A.representation.IntertwiningMap ((phiHatPlus T ψ n).obj σ).representation)
      (g : mirabolic (n + 1) F.Carrier) (v : A),
      phiHatPlusEvalOne T ψ n A σ Φ (A.representation g v) =
        phiHatPlusNormalizedEval T ψ n σ (Φ v) g := by
  let := T.topology
  intro A σ Φ g v
  rw [phiHatPlusEvalOne_apply, Representation.IntertwiningMap.isIntertwining, phiHatPlus_action,
    one_mul]

theorem phiHatPlusEvalOne_radical :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uA} ℂ (mirabolic (n + 1) F.Carrier))
      (σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (Φ : A.representation.IntertwiningMap ((phiHatPlus T ψ n).obj σ).representation)
      (u : radical (n + 1) F.Carrier) (v : A),
      phiHatPlusEvalOne T ψ n A σ Φ (A.representation (u : mirabolic (n + 1) F.Carrier) v) =
        (T.mirabolicTheta ψ n u : ℂ) • phiHatPlusEvalOne T ψ n A σ Φ v := by
  let := T.topology
  intro A σ Φ u v
  rw [phiHatPlusEvalOne_translate, phiHatPlusEvalOne_apply]
  have h := phiHatPlusNormalizedEval_radical_mul T ψ n σ (Φ v) u 1
  rw [mul_one] at h
  exact h

theorem phiHatPlusEvalOne_successor :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uA} ℂ (mirabolic (n + 1) F.Carrier))
      (σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (Φ : A.representation.IntertwiningMap ((phiHatPlus T ψ n).obj σ).representation)
      (g : mirabolic n F.Carrier) (v : A),
      phiHatPlusEvalOne T ψ n A σ Φ (A.representation (successor g) v) =
        (phiPlusCharacter T n g : ℂ) • σ.representation g (phiHatPlusEvalOne T ψ n A σ Φ v) := by
  let := T.topology
  intro A σ Φ g v
  rw [phiHatPlusEvalOne_translate, phiHatPlusEvalOne_apply]
  have h := phiHatPlusNormalizedEval_successor_mul T ψ n σ (Φ v) g 1
  rw [mul_one] at h
  exact h

/-- Equivariance of the evaluation at `1` for the normalized `Φ⁻` action. -/
theorem phiHatPlusEvalOne_phiMinus_action :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uA} ℂ (mirabolic (n + 1) F.Carrier))
      (σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (Φ : A.representation.IntertwiningMap ((phiHatPlus T ψ n).obj σ).representation)
      (h : mirabolic n F.Carrier) (v : A),
      (phiMinusCharacter T n h : ℂ) •
          phiHatPlusEvalOne T ψ n A σ Φ (A.representation (successor h) v) =
        σ.representation h (phiHatPlusEvalOne T ψ n A σ Φ v) := by
  let := T.topology
  intro A σ Φ h v
  rw [phiHatPlusEvalOne_successor, smul_smul, phiMinusCharacter_mul_phiPlusCharacter_apply,
    one_smul]

/-- The forward map `Hom(A, Φ̂⁺ σ) → Hom(Φ⁻ A, σ)`: evaluation at `1`, descended. -/
def phiHatPlusAdjForward :
    letI := T.topology
    (A : SmoothRep.{0, uF, uA} ℂ (mirabolic (n + 1) F.Carrier)) →
      (σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) →
      A.representation.IntertwiningMap ((phiHatPlus T ψ n).obj σ).representation →
        ((phiMinus T ψ n).obj A).representation.IntertwiningMap σ.representation := by
  letI := T.topology
  exact fun A σ Φ =>
    { toLinearMap := Jacquet.Localization.lift A.representation (radical (n + 1) F.Carrier)
        (T.mirabolicTheta ψ n) (phiHatPlusEvalOne T ψ n A σ Φ)
        (phiHatPlusEvalOne_radical T ψ n A σ Φ)
      isIntertwining' := fun h => by
        apply Jacquet.Localization.hom_ext
        apply LinearMap.ext
        intro v
        change Jacquet.Localization.lift A.representation (radical (n + 1) F.Carrier)
            (T.mirabolicTheta ψ n) (phiHatPlusEvalOne T ψ n A σ Φ)
            (phiHatPlusEvalOne_radical T ψ n A σ Φ)
            (((phiMinus T ψ n).obj A).representation h (phiMinusQuotient T ψ n A v)) =
          σ.representation h (phiHatPlusEvalOne T ψ n A σ Φ v)
        rw [phiMinus_action, ← phiHatPlusEvalOne_phiMinus_action]
        exact map_smul _ _ _ }

theorem phiHatPlusAdjForward_mk :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uA} ℂ (mirabolic (n + 1) F.Carrier))
      (σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (Φ : A.representation.IntertwiningMap ((phiHatPlus T ψ n).obj σ).representation) (v : A),
      phiHatPlusAdjForward T ψ n A σ Φ (phiMinusQuotient T ψ n A v) =
        phiHatPlusNormalizedEval T ψ n σ (Φ v) 1 := by
  intros
  rfl

/-- The composite `v ↦ B(q(v))` of an intertwiner out of `Φ⁻ A` with the quotient map. -/
def phiMinusAdjValue :
    letI := T.topology
    (A : SmoothRep.{0, uF, uA} ℂ (mirabolic (n + 1) F.Carrier)) →
      (σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) →
      ((phiMinus T ψ n).obj A).representation.IntertwiningMap σ.representation →
        A →ₗ[ℂ] σ := by
  letI := T.topology
  exact fun A σ B => B.toLinearMap ∘ₗ phiMinusQuotient T ψ n A

theorem phiMinusAdjValue_apply :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uA} ℂ (mirabolic (n + 1) F.Carrier))
      (σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (B : ((phiMinus T ψ n).obj A).representation.IntertwiningMap σ.representation) (v : A),
      phiMinusAdjValue T ψ n A σ B v = B (phiMinusQuotient T ψ n A v) := by
  intros
  rfl

/-- Radical elements act on `v ↦ B(q(v))` through `Θ`. -/
theorem phiMinusAdjValue_radical :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uA} ℂ (mirabolic (n + 1) F.Carrier))
      (σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (B : ((phiMinus T ψ n).obj A).representation.IntertwiningMap σ.representation)
      (u : radical (n + 1) F.Carrier) (v : A),
      phiMinusAdjValue T ψ n A σ B (A.representation (u : mirabolic (n + 1) F.Carrier) v) =
        (T.mirabolicTheta ψ n u : ℂ) • phiMinusAdjValue T ψ n A σ B v := by
  let := T.topology
  intro A σ B u v
  rw [phiMinusAdjValue_apply, phiMinusAdjValue_apply, phiMinusQuotient_radical]
  exact map_smul B _ _

/-- An intertwiner out of `Φ⁻ A` moves `successor g` to `|det g|^(1/2) σ(g)`. -/
theorem phiMinusAdjValue_successor :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uA} ℂ (mirabolic (n + 1) F.Carrier))
      (σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (B : ((phiMinus T ψ n).obj A).representation.IntertwiningMap σ.representation)
      (g : mirabolic n F.Carrier) (w : A),
      phiMinusAdjValue T ψ n A σ B (A.representation (successor g) w) =
        (phiPlusCharacter T n g : ℂ) • σ.representation g (phiMinusAdjValue T ψ n A σ B w) := by
  let := T.topology
  intro A σ B g w
  have h : (phiMinusCharacter T n g : ℂ) •
      phiMinusAdjValue T ψ n A σ B (A.representation (successor g) w) =
        σ.representation g (phiMinusAdjValue T ψ n A σ B w) := by
    rw [phiMinusAdjValue_apply, phiMinusAdjValue_apply,
      ← Representation.IntertwiningMap.isIntertwining _ _ B g (phiMinusQuotient T ψ n A w),
      phiMinus_action]
    exact (map_smul B _ _).symm
  rw [← h, smul_smul, mul_comm, phiMinusCharacter_mul_phiPlusCharacter_apply, one_smul]

/-- The orbit functions `x ↦ B(q(x • v))` are covariant for the normalized `τ'`. -/
theorem phiMinusAdjValue_covariant :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uA} ℂ (mirabolic (n + 1) F.Carrier))
      (σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (B : ((phiMinus T ψ n).obj A).representation.IntertwiningMap σ.representation)
      (v : A) (q : plusSubgroup n F.Carrier) (x : mirabolic (n + 1) F.Carrier),
      phiMinusAdjValue T ψ n A σ B
          (A.representation ((q : mirabolic (n + 1) F.Carrier) * x) v) =
        plusTwistRepresentation ψ n (Langlands.twist (phiPlusCharacter T n) σ.representation) q
          (phiMinusAdjValue T ψ n A σ B (A.representation x v)) := by
  let := T.topology
  intro A σ B v q x
  obtain ⟨u, g, rfl⟩ : ∃ (u : radical (n + 1) F.Carrier) (g : mirabolic n F.Carrier),
      q = plusRadical u * plusSuccessor g :=
    ⟨_, _, plus_eq_plusRadical_mul_plusSuccessor q⟩
  rw [plusTwistRepresentation_plusRadical_mul_plusSuccessor, Subgroup.coe_mul, plusRadical_val,
    plusSuccessor_val, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
    phiMinusAdjValue_radical, phiMinusAdjValue_successor]
  rfl

/-- The orbit functions `x ↦ B(q(x • v))`, before restricting to smooth vectors. -/
def phiHatPlusOrbitMap :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (n + 1 + 1)
    (A : SmoothRep.{0, uF, uA} ℂ (mirabolic (n + 1) F.Carrier)) →
      (σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) →
      ((phiMinus T ψ n).obj A).representation.IntertwiningMap σ.representation →
        A.representation.IntertwiningMap
          (Induction.equivariantAction (plusSubgroup n F.Carrier)
            (plusTwistRepresentation ψ n
              (Langlands.twist (phiPlusCharacter T n) σ.representation))) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (n + 1 + 1)
  exact fun A σ B =>
    { toLinearMap :=
        { toFun := fun v => ⟨fun x => phiMinusAdjValue T ψ n A σ B (A.representation x v),
            phiMinusAdjValue_covariant T ψ n A σ B v⟩
          map_add' := by
            intro v w
            apply Subtype.ext
            funext x
            change phiMinusAdjValue T ψ n A σ B (A.representation x (v + w)) =
              phiMinusAdjValue T ψ n A σ B (A.representation x v) +
                phiMinusAdjValue T ψ n A σ B (A.representation x w)
            rw [map_add, map_add]
          map_smul' := by
            intro c v
            apply Subtype.ext
            funext x
            change phiMinusAdjValue T ψ n A σ B (A.representation x (c • v)) =
              c • phiMinusAdjValue T ψ n A σ B (A.representation x v)
            rw [map_smul, map_smul] }
      isIntertwining' := fun g => by
        apply LinearMap.ext
        intro v
        apply Subtype.ext
        funext x
        change phiMinusAdjValue T ψ n A σ B (A.representation x (A.representation g v)) =
          phiMinusAdjValue T ψ n A σ B (A.representation (x * g) v)
        rw [map_mul, Module.End.mul_apply] }

/-- The backward map `Hom(Φ⁻ A, σ) → Hom(A, Φ̂⁺ σ)`: smooth orbit functions. -/
def phiHatPlusAdjBackward :
    letI := T.topology
    (A : SmoothRep.{0, uF, uA} ℂ (mirabolic (n + 1) F.Carrier)) →
      (σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) →
      ((phiMinus T ψ n).obj A).representation.IntertwiningMap σ.representation →
        A.representation.IntertwiningMap ((phiHatPlus T ψ n).obj σ).representation := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (n + 1 + 1)
  exact fun A σ B => smoothLift A.isSmooth (phiHatPlusOrbitMap T ψ n A σ B)

theorem phiHatPlusAdjBackward_eval :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uA} ℂ (mirabolic (n + 1) F.Carrier))
      (σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (B : ((phiMinus T ψ n).obj A).representation.IntertwiningMap σ.representation)
      (v : A) (x : mirabolic (n + 1) F.Carrier),
      phiHatPlusNormalizedEval T ψ n σ (phiHatPlusAdjBackward T ψ n A σ B v) x =
        B (phiMinusQuotient T ψ n A (A.representation x v)) := by
  intros
  rfl

/-- BZ77 §3.2(c): `Φ⁻` is left adjoint to `Φ̂⁺`, as an actual linear equivalence of
intertwiner spaces whose formula is evaluation at the identity. -/
def phiHatPlusAdjunction :
    letI := T.topology
    (A : SmoothRep.{0, uF, uA} ℂ (mirabolic (n + 1) F.Carrier)) →
      (σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) →
      A.representation.IntertwiningMap ((phiHatPlus T ψ n).obj σ).representation ≃ₗ[ℂ]
        ((phiMinus T ψ n).obj A).representation.IntertwiningMap σ.representation := by
  letI := T.topology
  exact fun A σ =>
    { toFun := phiHatPlusAdjForward T ψ n A σ
      invFun := phiHatPlusAdjBackward T ψ n A σ
      left_inv := fun Φ => by
        apply Representation.IntertwiningMap.ext
        apply LinearMap.ext
        intro v
        apply phiHatPlusNormalizedEval_injective T ψ n σ
        funext x
        exact phiHatPlusEvalOne_translate T ψ n A σ Φ x v
      right_inv := fun B => by
        apply Representation.IntertwiningMap.ext
        apply Jacquet.Localization.hom_ext
        apply LinearMap.ext
        intro v
        change phiHatPlusAdjForward T ψ n A σ (phiHatPlusAdjBackward T ψ n A σ B)
            (phiMinusQuotient T ψ n A v) = B (phiMinusQuotient T ψ n A v)
        rw [phiHatPlusAdjForward_mk, phiHatPlusAdjBackward_eval, map_one, Module.End.one_apply]
      map_add' := fun Φ Ψ => by
        apply Representation.IntertwiningMap.ext
        apply Jacquet.Localization.hom_ext
        apply LinearMap.ext
        intro v
        rfl
      map_smul' := fun c Φ => by
        apply Representation.IntertwiningMap.ext
        apply Jacquet.Localization.hom_ext
        apply LinearMap.ext
        intro v
        rfl }

/-- The adjunction is evaluation at the identity on quotient classes. -/
theorem phiHatPlusAdjunction_mk :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uA} ℂ (mirabolic (n + 1) F.Carrier))
      (σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (Φ : A.representation.IntertwiningMap ((phiHatPlus T ψ n).obj σ).representation) (v : A),
      phiHatPlusAdjunction T ψ n A σ Φ (phiMinusQuotient T ψ n A v) =
        phiHatPlusNormalizedEval T ψ n σ (Φ v) 1 := by
  intros
  rfl

/-- The inverse adjunction is the orbit-function formula. -/
theorem phiHatPlusAdjunction_symm_eval :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uA} ℂ (mirabolic (n + 1) F.Carrier))
      (σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (B : ((phiMinus T ψ n).obj A).representation.IntertwiningMap σ.representation)
      (v : A) (x : mirabolic (n + 1) F.Carrier),
      phiHatPlusNormalizedEval T ψ n σ ((phiHatPlusAdjunction T ψ n A σ).symm B v) x =
        B (phiMinusQuotient T ψ n A (A.representation x v)) := by
  intros
  rfl

/-- Naturality in the left argument: precomposition by `f : A' ⟶ A` corresponds to
precomposition by `Φ⁻ f`. -/
theorem phiHatPlusAdjunction_comp_left :
    letI := T.topology
    ∀ {A' A : SmoothRep.{0, uF, uA} ℂ (mirabolic (n + 1) F.Carrier)} (f : A' ⟶ A)
      (σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (Φ : A.representation.IntertwiningMap ((phiHatPlus T ψ n).obj σ).representation),
      phiHatPlusAdjunction T ψ n A' σ (Φ.comp (SmoothRep.hom f)) =
        (phiHatPlusAdjunction T ψ n A σ Φ).comp (SmoothRep.hom ((phiMinus T ψ n).map f)) := by
  let := T.topology
  intro A' A f σ Φ
  apply Representation.IntertwiningMap.ext
  apply Jacquet.Localization.hom_ext
  apply LinearMap.ext
  intro v
  rfl

/-- Naturality in the right argument: postcomposition by `Φ̂⁺ g` corresponds to
postcomposition by `g`. -/
theorem phiHatPlusAdjunction_comp_right :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uA} ℂ (mirabolic (n + 1) F.Carrier))
      {σ σ' : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)} (g : σ ⟶ σ')
      (Φ : A.representation.IntertwiningMap ((phiHatPlus T ψ n).obj σ).representation),
      phiHatPlusAdjunction T ψ n A σ' ((SmoothRep.hom ((phiHatPlus T ψ n).map g)).comp Φ) =
        (SmoothRep.hom g).comp (phiHatPlusAdjunction T ψ n A σ Φ) := by
  let := T.topology
  intro A σ σ' g Φ
  apply Representation.IntertwiningMap.ext
  apply Jacquet.Localization.hom_ext
  apply LinearMap.ext
  intro v
  rfl

end PhiAdjunction

/-! ## `Ψ⁻ ⊣ Ψ⁺` -/

section PsiAdjunction

variable (T : F.TopologicalData) (n : ℕ)

/-- An intertwiner into `Ψ⁺ θ` is constant on radical orbits. -/
theorem psiPlusAdj_radical :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uA} ℂ (mirabolic n F.Carrier))
      (θ : SmoothRep.{0, uF, uV} ℂ (Langlands.GeneralLinear n F.Carrier))
      (f : A.representation.IntertwiningMap ((psiPlus T n).obj θ).representation)
      (u : radical n F.Carrier) (v : A),
      f (A.representation (u : mirabolic n F.Carrier) v) =
        ((1 : radical n F.Carrier →* ℂˣ) u : ℂ) • f v := by
  let := T.topology
  intro A θ f u v
  rw [Representation.IntertwiningMap.isIntertwining, MonoidHom.one_apply, Units.val_one,
    one_smul]
  exact psiPlus_radical T n θ u (f v)

/-- The forward map `Hom(A, Ψ⁺ θ) → Hom(Ψ⁻ A, θ)`: descent to coinvariants. -/
def psiPlusAdjForward :
    letI := T.topology
    (A : SmoothRep.{0, uF, uA} ℂ (mirabolic n F.Carrier)) →
      (θ : SmoothRep.{0, uF, uV} ℂ (Langlands.GeneralLinear n F.Carrier)) →
      A.representation.IntertwiningMap ((psiPlus T n).obj θ).representation →
        ((psiMinus T n).obj A).representation.IntertwiningMap θ.representation := by
  letI := T.topology
  exact fun A θ f =>
    { toLinearMap := Jacquet.Localization.lift A.representation (radical n F.Carrier) 1
        f.toLinearMap (psiPlusAdj_radical T n A θ f)
      isIntertwining' := fun a => by
        apply Jacquet.Localization.hom_ext
        apply LinearMap.ext
        intro v
        change Jacquet.Localization.lift A.representation (radical n F.Carrier) 1
            f.toLinearMap (psiPlusAdj_radical T n A θ f)
            (((psiMinus T n).obj A).representation a (psiMinusQuotient T n A v)) =
          θ.representation a (f v)
        rw [psiMinus_action, map_smul]
        change (psiMinusCharacter T n a : ℂ) • f (A.representation (levi a) v) = _
        rw [Representation.IntertwiningMap.isIntertwining, psiPlus_levi]
        change (psiMinusCharacter T n a : ℂ) •
          ((psiPlusCharacter T n a : ℂ) • θ.representation a (f v)) = _
        rw [smul_smul, psiMinusCharacter_mul_psiPlusCharacter_apply, one_smul] }

theorem psiPlusAdjForward_mk :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uA} ℂ (mirabolic n F.Carrier))
      (θ : SmoothRep.{0, uF, uV} ℂ (Langlands.GeneralLinear n F.Carrier))
      (f : A.representation.IntertwiningMap ((psiPlus T n).obj θ).representation) (v : A),
      psiPlusAdjForward T n A θ f (psiMinusQuotient T n A v) = f v := by
  intros
  rfl

/-- The backward map `Hom(Ψ⁻ A, θ) → Hom(A, Ψ⁺ θ)`: composition with the quotient. -/
def psiPlusAdjBackward :
    letI := T.topology
    (A : SmoothRep.{0, uF, uA} ℂ (mirabolic n F.Carrier)) →
      (θ : SmoothRep.{0, uF, uV} ℂ (Langlands.GeneralLinear n F.Carrier)) →
      ((psiMinus T n).obj A).representation.IntertwiningMap θ.representation →
        A.representation.IntertwiningMap ((psiPlus T n).obj θ).representation := by
  letI := T.topology
  exact fun A θ B =>
    { toLinearMap := B.toLinearMap ∘ₗ psiMinusQuotient T n A
      isIntertwining' := fun g => by
        apply LinearMap.ext
        intro v
        change B (psiMinusQuotient T n A (A.representation g v)) =
          ((psiPlus T n).obj θ).representation g (B (psiMinusQuotient T n A v))
        rw [psiPlus_action]
        conv_lhs => rw [eq_radicalElement_mul_levi g, map_mul, Module.End.mul_apply,
          psiMinusQuotient_radical]
        have h : (psiMinusCharacter T n (projection g) : ℂ) •
            B (psiMinusQuotient T n A (A.representation (levi (projection g)) v)) =
              θ.representation (projection g) (B (psiMinusQuotient T n A v)) := by
          rw [← Representation.IntertwiningMap.isIntertwining _ _ B (projection g)
            (psiMinusQuotient T n A v), psiMinus_action]
          exact (map_smul B _ _).symm
        rw [← h, smul_smul, mul_comm, psiMinusCharacter_mul_psiPlusCharacter_apply, one_smul] }

theorem psiPlusAdjBackward_apply :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uA} ℂ (mirabolic n F.Carrier))
      (θ : SmoothRep.{0, uF, uV} ℂ (Langlands.GeneralLinear n F.Carrier))
      (B : ((psiMinus T n).obj A).representation.IntertwiningMap θ.representation) (v : A),
      psiPlusAdjBackward T n A θ B v = B (psiMinusQuotient T n A v) := by
  intros
  rfl

/-- BZ77 §3.2(b): `Ψ⁻` is left adjoint to `Ψ⁺`, as an actual linear equivalence of
intertwiner spaces whose formula is descent to the coinvariants. -/
def psiPlusAdjunction :
    letI := T.topology
    (A : SmoothRep.{0, uF, uA} ℂ (mirabolic n F.Carrier)) →
      (θ : SmoothRep.{0, uF, uV} ℂ (Langlands.GeneralLinear n F.Carrier)) →
      A.representation.IntertwiningMap ((psiPlus T n).obj θ).representation ≃ₗ[ℂ]
        ((psiMinus T n).obj A).representation.IntertwiningMap θ.representation := by
  letI := T.topology
  exact fun A θ =>
    { toFun := psiPlusAdjForward T n A θ
      invFun := psiPlusAdjBackward T n A θ
      left_inv := fun f => by
        apply Representation.IntertwiningMap.ext
        apply LinearMap.ext
        intro v
        rfl
      right_inv := fun B => by
        apply Representation.IntertwiningMap.ext
        apply Jacquet.Localization.hom_ext
        apply LinearMap.ext
        intro v
        rfl
      map_add' := fun f g => by
        apply Representation.IntertwiningMap.ext
        apply Jacquet.Localization.hom_ext
        apply LinearMap.ext
        intro v
        rfl
      map_smul' := fun c f => by
        apply Representation.IntertwiningMap.ext
        apply Jacquet.Localization.hom_ext
        apply LinearMap.ext
        intro v
        rfl }

theorem psiPlusAdjunction_mk :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uA} ℂ (mirabolic n F.Carrier))
      (θ : SmoothRep.{0, uF, uV} ℂ (Langlands.GeneralLinear n F.Carrier))
      (f : A.representation.IntertwiningMap ((psiPlus T n).obj θ).representation) (v : A),
      psiPlusAdjunction T n A θ f (psiMinusQuotient T n A v) = f v := by
  intros
  rfl

theorem psiPlusAdjunction_symm_apply :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uA} ℂ (mirabolic n F.Carrier))
      (θ : SmoothRep.{0, uF, uV} ℂ (Langlands.GeneralLinear n F.Carrier))
      (B : ((psiMinus T n).obj A).representation.IntertwiningMap θ.representation) (v : A),
      (psiPlusAdjunction T n A θ).symm B v = B (psiMinusQuotient T n A v) := by
  intros
  rfl

theorem psiPlusAdjunction_comp_left :
    letI := T.topology
    ∀ {A' A : SmoothRep.{0, uF, uA} ℂ (mirabolic n F.Carrier)} (f : A' ⟶ A)
      (θ : SmoothRep.{0, uF, uV} ℂ (Langlands.GeneralLinear n F.Carrier))
      (Φ : A.representation.IntertwiningMap ((psiPlus T n).obj θ).representation),
      psiPlusAdjunction T n A' θ (Φ.comp (SmoothRep.hom f)) =
        (psiPlusAdjunction T n A θ Φ).comp (SmoothRep.hom ((psiMinus T n).map f)) := by
  let := T.topology
  intro A' A f θ Φ
  apply Representation.IntertwiningMap.ext
  apply Jacquet.Localization.hom_ext
  apply LinearMap.ext
  intro v
  rfl

theorem psiPlusAdjunction_comp_right :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uA} ℂ (mirabolic n F.Carrier))
      {θ θ' : SmoothRep.{0, uF, uV} ℂ (Langlands.GeneralLinear n F.Carrier)} (g : θ ⟶ θ')
      (Φ : A.representation.IntertwiningMap ((psiPlus T n).obj θ).representation),
      psiPlusAdjunction T n A θ' ((SmoothRep.hom ((psiPlus T n).map g)).comp Φ) =
        (SmoothRep.hom g).comp (psiPlusAdjunction T n A θ Φ) := by
  let := T.topology
  intro A θ θ' g Φ
  apply Representation.IntertwiningMap.ext
  apply Jacquet.Localization.hom_ext
  apply LinearMap.ext
  intro v
  rfl

end PsiAdjunction

end Langlands.Derivative.Mirabolic
