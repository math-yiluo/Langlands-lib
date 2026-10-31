import Langlands.Representation.Derivative.Iteration
import Langlands.Representation.Shahidi.TwoBlocks

/-!
# Actual determinant normalization in the positive Jacquet comparison

The normalization of the existing iterated minus functors is evaluated on their
actual quotient maps. This module also computes the inverse-half two-block modulus
on the first general-linear factor. It does not construct a localization-tower
equivalence or prove the final Jacquet-to-derivative comparison.
-/

noncomputable section

open CategoryTheory
open scoped NNReal

namespace Langlands.Derivative.JacquetNormalization

open GeneralLinear GeneralLinear.Mirabolic HarmonicAnalysis

universe uF uV

section Matrices

variable {R : Type uF} [CommRing R]

/-- The actual block sum has the product of the two actual determinants. -/
theorem determinant_blockSum {n m : ℕ} (g : GeneralLinear n R)
    (h : GeneralLinear m R) :
    GeneralLinear.determinant (GeneralLinear.blockSum (g, h)) =
      GeneralLinear.determinant g * GeneralLinear.determinant h := by
  apply Units.ext
  change Matrix.det (Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks g.val 0 0 h.val)) = Matrix.det g.val * Matrix.det h.val
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

/-- Appending the final scalar one in the actual Levi embedding preserves determinant. -/
theorem determinant_levi {n : ℕ} (g : GeneralLinear n R) :
    GeneralLinear.determinant (levi g).val = GeneralLinear.determinant g := by
  change GeneralLinear.determinant (GeneralLinear.blockSum (g, (1 : GeneralLinear 1 R))) = _
  rw [determinant_blockSum, map_one, mul_one]

/-- The successor embedding used by `Φ⁻` preserves determinant. -/
theorem determinant_successor {n : ℕ} (h : mirabolic n R) :
    GeneralLinear.determinant (successor h).val = GeneralLinear.determinant h.val :=
  determinant_levi h.val

/-- The actual composite of the successor embeddings appearing in the minus iterate. -/
def successorIterate (n : ℕ) : (j : ℕ) → mirabolic n R →* mirabolic (n + j) R
  | 0 => MonoidHom.id _
  | j + 1 => successor.comp (successorIterate n j)

@[simp] theorem successorIterate_zero (n : ℕ) (h : mirabolic n R) :
    successorIterate n 0 h = h := rfl

@[simp] theorem successorIterate_succ (n j : ℕ) (h : mirabolic n R) :
    successorIterate n (j + 1) h = successor (successorIterate n j h) := rfl

/-- No step of the actual successor tower changes the determinant. -/
theorem determinant_successorIterate (n : ℕ) (j : ℕ) (h : mirabolic n R) :
    GeneralLinear.determinant (successorIterate n j h).val =
      GeneralLinear.determinant h.val := by
  induction j with
  | zero => rfl
  | succ j ih => rw [successorIterate_succ, determinant_successor, ih]

/-- The actual copy of `GL_n` acting before all `j` Phi steps and the final Psi step. -/
def generalLinearToMirabolic (n j : ℕ) : GeneralLinear n R →* mirabolic (n + j) R :=
  (successorIterate n j).comp levi

@[simp] theorem generalLinearToMirabolic_zero (n : ℕ) (g : GeneralLinear n R) :
    generalLinearToMirabolic n 0 g = levi g := rfl

@[simp] theorem generalLinearToMirabolic_succ (n j : ℕ) (g : GeneralLinear n R) :
    generalLinearToMirabolic n (j + 1) g =
      successor (generalLinearToMirabolic n j g) := rfl

theorem determinant_generalLinearToMirabolic (n j : ℕ) (g : GeneralLinear n R) :
    GeneralLinear.determinant (generalLinearToMirabolic n j g).val =
      GeneralLinear.determinant g := by
  exact (determinant_successorIterate n j (levi g)).trans (determinant_levi g)

/-- Appending one more identity coordinate agrees with the actual larger identity block. -/
theorem rankInclusion_succ {n : ℕ} (j : ℕ) (g : GeneralLinear n R) :
    GeneralLinear.rankInclusion 1 (GeneralLinear.rankInclusion j g) =
      GeneralLinear.rankInclusion (j + 1) g := by
  apply Units.ext
  ext a b
  change GeneralLinear.blockSum (GeneralLinear.blockSum (g, (1 : GeneralLinear j R)),
      (1 : GeneralLinear 1 R)) a b =
    GeneralLinear.blockSum (g, (1 : GeneralLinear (j + 1) R)) a b
  induction a using (Fin.addCases (m := n) (n := j + 1)) <;>
    induction b using (Fin.addCases (m := n) (n := j + 1))
  · rename_i a b
    change GeneralLinear.blockSum
        (GeneralLinear.blockSum (g, (1 : GeneralLinear j R)), (1 : GeneralLinear 1 R)) ((a.castAdd j).castAdd 1) ((b.castAdd j).castAdd 1) = _
    simp only [GeneralLinear.blockSum_apply_left]
  · rename_i a b
    refine Fin.lastCases ?_ (fun b => ?_) b
    · change GeneralLinear.blockSum
        (GeneralLinear.blockSum (g, (1 : GeneralLinear j R)), (1 : GeneralLinear 1 R)) ((a.castAdd j).castAdd 1)
        (Fin.natAdd (n + j) (0 : Fin 1)) = _
      simp only [GeneralLinear.blockSum_apply_left_right]
    · change GeneralLinear.blockSum
        (GeneralLinear.blockSum (g, (1 : GeneralLinear j R)), (1 : GeneralLinear 1 R)) ((a.castAdd j).castAdd 1)
        ((b.natAdd n).castAdd 1) = _
      simp only [GeneralLinear.blockSum_apply_left, GeneralLinear.blockSum_apply_left_right]
  · rename_i a b
    refine Fin.lastCases ?_ (fun a => ?_) a
    · change GeneralLinear.blockSum
        (GeneralLinear.blockSum (g, (1 : GeneralLinear j R)), (1 : GeneralLinear 1 R)) (Fin.natAdd (n + j) (0 : Fin 1))
        ((b.castAdd j).castAdd 1) = _
      simp only [GeneralLinear.blockSum_apply_right_left]
    · change GeneralLinear.blockSum
        (GeneralLinear.blockSum (g, (1 : GeneralLinear j R)), (1 : GeneralLinear 1 R)) ((a.natAdd n).castAdd 1)
        ((b.castAdd j).castAdd 1) = _
      simp only [GeneralLinear.blockSum_apply_left, GeneralLinear.blockSum_apply_right_left]
  · rename_i a b
    refine Fin.lastCases ?_ (fun a => ?_) a <;>
      refine Fin.lastCases ?_ (fun b => ?_) b
    · change GeneralLinear.blockSum
        (GeneralLinear.blockSum (g, (1 : GeneralLinear j R)), (1 : GeneralLinear 1 R)) (Fin.natAdd (n + j) (0 : Fin 1))
          (Fin.natAdd (n + j) (0 : Fin 1)) = _
      simp only [GeneralLinear.blockSum_apply_right, GeneralLinear.blockSum_apply_right,
        Units.val_one, Matrix.one_apply_eq]
    · change GeneralLinear.blockSum
        (GeneralLinear.blockSum (g, (1 : GeneralLinear j R)), (1 : GeneralLinear 1 R)) (Fin.natAdd (n + j) (0 : Fin 1))
          ((b.natAdd n).castAdd 1) = _
      simp only [GeneralLinear.blockSum_apply_right_left, GeneralLinear.blockSum_apply_right,
        Units.val_one, Matrix.one_apply, (Fin.castSucc_ne_last b).symm, ite_false]
    · change GeneralLinear.blockSum
        (GeneralLinear.blockSum (g, (1 : GeneralLinear j R)), (1 : GeneralLinear 1 R)) ((a.natAdd n).castAdd 1)
          (Fin.natAdd (n + j) (0 : Fin 1)) = _
      simp only [GeneralLinear.blockSum_apply_left_right, GeneralLinear.blockSum_apply_right,
        Units.val_one, Matrix.one_apply, Fin.castSucc_ne_last, ite_false]
    · change GeneralLinear.blockSum
        (GeneralLinear.blockSum (g, (1 : GeneralLinear j R)), (1 : GeneralLinear 1 R)) ((a.natAdd n).castAdd 1)
          ((b.natAdd n).castAdd 1) = _
      simp only [GeneralLinear.blockSum_apply_left, GeneralLinear.blockSum_apply_right,
        Units.val_one, Matrix.one_apply, Fin.castSucc_inj]

/-- The actual derivative acting embedding is literally `diag(g,I_(j+1))`. -/
theorem generalLinearToMirabolic_val (n j : ℕ) (g : GeneralLinear n R) :
    (generalLinearToMirabolic n j g).val = GeneralLinear.rankInclusion (j + 1) g := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change GeneralLinear.rankInclusion 1 (generalLinearToMirabolic n j g).val = _
    rw [ih]
    exact rankInclusion_succ (j + 1) g

end Matrices

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The normalized determinant is unchanged by the actual Levi embedding. -/
theorem determinantNorm_levi (T : F.TopologicalData) (n : ℕ)
    (g : GeneralLinear n F.Carrier) :
    T.determinantNorm (n + 1) (levi g).val = T.determinantNorm n g :=
  congrArg T.normalizedAbsUnits (determinant_levi g)

/-- The normalized determinant is unchanged throughout the actual successor tower. -/
theorem determinantNorm_successorIterate (T : F.TopologicalData) (n j : ℕ)
    (h : mirabolic n F.Carrier) :
    T.determinantNorm (n + j + 1) (successorIterate n j h).val =
      T.determinantNorm (n + 1) h.val :=
  congrArg T.normalizedAbsUnits (determinant_successorIterate n j h)

/-- Restricting any actual Phi normalization along all smaller successor embeddings
gives the same half-determinant character. -/
theorem phiMinusCharacter_successorIterate (T : F.TopologicalData) (n j : ℕ)
    (h : mirabolic n F.Carrier) :
    Mirabolic.phiMinusCharacter T (n + j) (successorIterate n j h) =
      Mirabolic.phiMinusCharacter T n h := by
  change positiveUnitsToComplex
      ((Units.map (NNReal.rpowMonoidHom (-(1 / 2 : ℝ))))
        (T.determinantNorm (n + j + 1) (successorIterate n j h).val)) = _
  rw [determinantNorm_successorIterate]
  rfl

/-- The actual Levi pullback of the Phi normalization is the Psi normalization. -/
theorem phiMinusCharacter_levi (T : F.TopologicalData) (n : ℕ)
    (g : GeneralLinear n F.Carrier) :
    Mirabolic.phiMinusCharacter T n (levi g) = Mirabolic.psiMinusCharacter T n g := by
  change positiveUnitsToComplex
      ((Units.map (NNReal.rpowMonoidHom (-(1 / 2 : ℝ))))
        (T.determinantNorm (n + 1) (levi g).val)) = _
  rw [determinantNorm_levi]
  rfl

/-- The library real inverse half is exactly its canonical positive inverse square root. -/
theorem psiMinusCharacter_eq_inverseHalf (T : F.TopologicalData) (n : ℕ) :
    Mirabolic.psiMinusCharacter T n = Jacquet.inverseHalfCharacter (T.determinantNorm n) := by
  ext g
  simp only [Mirabolic.psiMinusCharacter, coe_realPowerCharacter,
    Jacquet.inverseHalfCharacter_apply, Real.coe_sqrt, Real.sqrt_eq_rpow,
    Real.rpow_neg (NNReal.coe_nonneg _), Complex.ofReal_inv]

/-- Restrict the full two-block modulus along the actual inverse Levi equivalence. -/
theorem leviModulus_first (T : F.TopologicalData) (k m : ℕ) (hk : 0 < k) (hm : 0 < m)
    (g : GeneralLinear k F.Carrier) :
    T.leviModulus (Shahidi.twoBlocks k m hk hm)
        ((Shahidi.twoBlockLeviEquiv hk hm F.Carrier).symm (g, 1)) =
      T.determinantNorm k g ^ m := by
  rw [T.leviModulus_twoBlocks hk hm]
  simp

/-- The inverse-half Jacquet scalar on the first factor is exactly `m` actual Psi halves. -/
theorem inverseHalf_leviModulus_first (T : F.TopologicalData) (k m : ℕ)
    (hk : 0 < k) (hm : 0 < m) (g : GeneralLinear k F.Carrier) :
    Jacquet.inverseHalfCharacter (T.leviModulus (Shahidi.twoBlocks k m hk hm))
        ((Shahidi.twoBlockLeviEquiv hk hm F.Carrier).symm (g, 1)) =
      Mirabolic.psiMinusCharacter T k g ^ m := by
  rw [psiMinusCharacter_eq_inverseHalf]
  apply Units.ext
  simp only [Jacquet.inverseHalfCharacter_apply, leviModulus_first,
    Units.val_pow_eq_pow_val]
  change (((NNReal.sqrtHom ((T.determinantNorm k g : ℝ≥0) ^ m) : ℝ) : ℂ))⁻¹ = _
  rw [map_pow]
  simp only [NNReal.coe_pow, Complex.ofReal_pow, inv_pow]
  rfl

/-! ## Quotient maps of the existing iterates -/

/-- The existing Phi quotient map, typed with the actual normalized output object. -/
def phiStepMk (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    (A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier)) →
      A →ₗ[ℂ] (Mirabolic.phiMinus T ψ n).obj A := by
  let := T.topology
  intro A
  exact Mirabolic.phiMinusQuotient T ψ n A

theorem phiStepMk_surjective (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier),
      Function.Surjective (phiStepMk T ψ n A) := by
  let := T.topology
  intro A
  exact Mirabolic.phiMinusQuotient_surjective T ψ n A

theorem phiStepMk_natural (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier)}
      (f : A ⟶ B) (v : A),
      SmoothRep.hom ((Mirabolic.phiMinus T ψ n).map f) (phiStepMk T ψ n A v) =
        phiStepMk T ψ n B (SmoothRep.hom f v) := by
  intros
  rfl

theorem phiStep_action_mk (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier))
      (h : mirabolic n F.Carrier) (v : A),
      ((Mirabolic.phiMinus T ψ n).obj A).representation h (phiStepMk T ψ n A v) =
        (Mirabolic.phiMinusCharacter T n h : ℂ) •
          phiStepMk T ψ n A (A.representation (successor h) v) := by
  intros
  rfl

/-- Compose the actual quotient maps, without replacing the published iterate. -/
def phiIterateMk (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    (j : ℕ) →
      letI := T.topology
      (A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + j) F.Carrier)) →
        A →ₗ[ℂ] (phiMinusIterate T ψ n j).obj A
  | 0 => letI := T.topology; fun _ => LinearMap.id
  | j + 1 => letI := T.topology; fun A =>
      (phiIterateMk T ψ n j ((Mirabolic.phiMinus T ψ (n + j)).obj A)).comp
        (phiStepMk T ψ (n + j) A)

theorem phiIterateMk_zero (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) (v : A),
      phiIterateMk T ψ n 0 A v = v := by
  intros
  rfl

theorem phiIterateMk_succ (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n j : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + j + 1) F.Carrier)) (v : A),
      phiIterateMk T ψ n (j + 1) A v =
        phiIterateMk T ψ n j ((Mirabolic.phiMinus T ψ (n + j)).obj A)
          (phiStepMk T ψ (n + j) A v) := by
  intros
  rfl

theorem phiIterateMk_surjective (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n j : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + j) F.Carrier),
      Function.Surjective (phiIterateMk T ψ n j A) := by
  let := T.topology
  induction j with
  | zero => intro A v; exact ⟨v, rfl⟩
  | succ j ih =>
    intro A
    exact (ih ((Mirabolic.phiMinus T ψ (n + j)).obj A)).comp
      (phiStepMk_surjective T ψ (n + j) A)

/-- Every actual mapped intertwiner commutes with the composite quotient map. -/
theorem phiIterateMk_natural (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n j : ℕ) :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + j) F.Carrier)}
      (f : A ⟶ B) (v : A),
      SmoothRep.hom ((phiMinusIterate T ψ n j).map f) (phiIterateMk T ψ n j A v) =
        phiIterateMk T ψ n j B (SmoothRep.hom f v) := by
  let := T.topology
  induction j with
  | zero => intros; rfl
  | succ j ih =>
    intro A B f v
    change SmoothRep.hom ((phiMinusIterate T ψ n j).map
        ((Mirabolic.phiMinus T ψ (n + j)).map f))
        (phiIterateMk T ψ n j ((Mirabolic.phiMinus T ψ (n + j)).obj A)
          (phiStepMk T ψ (n + j) A v)) = _
    rw [ih, phiStepMk_natural]
    rfl

/-- Each actual Phi step contributes one equal half-determinant factor on the
smaller acting mirabolic group. -/
theorem phiIterate_action_mk (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n j : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + j) F.Carrier))
      (h : mirabolic n F.Carrier) (v : A),
      ((phiMinusIterate T ψ n j).obj A).representation h (phiIterateMk T ψ n j A v) =
        (Mirabolic.phiMinusCharacter T n h : ℂ) ^ j •
          phiIterateMk T ψ n j A (A.representation (successorIterate n j h) v) := by
  let := T.topology
  induction j with
  | zero =>
    intro A h v
    change A.representation h v = (1 : ℂ) • A.representation h v
    rw [one_smul]
  | succ j ih =>
    intro A h v
    change ((phiMinusIterate T ψ n j).obj
        ((Mirabolic.phiMinus T ψ (n + j)).obj A)).representation h
        (phiIterateMk T ψ n j ((Mirabolic.phiMinus T ψ (n + j)).obj A)
          (phiStepMk T ψ (n + j) A v)) = _
    rw [ih, phiStep_action_mk]
    change (Mirabolic.phiMinusCharacter T n h : ℂ) ^ j •
        phiIterateMk T ψ n j ((Mirabolic.phiMinus T ψ (n + j)).obj A)
          ((Mirabolic.phiMinusCharacter T (n + j) (successorIterate n j h) : ℂ) •
            phiStepMk T ψ (n + j) A
              (A.representation (successor (successorIterate n j h)) v)) = _
    rw [phiMinusCharacter_successorIterate, map_smul, smul_smul, ← pow_succ]
    rfl

/-- The actual quotient map of the derivative with `j` Phi steps and one Psi step. -/
def mirabolicDerivativeMk (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n j : ℕ) :
    letI := T.topology
    (A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + j) F.Carrier)) →
      A →ₗ[ℂ] (mirabolicDerivative T ψ n j).obj A := by
  let := T.topology
  intro A
  exact (Mirabolic.psiMinusQuotient T n ((phiMinusIterate T ψ n j).obj A)).comp
    (phiIterateMk T ψ n j A)

theorem mirabolicDerivativeMk_surjective (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n j : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + j) F.Carrier),
      Function.Surjective (mirabolicDerivativeMk T ψ n j A) := by
  let := T.topology
  intro A
  exact (Mirabolic.psiMinusQuotient_surjective T n ((phiMinusIterate T ψ n j).obj A)).comp
    (phiIterateMk_surjective T ψ n j A)

theorem mirabolicDerivativeMk_natural (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n j : ℕ) :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + j) F.Carrier)}
      (f : A ⟶ B) (v : A),
      SmoothRep.hom ((mirabolicDerivative T ψ n j).map f)
          (mirabolicDerivativeMk T ψ n j A v) =
        mirabolicDerivativeMk T ψ n j B (SmoothRep.hom f v) := by
  let := T.topology
  intro A B f v
  change SmoothRep.hom ((Mirabolic.psiMinus T n).map ((phiMinusIterate T ψ n j).map f))
      (Mirabolic.psiMinusQuotient T n ((phiMinusIterate T ψ n j).obj A)
        (phiIterateMk T ψ n j A v)) = _
  rw [Mirabolic.psiMinus_map_quotient, phiIterateMk_natural]
  rfl

/-- The actual normalized derivative action contributes all `j+1` half determinants. -/
theorem mirabolicDerivative_action_mk (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n j : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + j) F.Carrier))
      (g : GeneralLinear n F.Carrier) (v : A),
      ((mirabolicDerivative T ψ n j).obj A).representation g
          (mirabolicDerivativeMk T ψ n j A v) =
        (Mirabolic.psiMinusCharacter T n g : ℂ) ^ (j + 1) •
          mirabolicDerivativeMk T ψ n j A
            (A.representation (generalLinearToMirabolic n j g) v) := by
  let := T.topology
  intro A g v
  change ((Mirabolic.psiMinus T n).obj ((phiMinusIterate T ψ n j).obj A)).representation g
      (Mirabolic.psiMinusQuotient T n ((phiMinusIterate T ψ n j).obj A)
        (phiIterateMk T ψ n j A v)) = _
  rw [Mirabolic.psiMinus_action, phiIterate_action_mk]
  change (Mirabolic.psiMinusCharacter T n g : ℂ) •
      Mirabolic.psiMinusQuotient T n ((phiMinusIterate T ψ n j).obj A)
        ((Mirabolic.phiMinusCharacter T n (levi g) : ℂ) ^ j •
          phiIterateMk T ψ n j A
            (A.representation (successorIterate n j (levi g)) v)) = _
  rw [phiMinusCharacter_levi, map_smul, smul_smul, ← pow_succ']
  rfl

/-- The existing positive GL derivative's quotient map, after actual mirabolic restriction. -/
def generalLinearDerivativePositiveMk (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n j : ℕ) :
    letI := T.topology
    (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + j + 1) F.Carrier)) →
      A →ₗ[ℂ] (generalLinearDerivativePositive T ψ n j).obj A := by
  let := T.topology
  intro A
  exact mirabolicDerivativeMk T ψ n j ((generalLinearRestriction T (n + j)).obj A)

theorem generalLinearDerivativePositiveMk_surjective (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n j : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + j + 1) F.Carrier),
      Function.Surjective (generalLinearDerivativePositiveMk T ψ n j A) := by
  let := T.topology
  intro A
  exact mirabolicDerivativeMk_surjective T ψ n j ((generalLinearRestriction T (n + j)).obj A)

theorem generalLinearDerivativePositiveMk_natural (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n j : ℕ) :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + j + 1) F.Carrier)}
      (f : A ⟶ B) (v : A),
      SmoothRep.hom ((generalLinearDerivativePositive T ψ n j).map f)
          (generalLinearDerivativePositiveMk T ψ n j A v) =
        generalLinearDerivativePositiveMk T ψ n j B (SmoothRep.hom f v) := by
  let := T.topology
  intro A B f v
  exact mirabolicDerivativeMk_natural T ψ n j
    ((generalLinearRestriction T (n + j)).map f) v

/-- The existing positive GL derivative retains exactly all `j+1` determinant halves. -/
theorem generalLinearDerivativePositive_action_mk (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n j : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + j + 1) F.Carrier))
      (g : GeneralLinear n F.Carrier) (v : A),
      ((generalLinearDerivativePositive T ψ n j).obj A).representation g
          (generalLinearDerivativePositiveMk T ψ n j A v) =
        (Mirabolic.psiMinusCharacter T n g : ℂ) ^ (j + 1) •
          generalLinearDerivativePositiveMk T ψ n j A
            (A.representation (GeneralLinear.rankInclusion (j + 1) g) v) := by
  let := T.topology
  intro A g v
  have h := mirabolicDerivative_action_mk T ψ n j
    ((generalLinearRestriction T (n + j)).obj A) g v
  change ((generalLinearDerivativePositive T ψ n j).obj A).representation g
      (generalLinearDerivativePositiveMk T ψ n j A v) =
    (Mirabolic.psiMinusCharacter T n g : ℂ) ^ (j + 1) •
      generalLinearDerivativePositiveMk T ψ n j A
        (A.representation (generalLinearToMirabolic n j g).val v) at h
  simpa only [generalLinearToMirabolic_val] using h

/-- For positive first rank, the scalar of the actual positive derivative is
exactly the inverse-half Jacquet scalar through the actual continuous Levi equivalence. -/
theorem generalLinearDerivativePositive_action_mk_eq_inverseHalf
    (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k j : ℕ) (hk : 0 < k) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + j + 1) F.Carrier))
      (g : GeneralLinear k F.Carrier) (v : A),
      ((generalLinearDerivativePositive T ψ k j).obj A).representation g
          (generalLinearDerivativePositiveMk T ψ k j A v) =
        (Jacquet.inverseHalfCharacter (T.leviModulus
            (Shahidi.twoBlocks k (j + 1) hk (Nat.succ_pos j)))
          ((Shahidi.twoBlockLeviContinuousEquiv hk (Nat.succ_pos j) F.Carrier).symm
            (g, 1)) : ℂ) •
          generalLinearDerivativePositiveMk T ψ k j A
            (A.representation (GeneralLinear.rankInclusion (j + 1) g) v) := by
  let := T.topology
  intro A g v
  rw [generalLinearDerivativePositive_action_mk]
  have hc := congrArg (fun c : ℂˣ => (c : ℂ))
    (inverseHalf_leviModulus_first T k (j + 1) hk (Nat.succ_pos j) g)
  change (Jacquet.inverseHalfCharacter (T.leviModulus
      (Shahidi.twoBlocks k (j + 1) hk (Nat.succ_pos j)))
      ((Shahidi.twoBlockLeviContinuousEquiv hk (Nat.succ_pos j) F.Carrier).symm
        (g, 1)) : ℂ) = (Mirabolic.psiMinusCharacter T k g : ℂ) ^ (j + 1) at hc
  rw [hc]

end Langlands.Derivative.JacquetNormalization
