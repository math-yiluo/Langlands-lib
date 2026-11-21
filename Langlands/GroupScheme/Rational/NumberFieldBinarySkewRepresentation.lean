import Langlands.GroupScheme.Rational.NumberFieldRankThreeSkewIsotropy
import Langlands.GroupScheme.Quaternionic.SkewHermitianAdjoinLine

/-! # Representation of pure quaternions by binary skew-hermitian forms -/

noncomputable section

universe u v

open Matrix
open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

namespace AntihermitianForm

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D] [Invertible (2 : F)]
  {τ : FirstKindInvolution F D} {V : Type v} [AddCommGroup V] [Module F V]
  [Module D V] [IsScalarTower F D V] (B : AntihermitianForm τ V)

/-- A separating skew-hermitian form with a nonzero isotropic vector represents
  every skew scalar. -/
theorem represents_of_isotropic (hB : B.toBilin.SeparatingLeft) {x : V} (hx : x ≠ 0)
    (hxx : B x x = 0) (c : D) (hc : τ c = -c) : ∃ z, B z z = c := by
  obtain ⟨y, hxy, hyy⟩ := B.exists_hyperbolicPartner hB hx hxx
  let a := (⅟ (2 : F)) • c
  have ha : τ a = -a := by
    change τ ((⅟ (2 : F)) • c) = -((⅟ (2 : F)) • c)
    rw [τ.map_smul, hc, smul_neg]
  have hyx : B y x = -1 := by rw [B.skew x y, hxy, τ.map_one]
  refine ⟨y + a • x, ?_⟩
  simp only [B.add_left, B.add_right, B.smul_left, B.smul_right, hxx, hxy, hyx, hyy,
    mul_zero, zero_mul, zero_add, add_zero, mul_one, neg_one_mul, ha, neg_neg]
  exact invOf_two_smul_add_invOf_two_smul F c

end AntihermitianForm

namespace FirstKindInvolution

open FiniteAlgebraUnits.MatrixPoints

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D]
  {n : ℕ} (τ : FirstKindInvolution F D)

/-- The prescribed pure value is represented over every completion in actual
  scalar-extended Gram coordinates. -/
def IsLocallyRepresented [NumberField F] (H : Matrix (Fin n) (Fin n) D) (c : D) : Prop :=
  ∀ v : Global.Place F, let R := Global.placeCompletion F v
    let M := coefficientEquiv F D R ((1 : R) ⊗ₜ[F] H)
    ∃ x : Fin n → R ⊗[F] D,
      (τ.baseChange R).matrixSesqBilin M x x = (1 : R) ⊗ₜ[F] c

private theorem exists_isotropic_adjoin_neg_over (R : Type u) [Field R] [Algebra F R]
    {H : Matrix (Fin n) (Fin n) D} {c : D} (x : Fin n → R ⊗[F] D)
    (hx : (τ.baseChange R).matrixSesqBilin (coefficientEquiv F D R ((1 : R) ⊗ₜ[F] H)) x x =
      (1 : R) ⊗ₜ[F] c) :
    ∃ (z : Fin (n + 1) → R ⊗[F] D) (i : Fin (n + 1)), IsUnit (z i) ∧
      (τ.baseChange R).matrixSesqBilin
        (coefficientEquiv F D R ((1 : R) ⊗ₜ[F] adjoinSkewLine H (-c))) z z = 0 := by
  let g : D →ₐ[F] R ⊗[F] D := Algebra.TensorProduct.includeRight
  let z : Fin (n + 1) → R ⊗[F] D := Fin.lastCases 1 x
  have hz : z (Fin.last n) = 1 := by simp [z]
  refine ⟨z, Fin.last n, by rw [hz]; exact isUnit_one, ?_⟩
  have hcoeff {m : Type} [Fintype m] [DecidableEq m] (J : Matrix m m D) :
      coefficientEquiv F D R ((1 : R) ⊗ₜ[F] J) = J.map g.toRingHom := by
    ext i j
    rw [coefficientEquiv_tmul, Matrix.map_apply]
    rfl
  change (τ.baseChange R).matrixSesqBilin (coefficientEquiv F D R ((1 : R) ⊗ₜ[F] adjoinSkewLine H (-c))) z z = 0
  rw [hcoeff, map_adjoinSkewLine g.toRingHom, (τ.baseChange R).matrixSesqBilin_adjoinSkewLine]
  have hin : z ∘ Fin.castSucc = x := by funext i; simp [z]
  rw [hin, hz, (τ.baseChange R).map_one, one_mul, mul_one, _root_.map_neg g.toRingHom, ← hcoeff H]
  rw [hx]
  exact add_neg_cancel (g c)

/-- Local representation gives a nonsingular local zero after adjoining the
  negative line. The added coordinate is one. -/
theorem isLocallyNonsingularIsotropic_adjoin_neg [NumberField F]
    {H : Matrix (Fin n) (Fin n) D} {c : D} (hl : τ.IsLocallyRepresented H c) :
    τ.IsLocallyNonsingularIsotropic (adjoinSkewLine H (-c)) := by
  intro v
  rcases v with v | v
  · obtain ⟨x, hx⟩ := hl (.inl v)
    exact τ.exists_isotropic_adjoin_neg_over v.Completion x hx
  · obtain ⟨x, hx⟩ := hl (.inr v)
    exact τ.exists_isotropic_adjoin_neg_over (Global.FiniteCompletion F v) x hx

/-- A global zero of the appended form gives the prescribed value on the old
  form. If the last coordinate vanishes, the old form contains a skew hyperbolic pair. -/
theorem represents_of_adjoin_neg_isotropic [Invertible (2 : F)]
    {H : Matrix (Fin n) (Fin n) D} (hH : τ.IsAntihermitian H) (hu : IsUnit H)
    (c : D) (hc : c ∈ τ.alternatingSubspace) {y : Fin (n + 1) → D} (hy : y ≠ 0)
    (hyval : τ.sesqForm (adjoinSkewLine H (-c)) y y = 0) :
    ∃ x, τ.sesqForm H x x = c := by
  let B := AntihermitianForm.ofMatrix hH
  let x : Fin n → D := y ∘ Fin.castSucc
  let s := y (Fin.last n)
  have heq : B x x = s * c * τ s := by
    have h := (τ.matrixSesqBilin_adjoinSkewLine H (-c) y y).symm
    rw [matrixSesqBilin_eq_sesqForm, matrixSesqBilin_eq_sesqForm, hyval, mul_neg, neg_mul,
      ← sub_eq_add_neg] at h
    exact sub_eq_zero.mp h
  by_cases hs : s = 0
  · have hx0 : x ≠ 0 := by
      intro h
      apply hy
      funext i
      exact Fin.lastCases hs (fun j => congrFun h j) i
    have hxx : B x x = 0 := by rw [heq, hs, zero_mul, zero_mul]
    have hneg : τ c = -c := by
      obtain ⟨a, rfl⟩ := τ.mem_alternatingSubspace.mp hc
      rw [τ.map_sub, τ.apply_apply, neg_sub]
    exact B.represents_of_isotropic (AntihermitianForm.ofMatrix_separatingLeft hH hu) hx0 hxx c hneg
  · refine ⟨s⁻¹ • x, ?_⟩
    have hτ : τ s * τ s⁻¹ = 1 := by rw [← τ.map_mul, inv_mul_cancel₀ hs, τ.map_one]
    change B (s⁻¹ • x) (s⁻¹ • x) = c
    rw [B.smul_right, B.smul_left, heq]
    calc
      s⁻¹ * (s * c * τ s) * τ s⁻¹ = (s⁻¹ * s) * c * (τ s * τ s⁻¹) := by simp only [mul_assoc]
      _ = c := by rw [inv_mul_cancel₀ hs, hτ, one_mul, mul_one]

end FirstKindInvolution

/-- A nonzero pure quaternion represented locally by a nonsingular binary
  skew-hermitian form over a number field is represented globally. -/
def NumberFieldBinarySkewRepresentationStatement : Prop :=
  ∀ (F D : Type u) [Field F] [NumberField F] [DivisionRing D] [Algebra F D]
    [FiniteDimensional F D] [Algebra.IsCentral F D] (σ : FirstKindInvolution F D)
    (hdim : Module.finrank F D = 4) (hsym : Module.finrank F σ.symmetricSubspace = 3),
    let τ := σ.quaternionConjugation hdim hsym
    ∀ (H : Matrix (Fin 2) (Fin 2) D) (_ : τ.IsAntihermitian H), IsUnit H →
    ∀ c : D, c ∈ τ.alternatingSubspace → c ≠ 0 → τ.IsLocallyRepresented H c →
    ∃ x, τ.sesqForm H x x = c

/-- Apply rank-three skew isotropy to the binary form plus the negative line. -/
theorem numberFieldBinarySkewRepresentation : NumberFieldBinarySkewRepresentationStatement.{u} := by
  intro F D _ _ _ _ _ _ σ hdim hsym τ H hH hu c hc hc0 hl
  let : Invertible (2 : F) := invertibleOfNonzero (two_ne_zero : (2 : F) ≠ 0)
  let H' := adjoinSkewLine H (-c)
  have hH' : τ.IsAntihermitian H' := hH.adjoinSkewLine (τ.alternatingSubspace.neg_mem hc)
  have hu' : IsUnit H' := adjoinSkewLine_isUnit hu (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr hc0))
  obtain ⟨y, hy, hyval⟩ := numberFieldRankThreeSkewIsotropy F D σ hdim hsym H' hH' hu'
    (τ.isLocallyNonsingularIsotropic_adjoin_neg hl)
  exact τ.represents_of_adjoin_neg_isotropic hH hu c hc hy hyval

end Langlands.GroupScheme.Quaternionic
