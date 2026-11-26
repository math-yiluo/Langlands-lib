import Langlands.Algebra.BrauerGroup
import Langlands.Algebra.CentralSimple.MatrixSemilinearInvolution
import Langlands.Algebra.UnitaryInvolutionStatements
import Mathlib.Data.Matrix.Composition

/-! # The involution on the tensor with a conjugate opposite -/

noncomputable section

universe u v

namespace Langlands.Algebra.CentralSimple

open scoped TensorProduct

variable {K : Type u} [Field K] (c : K ≃+* K)

/-- A ring with its scalar inclusion composed with the specified field automorphism. -/
@[nolint unusedArguments]
def ScalarConjugate (_c : K ≃+* K) (A : Type v) : Type v := A

namespace ScalarConjugate

variable (A : Type v) [Ring A] [Algebra K A]

instance : Ring (ScalarConjugate c A) := inferInstanceAs (Ring A)

instance : Algebra K (ScalarConjugate c A) := Algebra.compHom A c.toRingHom

/-- Forget the scalar twist as a ring equivalence. -/
def toRing : ScalarConjugate c A ≃+* A := RingEquiv.refl A

@[simp] theorem toRing_algebraMap (r : K) :
    toRing c A (algebraMap K (ScalarConjugate c A) r) = algebraMap K A (c r) := rfl

@[simp] theorem toRing_smul (r : K) (a : ScalarConjugate c A) :
    toRing c A (r • a) = c r • toRing c A a := rfl

private def toSemilinear : ScalarConjugate c A →ₛₗ[c.toRingHom] A where
  toFun := toRing c A
  map_add' := map_add (toRing c A)
  map_smul' := toRing_smul c A

instance [FiniteDimensional K A] : FiniteDimensional K (ScalarConjugate c A) := by
  let : RingHomSurjective c.toRingHom := ⟨c.surjective⟩
  exact (LinearMap.finite_iff_of_bijective (toSemilinear c A)
    (toRing c A).bijective).mpr inferInstance

instance [IsSimpleRing A] : IsSimpleRing (ScalarConjugate c A) :=
  inferInstanceAs (IsSimpleRing A)

instance [Algebra.IsCentral K A] : Algebra.IsCentral K (ScalarConjugate c A) where
  out a ha := by
    have h : toRing c A a ∈ Subalgebra.center K A := by
      rw [Subalgebra.mem_center_iff] at ha ⊢
      intro b
      exact congrArg (toRing c A) (ha ((toRing c A).symm b))
    obtain ⟨r, hr⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out h)
    exact Algebra.mem_bot.mpr ⟨c.symm r, (toRing c A).injective (by simpa using hr)⟩

/-- The scalar conjugate of a central simple algebra. -/
def csa (B : CSA.{u, v} K) : CSA.{u, v} K where
  toAlgCat := AlgCat.of K (ScalarConjugate c B)

end ScalarConjugate

section Flip

variable (A : Type v) [Ring A] [Algebra K A]

local notation "B" => ScalarConjugate c Aᵐᵒᵖ
local notation "T" => A ⊗[K] B

private def leftToRight : A ≃+ B :=
  MulOpposite.opAddEquiv.trans (ScalarConjugate.toRing c Aᵐᵒᵖ).symm.toAddEquiv

private def rightToLeft : B ≃+ A := (leftToRight c A).symm

private theorem rightToLeft_smul (r : K) (b : B) :
    rightToLeft c A (r • b) = c r • rightToLeft c A b := rfl

private theorem leftToRight_smul (r : K) (a : A) :
    leftToRight c A (r • a) = c.symm r • leftToRight c A a := by
  change _ = leftToRight c A (c (c.symm r) • a)
  rw [c.apply_symm_apply]

private def flipPairing : A →+ B →+ T where
  toFun a :=
    { toFun b := rightToLeft c A b ⊗ₜ[K] leftToRight c A a
      map_zero' := by simp
      map_add' b b' := by simp [TensorProduct.add_tmul] }
  map_zero' := by ext; simp
  map_add' a a' := by ext; simp [TensorProduct.tmul_add]

variable (hc : Function.Involutive c)

/-- Exchange the tensor factors, using the two additive maps to or from the
conjugate opposite. The exchange is semilinear for the specified involutive
scalar automorphism `c`. -/
def conjugateOppositeFlip : T →+ T :=
  TensorProduct.liftAddHom (flipPairing c A) (by
    intro r a b
    change rightToLeft c A b ⊗ₜ[K] leftToRight c A (r • a) =
      rightToLeft c A (r • b) ⊗ₜ[K] leftToRight c A a
    have hrs : c.symm r = c r := c.symm_apply_eq.mpr (hc r).symm
    rw [leftToRight_smul, rightToLeft_smul, hrs, TensorProduct.tmul_smul, TensorProduct.smul_tmul'])

@[simp] theorem conjugateOppositeFlip_tmul (a : A) (b : B) :
    conjugateOppositeFlip c A hc (a ⊗ₜ[K] b) =
      rightToLeft c A b ⊗ₜ[K] leftToRight c A a := rfl

omit [Algebra K A] in
private theorem rightToLeft_mul (b b' : B) :
    rightToLeft c A (b * b') = rightToLeft c A b' * rightToLeft c A b := rfl

omit [Algebra K A] in
private theorem leftToRight_mul (a a' : A) :
    leftToRight c A (a * a') = leftToRight c A a' * leftToRight c A a := rfl

theorem isUnitaryInvolution_conjugateOppositeFlip :
    IsUnitaryInvolution c (conjugateOppositeFlip c A hc) := by
  let F := conjugateOppositeFlip c A hc
  refine ⟨F.map_add, ?_, ?_, ?_⟩
  · intro x y
    induction x using TensorProduct.inductionOn with
    | add a b ha hb => simp only [add_mul, map_add, ha, hb, mul_add]
    | tmul a b =>
      induction y using TensorProduct.inductionOn with
      | add d e hd he => simp only [mul_add, map_add, hd, he, add_mul]
      | tmul d e =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, conjugateOppositeFlip_tmul,
          rightToLeft_mul, leftToRight_mul]
  · intro x
    induction x using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a b =>
      rw [conjugateOppositeFlip_tmul, conjugateOppositeFlip_tmul]
      exact congrArg₂ (fun a b => a ⊗ₜ[K] b) ((leftToRight c A).symm_apply_apply a)
        ((leftToRight c A).apply_symm_apply b)
  · intro r
    rw [Algebra.TensorProduct.algebraMap_apply, conjugateOppositeFlip_tmul]
    have h₁ : rightToLeft c A (1 : B) = 1 := rfl
    have h₂ : leftToRight c A (algebraMap K A r) = algebraMap K B (c r) := by
      apply (ScalarConjugate.toRing c Aᵐᵒᵖ).injective
      rw [ScalarConjugate.toRing_algebraMap, hc]
      rfl
    rw [h₁, h₂, Algebra.TensorProduct.algebraMap_apply']

end Flip

section MatrixTransfer

variable {D : Type v} [Ring D] [Algebra K D]

private theorem isUnitaryInvolution_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    {τ : D → D} (hτ : IsUnitaryInvolution c τ) :
    IsUnitaryInvolution c (fun M : Matrix ι ι D => fun i j => τ (M j i)) := by
  have h0 : τ 0 = 0 := by simpa only [map_zero] using hτ.2.2.2 0
  let addτ : D →+ D := { toFun := τ, map_zero' := h0, map_add' := hτ.1 }
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X Y
    ext i j
    exact hτ.1 _ _
  · intro X Y
    ext i j
    change addτ (∑ k, X j k * Y k i) = ∑ k, τ (Y k i) * τ (X j k)
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => hτ.2.1 _ _
  · intro X
    ext i j
    exact hτ.2.2.1 _
  · intro r
    ext i j
    simp only [Matrix.algebraMap_matrix_apply]
    by_cases hij : i = j
    · subst j
      simpa using hτ.2.2.2 r
    · simp [hij, Ne.symm hij, h0]

private theorem isUnitaryInvolution_transport {A : Type*} [Ring A] [Algebra K A]
    {τ : D → D} (hτ : IsUnitaryInvolution c τ) (e : D ≃ₐ[K] A) :
    IsUnitaryInvolution c (fun a => e (τ (e.symm a))) := by
  exact
    ⟨fun a b => by simp only [map_add, hτ.1],
      fun a b => by simp only [map_mul, hτ.2.1],
      fun a => by simp only [e.symm_apply_apply, hτ.2.2.1, e.apply_symm_apply],
      fun r => by simp only [AlgEquiv.commutes, hτ.2.2.2]⟩

/-- The existence of a unitary involution for a nontrivial center automorphism
passes to every matrix-stably equivalent central simple algebra. -/
theorem exists_unitaryInvolution_of_brauerEquivalent (hc : ∃ r, c r ≠ r)
    {A B : CSA.{u, v} K} (h : IsBrauerEquivalent A B)
    (τ : A → A) (hτ : IsUnitaryInvolution c τ) :
    ∃ ρ : B → B, IsUnitaryInvolution c ρ := by
  classical
  obtain ⟨m, n, hm, hn, ⟨e⟩⟩ := h
  let : IsArtinianRing B := IsArtinianRing.of_finite K B
  obtain ⟨r, hr, D, _, _, _, ⟨f⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite K B
  let : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  let : Nonempty (Fin r) := ⟨⟨0, Nat.pos_of_ne_zero hr.ne⟩⟩
  let g := f.mapMatrix.trans (Matrix.compAlgEquiv (Fin n) (Fin r) D K)
  let τm (M : Matrix (Fin m) (Fin m) A) : Matrix (Fin m) (Fin m) A :=
    fun i j => τ (M j i)
  have hτm : IsUnitaryInvolution c τm := isUnitaryInvolution_matrix c hτ
  have h' := isUnitaryInvolution_transport c hτm e
  obtain ⟨ρ, hρ⟩ :=
    exists_semilinear_involution_of_algEquiv_matrix g c.toRingHom hc
      (fun a => e (τm (e.symm a))) h'.1 h'.2.1 h'.2.2.1 (fun r => h'.2.2.2 r)
  have hρ' : IsUnitaryInvolution c ρ := hρ
  have hρm : IsUnitaryInvolution c
      (fun M : Matrix (Fin r) (Fin r) D => fun i j => ρ (M j i)) :=
    isUnitaryInvolution_matrix c hρ'
  exact ⟨_, isUnitaryInvolution_transport c hρm f.symm⟩

end MatrixTransfer

end Langlands.Algebra.CentralSimple
