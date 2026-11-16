import Langlands.Representation.Archimedean.RealSwapFLanding
import Langlands.Representation.Archimedean.RealKTypeTransport
import Langlands.Representation.Archimedean.RealJacquetFrobeniusProof

/-!
# The mirror of the landing statements on `GL_3(ℝ)`

Let `κ₀` be the orthogonal matrix `diag(1, -1, 1) · J` (`J` the antidiagonal permutation), so
`κ₀ e₀ = e₂`, `κ₀ e₁ = -e₁`, `κ₀ e₂ = e₀`. It is an involution with determinant `1`, and it
exchanges the two block rotations of `GL_3(ℝ)` with the same angle:
`κ₀ r_0(θ) = r_1(θ) κ₀` and `κ₀ r_1(θ) = r_0(θ) κ₀`.

For `e = ℓ + 1` (`ℓ = |m|` the weight of the induction block), the mirror
`φ ↦ (x ↦ φ(κ₀ x) sgnDet(κ₀ x)^e)` exchanges the left Fourier coefficients along `r_0` and
`r_1`. Restricted to `O(3)` and extended back as a principal series function, it carries the
`O(3)`-finite functions of the standard module of `[c, d]` to those of `[d, c']`, where `c'` is
the real character data of parity `(ℓ + 1 + ε₁) mod 2` (`ε₁` the parity of `c`) and exponent
`0`. Applying `RealSwapLandingInducedFirstStatement` to `c'`, `d` and the mirrored functions
gives `RealSwapLandingCharacterFirstStatement`:
`characterFirst_of_inducedFirst`.
-/

noncomputable section

open scoped Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

set_option backward.isDefEq.respectTransparency false

namespace RealSwapLandingMirror

open Langlands.LocalFactor.Archimedean RealBlockMultiplier RealSwapFLanding RealKTypeTransport
open PrincipalSeriesExtension GramFormula

/-! ## Parity classes and signs -/

/-- The recurrence only depends on the parity class. -/
theorem isRecurrent_congr {δ : ℂ} {ε ε' : ℤ} {μ : ℤ → ℂ} (h : IsRecurrent δ ε μ)
    (hε : Even (ε - ε')) : IsRecurrent δ ε' μ := fun k hk =>
  h k (by
    have : k - ε = (k - ε') - (ε - ε') := by ring
    rw [this]
    exact hk.sub hε)

/-- The symmetry only depends on the parity class. -/
theorem isSymmetric_congr {σ σ' : ℂ} {ε ε' : ℤ} {μ : ℤ → ℂ} (h : IsSymmetric ε σ μ)
    (hε : Even (ε - ε')) (hσ : σ = σ') : IsSymmetric ε' σ' μ := fun k hk => by
  rw [← hσ]
  exact h k (by
    have : k - ε = (k - ε') - (ε - ε') := by ring
    rw [this]
    exact hk.sub hε)

theorem neg_one_pow_congr {m n : ℕ} (h : m % 2 = n % 2) : (-1 : ℂ) ^ m = (-1) ^ n := by
  rw [neg_one_pow_eq_pow_mod_two, h]
  exact (neg_one_pow_eq_pow_mod_two n).symm

theorem even_sub_mod (n : ℕ) : Even ((n : ℤ) - ((n % 2 : ℕ) : ℤ)) :=
  Int.even_iff.mpr (by omega)

theorem even_sub_mod' (l ε : ℕ) : Even ((ε : ℤ) - ((l + 1 + (l + 1 + ε) % 2 : ℕ) : ℤ)) :=
  Int.even_iff.mpr (by omega)

theorem pow_mod_two {x : ℂ} (hx : x ^ 2 = 1) (k : ℕ) : x ^ (k % 2) = x ^ k := by
  conv_rhs => rw [← Nat.mod_add_div k 2, pow_add, pow_mul, hx, one_pow, mul_one]

theorem sq_signReal (r : ℝ) : ((signReal r : ℝ) : ℂ) ^ 2 = 1 := by
  unfold signReal
  split_ifs <;> norm_num

/-- A real character at a sign. -/
theorem character_signUnit (c : RealCharacterData) (x : ℝˣ) :
    (c.character (signUnit x) : ℂ) = ((signReal (x : ℝ) : ℝ) : ℂ) ^ c.parity.val := by
  rw [c.character_eq, abs_signUnit, div_one, signUnit_val]
  simp

theorem realInducedFirstCharacter_signUnit (d : ComplexCharacterData) (x : ℝˣ) :
    realInducedFirstCharacter d (signUnit x) =
      ((signReal (x : ℝ) : ℝ) : ℂ) ^ (d.weight.natAbs + 1) := by
  rw [realInducedFirstCharacter, abs_signUnit, div_one, signUnit_val]
  simp

theorem realInducedSecondCharacter_signUnit (d : ComplexCharacterData) (x : ℝˣ) :
    realInducedSecondCharacter d (signUnit x) = 1 := by
  rw [realInducedSecondCharacter, abs_signUnit]
  simp

theorem sgnDet_signDiagonal (a : Fin 3 → ℝˣ) :
    sgnDet 3 (Unitary.toUnits (signDiagonal (fun i => (a i : ℝ)))) =
      ∏ i : Fin 3, ((signReal (a i : ℝ) : ℝ) : ℂ) := by
  unfold sgnDet
  have hdet : ((Unitary.toUnits (signDiagonal (fun i => (a i : ℝ))) :
      Langlands.GeneralLinear 3 ℝ) : Matrix (Fin 3) (Fin 3) ℝ).det =
        ∏ i : Fin 3, signReal (a i : ℝ) := by
    show (Matrix.diagonal fun i => signReal (a i : ℝ)).det = _
    rw [Matrix.det_diagonal]
  rw [hdet, Finset.abs_prod]
  simp only [abs_signReal, Finset.prod_const_one, div_one, Complex.ofReal_prod]

theorem sgnDet_ne_zero (x : Langlands.GeneralLinear 3 ℝ) : sgnDet 3 x ≠ 0 := fun h0 => by
  have h := sgnDet_mul_self x
  rw [h0, zero_mul] at h
  exact zero_ne_one h

/-- The sign identity behind the mirror: with `s_i² = 1`,
`s₂^ε s₁^(ℓ+1) · 1 · (s₂ s₁ s₀)^(ℓ+1) = s₀^(ℓ+1) · 1 · s₂^((ℓ+1+ε) mod 2)`. -/
theorem sign_identity {s₀ s₁ s₂ : ℂ} (h₁ : s₁ ^ 2 = 1) (h₂ : s₂ ^ 2 = 1) (l ε : ℕ) :
    s₂ ^ ε * s₁ ^ (l + 1) * 1 * (s₂ * s₁ * s₀) ^ (l + 1) =
      s₀ ^ (l + 1) * 1 * s₂ ^ ((l + 1 + ε) % 2) := by
  calc s₂ ^ ε * s₁ ^ (l + 1) * 1 * (s₂ * s₁ * s₀) ^ (l + 1)
      = s₀ ^ (l + 1) * s₂ ^ (l + 1 + ε) * (s₁ ^ 2) ^ (l + 1) := by ring
    _ = s₀ ^ (l + 1) * 1 * s₂ ^ ((l + 1 + ε) % 2) := by
      rw [h₁, one_pow, pow_mod_two h₂]
      ring

/-! ## The mirror matrix -/

/-- The matrix `κ₀ = diag(1, -1, 1) · J`. -/
def mirrorMatrix : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 1; 0, -1, 0; 1, 0, 0]

theorem mirrorMatrix_mem : mirrorMatrix ∈ Matrix.unitaryGroup (Fin 3) ℝ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mirrorMatrix, Matrix.mul_apply, Fin.sum_univ_three]

/-- `κ₀` as an element of `O(3)`. -/
def mirror : Matrix.unitaryGroup (Fin 3) ℝ := ⟨mirrorMatrix, mirrorMatrix_mem⟩

/-- `κ₀` as an element of `GL_3(ℝ)`. -/
def mirrorUnit : Langlands.GeneralLinear 3 ℝ := Unitary.toUnits mirror

theorem mirrorUnit_mem : mirrorUnit ∈ unitaryCompact ℝ 3 := mirror.2

theorem mirror_mul_mirror : mirror * mirror = 1 := by
  apply Subtype.ext
  show mirrorMatrix * mirrorMatrix = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mirrorMatrix, Matrix.mul_apply, Fin.sum_univ_three]

theorem mirrorUnit_mul_mirrorUnit_mul (x : Langlands.GeneralLinear 3 ℝ) :
    mirrorUnit * (mirrorUnit * x) = x := by
  rw [← mul_assoc, mirrorUnit, ← map_mul, mirror_mul_mirror, map_one, one_mul]

/-- `κ₀ r_0(θ) = r_1(θ) κ₀`. -/
theorem mirror_mul_blockRotation_zero (θ : ℝ) :
    mirrorMatrix * (blockRotation 3 0 θ : Matrix (Fin 3) (Fin 3) ℝ) =
      (blockRotation 3 1 θ : Matrix (Fin 3) (Fin 3) ℝ) * mirrorMatrix := by
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [RealBlockRotation.blockRotation_apply (by norm_num : 0 + 1 < 3),
    RealBlockRotation.blockRotation_apply (by norm_num : 1 + 1 < 3)]
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_three, mirrorMatrix]

/-- `κ₀ r_1(θ) = r_0(θ) κ₀`. -/
theorem mirror_mul_blockRotation_one (θ : ℝ) :
    mirrorMatrix * (blockRotation 3 1 θ : Matrix (Fin 3) (Fin 3) ℝ) =
      (blockRotation 3 0 θ : Matrix (Fin 3) (Fin 3) ℝ) * mirrorMatrix := by
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [RealBlockRotation.blockRotation_apply (by norm_num : 0 + 1 < 3),
    RealBlockRotation.blockRotation_apply (by norm_num : 1 + 1 < 3)]
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_three, mirrorMatrix]

/-- `κ₀ · diag(sgn a) = diag(sgn (a₂, a₁, a₀)) · κ₀`. -/
theorem mirror_mul_signDiagonal (a : Fin 3 → ℝˣ) :
    mirror * signDiagonal (fun i => (a i : ℝ)) =
      signDiagonal (fun i => ((![a 2, a 1, a 0] : Fin 3 → ℝˣ) i : ℝ)) * mirror := by
  apply Subtype.ext
  show mirrorMatrix * Matrix.diagonal _ = Matrix.diagonal _ * mirrorMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mirrorMatrix, Matrix.mul_apply, Matrix.diagonal]

/-! ## The mirror of a function -/

/-- If `κ₀ r_p(θ) = r_q(θ) κ₀`, the block Fourier coefficients along `r_p` of `x ↦ Ψ(κ₀ x)`
at `g` are those of `Ψ` along `r_q` at `κ₀ g`. -/
theorem blockFourierCoefficient_comp_mirror {p q : ℕ}
    (hrot : ∀ θ : ℝ, mirrorMatrix * (blockRotation 3 p θ : Matrix (Fin 3) (Fin 3) ℝ) =
      (blockRotation 3 q θ : Matrix (Fin 3) (Fin 3) ℝ) * mirrorMatrix)
    (Ψ : Langlands.GeneralLinear 3 ℝ → ℂ) (j : ℤ) (g : Langlands.GeneralLinear 3 ℝ) :
    blockFourierCoefficient 3 p j (fun x => Ψ (mirrorUnit * x)) g =
      blockFourierCoefficient 3 q j Ψ (mirrorUnit * g) := by
  unfold blockFourierCoefficient
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have h : mirrorUnit * (blockRotation 3 p θ * g) = blockRotation 3 q θ * (mirrorUnit * g) := by
    rw [← mul_assoc, ← mul_assoc]
    congr 1
    exact Units.ext (hrot θ)
  simp only [h]

/-- The mirror `x ↦ φ(κ₀ x) sgnDet(κ₀ x)^e` of a function `φ` on `GL_3(ℝ)`. -/
def mirrorFun (e : ℕ) (φ : Langlands.GeneralLinear 3 ℝ → ℂ) :
    Langlands.GeneralLinear 3 ℝ → ℂ :=
  fun x => φ (mirrorUnit * x) * sgnDet 3 (mirrorUnit * x) ^ e

theorem continuous_mirrorFun (e : ℕ) {φ : Langlands.GeneralLinear 3 ℝ → ℂ}
    (hφ : Continuous φ) : Continuous (mirrorFun e φ) :=
  (continuous_mul_sgnDet_pow hφ e).comp (continuous_const.mul continuous_id)

/-- The block Fourier coefficients of the mirror. -/
theorem blockFourierCoefficient_mirrorFun {p q : ℕ}
    (hrot : ∀ θ : ℝ, mirrorMatrix * (blockRotation 3 p θ : Matrix (Fin 3) (Fin 3) ℝ) =
      (blockRotation 3 q θ : Matrix (Fin 3) (Fin 3) ℝ) * mirrorMatrix)
    (e : ℕ) (φ : Langlands.GeneralLinear 3 ℝ → ℂ) (j : ℤ) (g : Langlands.GeneralLinear 3 ℝ) :
    blockFourierCoefficient 3 p j (mirrorFun e φ) g =
      sgnDet 3 (mirrorUnit * g) ^ e * blockFourierCoefficient 3 q j φ (mirrorUnit * g) := by
  rw [← blockFourierCoefficient_mul_sgnDet_pow]
  exact blockFourierCoefficient_comp_mirror hrot (fun y => φ y * sgnDet 3 y ^ e) j g

/-! ## The mirror of the standard module of `[c, d]` -/

variable (c : RealCharacterData) (d : ComplexCharacterData)

/-- The real character data `c'` of parity `(ℓ + 1 + ε₁) mod 2` and exponent `0`. -/
def mirrorCharacter : RealCharacterData :=
  RealJacquetFrobenius.charData ⟨(d.weight.natAbs + 1 + c.parity.val) % 2, Nat.mod_lt _ (by norm_num)⟩ 0

theorem mirrorCharacter_parity :
    (mirrorCharacter c d).parity.val = (d.weight.natAbs + 1 + c.parity.val) % 2 :=
  rfl

/-- The principal series function of `[d, c']` extending the restriction to `O(3)` of the
mirror of `f`. -/
def mirrorExt (f : Langlands.GeneralLinear 3 ℝ → ℂ) : Langlands.GeneralLinear 3 ℝ → ℂ :=
  extension (shiftedExponent 3
      (realPositionExponent [RealBlock.induced d, RealBlock.character (mirrorCharacter c d)]))
    (transport mirror fun x => f x * sgnDet 3 x ^ (d.weight.natAbs + 1))

theorem mirrorExt_eq (f : Langlands.GeneralLinear 3 ℝ → ℂ) {x : Langlands.GeneralLinear 3 ℝ}
    (hx : x ∈ unitaryCompact ℝ 3) :
    mirrorExt c d f x = mirrorFun (d.weight.natAbs + 1) f x := by
  have h := extension_unitary (shiftedExponent 3
      (realPositionExponent [RealBlock.induced d, RealBlock.character (mirrorCharacter c d)]))
    (transport mirror fun y => f y * sgnDet 3 y ^ (d.weight.natAbs + 1))
    ⟨(x : Matrix (Fin 3) (Fin 3) ℝ), hx⟩
  rw [RealKTypeCount.toUnits_mk hx, transport_apply] at h
  rw [mirrorExt, h]
  show f (Unitary.toUnits (mirror * ⟨(x : Matrix (Fin 3) (Fin 3) ℝ), hx⟩)) *
      sgnDet 3 (Unitary.toUnits (mirror * ⟨(x : Matrix (Fin 3) (Fin 3) ℝ), hx⟩)) ^ _ =
    f (mirrorUnit * x) * sgnDet 3 (mirrorUnit * x) ^ _
  rw [map_mul, RealKTypeCount.toUnits_mk hx]
  rfl

/-- The sign equivariance of the restriction to `O(3)` of the mirror. -/
theorem transport_mirror_signDiagonal {f : Langlands.GeneralLinear 3 ℝ → ℂ}
    (hf : f ∈ principalSeries ℝ 3
      (realPositionCharacter [RealBlock.character c, RealBlock.induced d]))
    (a : Fin 3 → ℝˣ) (κ : Matrix.unitaryGroup (Fin 3) ℝ) :
    transport mirror (fun x => f x * sgnDet 3 x ^ (d.weight.natAbs + 1))
        (signDiagonal (fun i => (a i : ℝ)) * κ) =
      principalSeriesCharacter ℝ 3
          (realPositionCharacter [RealBlock.induced d, RealBlock.character (mirrorCharacter c d)])
          (fun i => signUnit (a i)) *
        transport mirror (fun x => f x * sgnDet 3 x ^ (d.weight.natAbs + 1)) κ := by
  set b : Fin 3 → ℝˣ := ![a 2, a 1, a 0] with hb
  rw [transport_apply, transport_apply, ← mul_assoc, mirror_mul_signDiagonal, mul_assoc]
  have h₁ : f (Unitary.toUnits (signDiagonal (fun i => (b i : ℝ)) * (mirror * κ))) =
      principalSeriesCharacter ℝ 3
          (realPositionCharacter [RealBlock.character c, RealBlock.induced d])
          (fun i => signUnit (b i)) * f (Unitary.toUnits (mirror * κ)) := by
    rw [PartialJacquet.signDiagonal_toUnits, hf.2]
  have h₂ : sgnDet 3 (Unitary.toUnits (signDiagonal (fun i => (b i : ℝ)) * (mirror * κ))) =
      (∏ i : Fin 3, ((signReal (b i : ℝ) : ℝ) : ℂ)) * sgnDet 3 (Unitary.toUnits (mirror * κ)) := by
    rw [map_mul, sgnDet_mul, sgnDet_signDiagonal]
  have hchar : principalSeriesCharacter ℝ 3
        (realPositionCharacter [RealBlock.character c, RealBlock.induced d])
        (fun i => signUnit (b i)) * (∏ i : Fin 3, ((signReal (b i : ℝ) : ℝ) : ℂ)) ^
          (d.weight.natAbs + 1) =
      principalSeriesCharacter ℝ 3
        (realPositionCharacter [RealBlock.induced d, RealBlock.character (mirrorCharacter c d)])
        (fun i => signUnit (a i)) := by
    rw [JacquetKernel.principalSeriesCharacter_sign, JacquetKernel.principalSeriesCharacter_sign,
      Fin.prod_univ_three, Fin.prod_univ_three, Fin.prod_univ_three]
    simp only [hb, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons,
      realPositionCharacter, character_signUnit, realInducedFirstCharacter_signUnit,
      realInducedSecondCharacter_signUnit, mirrorCharacter_parity]
    exact sign_identity (sq_signReal _) (sq_signReal _) _ _
  show f _ * sgnDet 3 _ ^ _ = _ * (f _ * sgnDet 3 _ ^ _)
  rw [h₁, h₂, mul_pow, ← hchar]
  ring

/-- **The mirror lands in the standard module of `[d, c']`.** -/
theorem mirrorExt_mem {f : Langlands.GeneralLinear 3 ℝ → ℂ}
    (hf : f ∈ kFiniteFunctions (realStandardModule 3 [RealBlock.character c, RealBlock.induced d])
      (unitaryCompact ℝ 3)) :
    mirrorExt c d f ∈ kFiniteFunctions
      (realStandardModule 3 [RealBlock.induced d, RealBlock.character (mirrorCharacter c d)])
      (unitaryCompact ℝ 3) := by
  have hfPS := hf.1.1
  have hE : mirrorExt c d f ∈ kFiniteFunctions (principalSeries ℝ 3
      (realPositionCharacter [RealBlock.induced d, RealBlock.character (mirrorCharacter c d)]))
      (unitaryCompact ℝ 3) :=
    extension_mem_kFiniteFunctions _ (realPositionCharacter_eq_signUnit_mul _)
      (continuous_transport mirror (continuous_mul_sgnDet_pow hfPS.1.continuous _))
      (finiteDimensional_transport mirror (mem_kFiniteVectors_mul_sgnDet_pow hf.2 _))
      (fun a κ => transport_mirror_signDiagonal c d hfPS a κ)
  refine Submodule.mem_inf.mpr ⟨mem_realStandardModule_of_unitaryCompact (n := 3) rfl
    (Submodule.mem_inf.mp hE).1 ?_, (Submodule.mem_inf.mp hE).2⟩
  intro p d' hd j hj x hx
  rcases p with _ | _ | _ | p
  · simp only [realInducedBlockAt, Option.some.injEq] at hd
    subst hd
    rw [blockFourierCoefficient_congr (fun y hy => mirrorExt_eq c d f hy) 0 j hx,
      blockFourierCoefficient_mirrorFun mirror_mul_blockRotation_zero,
      hf.1.2 1 _ (by simp [realInducedBlockAt]) j hj _, mul_zero]
  all_goals simp [realInducedBlockAt] at hd

/-! ## The mirror of the landing statement -/

/-- **`RealSwapLandingInducedFirstStatement` implies `RealSwapLandingCharacterFirstStatement`.**
The mirror by `κ₀` (with the twist `sgnDet^(ℓ+1)`) carries the data of the character-first
statement for `c`, `d`, `δ`, `μ₀`, `μ₁` to those of the induced-first statement for `c'`, `d`,
`δ`, with `μ₀` as the multiplier along `r_1` and `μ₁` as the multiplier along `r_0`. -/
theorem characterFirst_of_inducedFirst (hI : RealSwapLandingInducedFirstStatement) :
    RealSwapLandingCharacterFirstStatement := by
  intro c d δ μ₀ μ₁ f h u hμ₀ hσ₀ hμ₁ hσ₁ hf hh hu hhf huh g hg k hk
  have hpar := mirrorCharacter_parity c d
  have key := hI (mirrorCharacter c d) d δ μ₁ μ₀ (mirrorExt c d f)
    (mirrorFun (d.weight.natAbs + 1) h) (mirrorFun (d.weight.natAbs + 1) u)
    (isRecurrent_congr hμ₀ (by rw [hpar]; exact even_sub_mod _))
    (isSymmetric_congr hσ₀ (by rw [hpar]; exact even_sub_mod _)
      (neg_one_pow_congr (by rw [hpar, Nat.mod_mod])))
    (isRecurrent_congr hμ₁ (by rw [hpar]; exact even_sub_mod' _ _))
    (isSymmetric_congr hσ₁ (by rw [hpar]; exact even_sub_mod' _ _)
      (neg_one_pow_congr (by rw [hpar]; omega)))
    (mirrorExt_mem c d hf) (continuous_mirrorFun _ hh) (continuous_mirrorFun _ hu)
    (fun x hx j => by
      rw [blockFourierCoefficient_mirrorFun mirror_mul_blockRotation_one,
        blockFourierCoefficient_congr (fun y hy => mirrorExt_eq c d f hy) 1 j hx,
        blockFourierCoefficient_mirrorFun mirror_mul_blockRotation_one,
        hhf _ ((unitaryCompact ℝ 3).mul_mem mirrorUnit_mem hx)]
      ring)
    (fun x hx j => by
      rw [blockFourierCoefficient_mirrorFun mirror_mul_blockRotation_zero,
        blockFourierCoefficient_mirrorFun mirror_mul_blockRotation_zero,
        huh _ ((unitaryCompact ℝ 3).mul_mem mirrorUnit_mem hx)]
      ring)
  have h₁ := key (mirrorUnit * g) ((unitaryCompact ℝ 3).mul_mem mirrorUnit_mem hg) k hk
  rw [blockFourierCoefficient_mirrorFun mirror_mul_blockRotation_one,
    mirrorUnit_mul_mirrorUnit_mul] at h₁
  exact (mul_eq_zero.mp h₁).resolve_left (pow_ne_zero _ (sgnDet_ne_zero g))

end RealSwapLandingMirror

end Langlands.Archimedean
