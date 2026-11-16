import Langlands.Representation.Archimedean.RealKTypeCount
import Langlands.Representation.Archimedean.PrincipalSeriesExtension
import Langlands.Representation.Archimedean.RealBlockFourierPropagation
import Langlands.Representation.Archimedean.RealBlockFourierFinite
import Langlands.Representation.Archimedean.RealStrictCharacterLanglandsQuotient
import Langlands.Representation.Archimedean.JacquetKernel
import Langlands.Representation.Archimedean.RealStandardModuleGKModule

/-!
# Transporting `O(n)`-finite functions by left multiplication on `O(n)`

For `κ₀ ∈ O(n)` and an `O(n)`-finite function `f` of a principal series of `GL_n(ℝ)`, the
function `κ ↦ f(κ₀ κ)` on `O(n)` extends (Library module `PrincipalSeriesExtension`) to an
`O(n)`-finite function of another principal series, provided left multiplication by `κ₀` carries
the sign matrices compatibly with the two characters (`IsSignCompatible`). The resulting map
`transportMap` is injective and commutes with right translation by `O(n)`.

On `GL_3(ℝ)`, the cyclic permutation `w` (`cycle`) with `w r_0(θ) = r_1(θ) w` and its inverse
give such maps between the `O(3)`-finite functions of the standard modules of `[χ, D]` and of
`[D, χ]`, in both directions (`cycleMap`, `cycleInvMap`). With the counting lemma
`RealKTypeCount.surjective_of_injective` this proves that every injective linear map between
these two spaces that commutes with right translation by `O(3)` is surjective
(`surjective_of_injective_induced_character`, `surjective_of_injective_character_induced`).

The module also proves `mem_realStandardModule_of_unitaryCompact`: a function of the principal
series of the position characters lies in the standard module as soon as its block Fourier
coefficients of the small modes vanish on `O(n)`.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

open scoped Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false

namespace RealKTypeTransport

open PrincipalSeriesExtension GramFormula

variable {n : ℕ}

/-! ## Standard modules from vanishing on `O(n)` -/

/-- The position characters and exponents at an induction block. -/
theorem realInducedBlockAt_eq_some : ∀ {ds : List RealBlock} {p : ℕ} {d : ComplexCharacterData},
    realInducedBlockAt ds p = some d →
      realPositionCharacter ds p = realInducedFirstCharacter d ∧
      realPositionCharacter ds (p + 1) = realInducedSecondCharacter d ∧
      realPositionExponent ds p = d.exponent + (d.weight.natAbs : ℂ) / 2 ∧
      realPositionExponent ds (p + 1) = d.exponent - (d.weight.natAbs : ℂ) / 2
  | [], _, _, h => by simp [realInducedBlockAt] at h
  | .character _ :: _, 0, _, h => by simp [realInducedBlockAt] at h
  | .character _ :: ds, p + 1, _, h => by
      have := realInducedBlockAt_eq_some (ds := ds) (p := p) h
      simpa [realPositionCharacter, realPositionExponent] using this
  | .induced _ :: _, 0, _, h => by
      simp only [realInducedBlockAt, Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl, rfl, rfl⟩
  | .induced _ :: _, 1, _, h => by simp [realInducedBlockAt] at h
  | .induced _ :: ds, p + 2, _, h => by
      have := realInducedBlockAt_eq_some (ds := ds) (p := p) h
      simpa [realPositionCharacter, realPositionExponent] using this

theorem realPositionCharacter_exp (ds : List RealBlock) (l : ℕ) (x : ℝ) :
    realPositionCharacter ds l (Units.mk0 (Real.exp x) (Real.exp_pos x).ne') =
      Complex.exp (realPositionExponent ds l * x) := by
  have hs : signUnit (Units.mk0 (Real.exp x) (Real.exp_pos x).ne') = 1 := by
    unfold signUnit
    exact ite_eq_left_iff.mpr fun h => absurd (Real.exp_pos x) h
  rw [realPositionCharacter_eq_signUnit_mul, hs,
    RealStrictCharacterLanglandsQuotient.realPositionCharacter_one, one_mul, Units.val_mk0,
    abs_of_pos (Real.exp_pos x),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, mul_comm]

theorem even_of_neg_one_zpow_eq {j : ℤ} {M : ℕ} (h : (-1 : ℂ) ^ j = (-1) ^ (M + 1)) :
    Even (j + M + 1) := by
  rcases Int.even_or_odd j with hj | hj <;> rcases Nat.even_or_odd (M + 1) with hm | hm
  · obtain ⟨r, rfl⟩ := hj
    obtain ⟨q, hq⟩ := hm
    exact ⟨r + q, by omega⟩
  · rw [hj.neg_one_zpow, hm.neg_one_pow] at h
    norm_num at h
  · rw [hj.neg_one_zpow, hm.neg_one_pow] at h
    norm_num at h
  · obtain ⟨r, rfl⟩ := hj
    obtain ⟨q, hq⟩ := hm
    exact ⟨r + q + 1, by omega⟩

/-- **Standard modules from `O(n)`.** A function of the principal series of the position
characters of `ds` lies in the standard module of `ds` as soon as, at every induction block of
weight `m`, its block Fourier coefficients of the modes `|j| < |m|` vanish on `O(n)`. -/
theorem mem_realStandardModule_of_unitaryCompact {ds : List RealBlock} (hN : realRank ds = n)
    {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : f ∈ principalSeries ℝ n (realPositionCharacter ds))
    (hK : ∀ (p : ℕ) (d : ComplexCharacterData), realInducedBlockAt ds p = some d →
      ∀ j : ℤ, |j| < |d.weight| → ∀ k ∈ unitaryCompact ℝ n,
        blockFourierCoefficient n p j f k = 0) :
    f ∈ realStandardModule n ds := by
  refine ⟨hf, fun p d hd j hj g => ?_⟩
  have hp : p + 1 < n := hN ▸ realInducedBlockAt_lt hd
  obtain ⟨hc1, hc2, he1, he2⟩ := realInducedBlockAt_eq_some hd
  rw [Int.abs_eq_natAbs d.weight] at hj
  by_cases hev : Even (j + (d.weight.natAbs : ℤ) + 1)
  · have hα := RealBlockDerivative.isExpEquivariant_of_mem_principalSeries
      (τ := fun i : Fin n => realPositionExponent ds i)
      (fun i x => realPositionCharacter_exp ds i x) hf
    have hδ : (fun i : Fin n => realPositionExponent ds i + ((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ))
          (RealBlockRotation.ia hp) -
        (fun i : Fin n => realPositionExponent ds i + ((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ))
          (RealBlockRotation.ib hp) = ((d.weight.natAbs : ℕ) : ℂ) + 1 := by
      show realPositionExponent ds p + ((n : ℂ) - 1) / 2 - (p : ℂ) -
        (realPositionExponent ds (p + 1) + ((n : ℂ) - 1) / 2 - ((p + 1 : ℕ) : ℂ)) = _
      rw [he1, he2]
      push_cast
      ring
    refine RealBlockPropagation.blockFourierCoefficient_window_eq_zero hp hf.1 hα hδ
      (fun k hk j' hj' => ?_) g j (RealBlockPropagation.mem_window.mpr ⟨hj, hev⟩)
    have hj'' := (RealBlockPropagation.mem_window.mp hj').1
    exact hK p d hd j' (by rw [Int.abs_eq_natAbs d.weight]; exact hj'') k hk
  · refine RealBlockFourierFinite.blockFourierCoefficient_eq_zero_of_parity hp
      (RealStrictCharacterLanglandsQuotient.realPositionCharacter_one ds) hf ?_ g
    rw [hc1, hc2]
    have a1 : realInducedFirstCharacter d (-1) = (-1) ^ (d.weight.natAbs + 1) := by
      simp [realInducedFirstCharacter]
    have a2 : realInducedSecondCharacter d (-1) = 1 := by
      simp [realInducedSecondCharacter]
    rw [a1, a2, mul_one]
    exact fun h => hev (even_of_neg_one_zpow_eq h)

/-! ## Transport by left multiplication -/

/-- The function `κ ↦ f(κ₀ κ)` on `O(n)` attached to a function `f` on `GL_n(ℝ)`. -/
def transport (κ₀ : Matrix.unitaryGroup (Fin n) ℝ) :
    (Langlands.GeneralLinear n ℝ → ℂ) →ₗ[ℂ] (Matrix.unitaryGroup (Fin n) ℝ → ℂ) :=
  LinearMap.funLeft ℂ ℂ fun κ => Unitary.toUnits (κ₀ * κ)

theorem transport_apply (κ₀ : Matrix.unitaryGroup (Fin n) ℝ)
    (f : Langlands.GeneralLinear n ℝ → ℂ) (κ : Matrix.unitaryGroup (Fin n) ℝ) :
    transport κ₀ f κ = f (Unitary.toUnits (κ₀ * κ)) :=
  rfl

theorem continuous_transport (κ₀ : Matrix.unitaryGroup (Fin n) ℝ)
    {f : Langlands.GeneralLinear n ℝ → ℂ} (hf : Continuous f) : Continuous (transport κ₀ f) :=
  hf.comp (continuous_unitary_toUnits.comp (continuous_const.mul continuous_id))

theorem finiteDimensional_transport (κ₀ : Matrix.unitaryGroup (Fin n) ℝ)
    {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ))
      (unitaryCompact ℝ n)) :
    FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun k : Matrix.unitaryGroup (Fin n) ℝ => fun x => transport κ₀ f (x * k))) := by
  have hfK : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : unitaryCompact ℝ n =>
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
        (k : Langlands.GeneralLinear n ℝ) f)) := hf
  have hle : Submodule.span ℂ (Set.range fun k : Matrix.unitaryGroup (Fin n) ℝ =>
      fun x => transport κ₀ f (x * k)) ≤
      (Submodule.span ℂ (Set.range fun k : unitaryCompact ℝ n =>
        Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
          (k : Langlands.GeneralLinear n ℝ) f)).map (transport κ₀) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    refine ⟨_, Submodule.subset_span ⟨⟨Unitary.toUnits k, k.2⟩, rfl⟩, ?_⟩
    funext x
    show f (Unitary.toUnits (κ₀ * x) * Unitary.toUnits k) = f (Unitary.toUnits (κ₀ * (x * k)))
    rw [← map_mul, mul_assoc]
  exact Submodule.finiteDimensional_of_le hle

/-- Left multiplication by `κ₀` carries the sign matrices compatibly with the characters `χ`
(of the source) and `χ'` (of the target): for every `a`, there is `b` with
`κ₀ · diag(sgn a) = diag(sgn b) · κ₀` and `χ(sgn b) = χ'(sgn a)` for the principal series
characters. -/
def IsSignCompatible (κ₀ : Matrix.unitaryGroup (Fin n) ℝ) (χ χ' : ℕ → ℝˣ → ℂ) : Prop :=
  ∀ a : Fin n → ℝˣ, ∃ b : Fin n → ℝˣ,
    κ₀ * signDiagonal (fun i => (a i : ℝ)) = signDiagonal (fun i => (b i : ℝ)) * κ₀ ∧
      principalSeriesCharacter ℝ n χ (fun i => signUnit (b i)) =
        principalSeriesCharacter ℝ n χ' (fun i => signUnit (a i))

theorem transport_signDiagonal_mul {κ₀ : Matrix.unitaryGroup (Fin n) ℝ} {χ χ' : ℕ → ℝˣ → ℂ}
    (hκ₀ : IsSignCompatible κ₀ χ χ') {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : f ∈ principalSeries ℝ n χ) (a : Fin n → ℝˣ) (κ : Matrix.unitaryGroup (Fin n) ℝ) :
    transport κ₀ f (signDiagonal (fun i => (a i : ℝ)) * κ) =
      principalSeriesCharacter ℝ n χ' (fun i => signUnit (a i)) * transport κ₀ f κ := by
  obtain ⟨b, hb, hχ⟩ := hκ₀ a
  rw [transport_apply, transport_apply, ← mul_assoc, hb, mul_assoc,
    PartialJacquet.signDiagonal_toUnits, hf.2, hχ]

variable {χ χ' : ℕ → ℝˣ → ℂ} {e' : ℕ → ℂ}

/-- The extension of the transport of an `O(n)`-finite principal series function is an
`O(n)`-finite function of the principal series of `χ'`. -/
theorem extension_transport_mem {V : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ)}
    (hV : V ≤ principalSeries ℝ n χ) {κ₀ : Matrix.unitaryGroup (Fin n) ℝ}
    (hκ₀ : IsSignCompatible κ₀ χ χ')
    (hχ' : ∀ (l : ℕ) (x : ℝˣ), χ' l x = χ' l (signUnit x) * ((|(x : ℝ)| : ℝ) : ℂ) ^ e' l)
    {f : Langlands.GeneralLinear n ℝ → ℂ} (hf : f ∈ kFiniteFunctions V (unitaryCompact ℝ n)) :
    extension (shiftedExponent n e') (transport κ₀ f) ∈
      kFiniteFunctions (principalSeries ℝ n χ') (unitaryCompact ℝ n) :=
  extension_mem_kFiniteFunctions e' hχ' (continuous_transport κ₀ (hV hf.1).1.continuous)
    (finiteDimensional_transport κ₀ hf.2) fun a κ => transport_signDiagonal_mul hκ₀ (hV hf.1) a κ

/-- The transport map `f ↦ extension (κ ↦ f(κ₀ κ))` from the `O(n)`-finite functions of `V`
to those of `W`, given that it lands there. -/
def transportMap (V W : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ))
    (κ₀ : Matrix.unitaryGroup (Fin n) ℝ) (e' : ℕ → ℂ)
    (hVW : ∀ f ∈ kFiniteFunctions V (unitaryCompact ℝ n),
      extension (shiftedExponent n e') (transport κ₀ f) ∈ kFiniteFunctions W (unitaryCompact ℝ n)) :
    kFiniteFunctions V (unitaryCompact ℝ n) →ₗ[ℂ] kFiniteFunctions W (unitaryCompact ℝ n) :=
  LinearMap.codRestrict _ (extensionLinear (shiftedExponent n e') ∘ₗ transport κ₀ ∘ₗ
    (kFiniteFunctions V (unitaryCompact ℝ n)).subtype) fun f => hVW f f.2

theorem transportMap_apply_toUnits {V W : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ)}
    {κ₀ : Matrix.unitaryGroup (Fin n) ℝ}
    {hVW : ∀ f ∈ kFiniteFunctions V (unitaryCompact ℝ n),
      extension (shiftedExponent n e') (transport κ₀ f) ∈ kFiniteFunctions W (unitaryCompact ℝ n)}
    (f : kFiniteFunctions V (unitaryCompact ℝ n)) (κ : Matrix.unitaryGroup (Fin n) ℝ) :
    (transportMap V W κ₀ e' hVW f : Langlands.GeneralLinear n ℝ → ℂ) (Unitary.toUnits κ) =
      (f : Langlands.GeneralLinear n ℝ → ℂ) (Unitary.toUnits (κ₀ * κ)) :=
  extension_unitary _ _ κ

/-- The transport map is injective. -/
theorem transportMap_injective {V W : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ)}
    (hV : V ≤ principalSeries ℝ n χ) {κ₀ : Matrix.unitaryGroup (Fin n) ℝ}
    {hVW : ∀ f ∈ kFiniteFunctions V (unitaryCompact ℝ n),
      extension (shiftedExponent n e') (transport κ₀ f) ∈ kFiniteFunctions W (unitaryCompact ℝ n)} :
    Function.Injective (transportMap V W κ₀ e' hVW) := by
  refine (injective_iff_map_eq_zero _).mpr fun f hf => Subtype.ext ?_
  refine eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact (hV f.2.1) fun k hk => ?_
  have h := congrArg (fun F : kFiniteFunctions W (unitaryCompact ℝ n) =>
    (F : Langlands.GeneralLinear n ℝ → ℂ)
      (Unitary.toUnits (κ₀⁻¹ * ⟨(k : Matrix (Fin n) (Fin n) ℝ), hk⟩))) hf
  rw [transportMap_apply_toUnits, mul_inv_cancel_left, RealKTypeCount.toUnits_mk hk] at h
  exact h

/-- The transport map commutes with right translation by `O(n)`. -/
theorem transportMap_isRealKEquivariant {V W : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ)}
    (hV : V ≤ principalSeries ℝ n χ)
    (hVK : ∀ k ∈ unitaryCompact ℝ n, ∀ f ∈ kFiniteFunctions V (unitaryCompact ℝ n),
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) k f ∈
        kFiniteFunctions V (unitaryCompact ℝ n))
    {κ₀ : Matrix.unitaryGroup (Fin n) ℝ} (hκ₀ : IsSignCompatible κ₀ χ χ')
    (hχ' : ∀ (l : ℕ) (x : ℝˣ), χ' l x = χ' l (signUnit x) * ((|(x : ℝ)| : ℝ) : ℂ) ^ e' l)
    {hVW : ∀ f ∈ kFiniteFunctions V (unitaryCompact ℝ n),
      extension (shiftedExponent n e') (transport κ₀ f) ∈ kFiniteFunctions W (unitaryCompact ℝ n)} :
    IsRealKEquivariant V W (transportMap V W κ₀ e' hVW) := by
  intro k f
  have hf := hVK k k.2 f f.2
  set κ : Matrix.unitaryGroup (Fin n) ℝ :=
    ⟨((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ), k.2⟩ with hκdef
  have hkκ : (k : Langlands.GeneralLinear n ℝ) = Unitary.toUnits κ := Units.ext rfl
  have heq : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
      (k : Langlands.GeneralLinear n ℝ)
        (transportMap V W κ₀ e' hVW f : Langlands.GeneralLinear n ℝ → ℂ) =
      (transportMap V W κ₀ e' hVW ⟨_, hf⟩ : Langlands.GeneralLinear n ℝ → ℂ) := by
    have hfV := hV f.2.1
    refine (congrArg (fun s => Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) s
      (transportMap V W κ₀ e' hVW f : Langlands.GeneralLinear n ℝ → ℂ)) hkκ).trans ?_
    refine (rightTranslation_extension e' hχ'
      (continuous_transport κ₀ hfV.1.continuous) (finiteDimensional_transport κ₀ f.2.2)
      (fun a κ' => transport_signDiagonal_mul hκ₀ hfV a κ') κ).trans ?_
    show extension (shiftedExponent n e') _ = extension (shiftedExponent n e') _
    congr 1
    funext x
    show (f : Langlands.GeneralLinear n ℝ → ℂ) (Unitary.toUnits (κ₀ * (x * κ))) =
      (f : Langlands.GeneralLinear n ℝ → ℂ) (Unitary.toUnits (κ₀ * x) * (k : _))
    rw [hkκ, ← map_mul, mul_assoc]
  have hg : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
      (k : Langlands.GeneralLinear n ℝ)
        (transportMap V W κ₀ e' hVW f : Langlands.GeneralLinear n ℝ → ℂ) ∈
          kFiniteFunctions W (unitaryCompact ℝ n) := by
    rw [heq]
    exact (transportMap V W κ₀ e' hVW ⟨_, hf⟩).2
  exact ⟨hf, hg, Subtype.ext heq.symm⟩

/-- The block Fourier coefficients of a function `g` with `g(κ) = f(κ₀ κ)` on `O(n)`, at a
point of `O(n)`, when `κ₀ r_p(θ) = r_q(θ) κ₀`. -/
theorem blockFourierCoefficient_of_transport {f g : Langlands.GeneralLinear n ℝ → ℂ}
    {κ₀ : Matrix.unitaryGroup (Fin n) ℝ}
    (hg : ∀ κ : Matrix.unitaryGroup (Fin n) ℝ,
      g (Unitary.toUnits κ) = f (Unitary.toUnits (κ₀ * κ)))
    {p q : ℕ} (hrot : ∀ θ : ℝ, (κ₀ : Matrix (Fin n) (Fin n) ℝ) *
      (blockRotation n p θ : Matrix (Fin n) (Fin n) ℝ) =
        (blockRotation n q θ : Matrix (Fin n) (Fin n) ℝ) * (κ₀ : Matrix (Fin n) (Fin n) ℝ))
    (j : ℤ) {k : Langlands.GeneralLinear n ℝ} (hk : k ∈ unitaryCompact ℝ n) :
    blockFourierCoefficient n p j g k =
      blockFourierCoefficient n q j f
        (Unitary.toUnits (κ₀ * ⟨(k : Matrix (Fin n) (Fin n) ℝ), hk⟩)) := by
  unfold blockFourierCoefficient
  congr 1
  funext θ
  congr 1
  have hmem : ((blockRotation n p θ * k : Langlands.GeneralLinear n ℝ) :
      Matrix (Fin n) (Fin n) ℝ) ∈ Matrix.unitaryGroup (Fin n) ℝ :=
    (unitaryCompact ℝ n).mul_mem (blockRotation_mem_unitaryCompact n p θ) hk
  have h1 : blockRotation n p θ * k = Unitary.toUnits (⟨_, hmem⟩ : Matrix.unitaryGroup (Fin n) ℝ) :=
    Units.ext rfl
  rw [h1, hg]
  congr 1
  apply Units.ext
  show (κ₀ : Matrix (Fin n) (Fin n) ℝ) * ((blockRotation n p θ : Matrix (Fin n) (Fin n) ℝ) *
      (k : Matrix (Fin n) (Fin n) ℝ)) =
    (blockRotation n q θ : Matrix (Fin n) (Fin n) ℝ) *
      ((κ₀ : Matrix (Fin n) (Fin n) ℝ) * (k : Matrix (Fin n) (Fin n) ℝ))
  rw [← Matrix.mul_assoc, hrot, Matrix.mul_assoc]

/-! ## The cyclic permutation of `GL_3(ℝ)` -/

/-- The cyclic permutation matrix `w` with `w e₀ = e₁`, `w e₁ = e₂`, `w e₂ = e₀`. -/
def cycleMatrix : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

/-- The inverse cyclic permutation matrix `w⁻¹`. -/
def cycleInvMatrix : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, 0; 0, 0, 1; 1, 0, 0]

theorem cycleMatrix_mem : cycleMatrix ∈ Matrix.unitaryGroup (Fin 3) ℝ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycleMatrix, Matrix.mul_apply, Fin.sum_univ_three]

theorem cycleInvMatrix_mem : cycleInvMatrix ∈ Matrix.unitaryGroup (Fin 3) ℝ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycleInvMatrix, Matrix.mul_apply, Fin.sum_univ_three]

/-- `w` as an element of `O(3)`. -/
def cycle : Matrix.unitaryGroup (Fin 3) ℝ := ⟨cycleMatrix, cycleMatrix_mem⟩

/-- `w⁻¹` as an element of `O(3)`. -/
def cycleInv : Matrix.unitaryGroup (Fin 3) ℝ := ⟨cycleInvMatrix, cycleInvMatrix_mem⟩

/-- `w r_0(θ) = r_1(θ) w`. -/
theorem cycle_mul_blockRotation (θ : ℝ) :
    ((cycle : Matrix.unitaryGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *
        (blockRotation 3 0 θ : Matrix (Fin 3) (Fin 3) ℝ) =
      (blockRotation 3 1 θ : Matrix (Fin 3) (Fin 3) ℝ) *
        ((cycle : Matrix.unitaryGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
  show cycleMatrix * _ = _ * cycleMatrix
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [RealBlockRotation.blockRotation_apply (by norm_num : 0 + 1 < 3),
    RealBlockRotation.blockRotation_apply (by norm_num : 1 + 1 < 3)]
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_three, cycleMatrix]

/-- `w⁻¹ r_1(θ) = r_0(θ) w⁻¹`. -/
theorem cycleInv_mul_blockRotation (θ : ℝ) :
    ((cycleInv : Matrix.unitaryGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *
        (blockRotation 3 1 θ : Matrix (Fin 3) (Fin 3) ℝ) =
      (blockRotation 3 0 θ : Matrix (Fin 3) (Fin 3) ℝ) *
        ((cycleInv : Matrix.unitaryGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
  show cycleInvMatrix * _ = _ * cycleInvMatrix
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [RealBlockRotation.blockRotation_apply (by norm_num : 0 + 1 < 3),
    RealBlockRotation.blockRotation_apply (by norm_num : 1 + 1 < 3)]
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_three, cycleInvMatrix]

variable (c : RealCharacterData) (d : ComplexCharacterData)

theorem cycle_isSignCompatible :
    IsSignCompatible cycle (realPositionCharacter [RealBlock.character c, RealBlock.induced d])
      (realPositionCharacter [RealBlock.induced d, RealBlock.character c]) := by
  intro a
  refine ⟨![a 2, a 0, a 1], ?_, ?_⟩
  · apply Subtype.ext
    show cycleMatrix * Matrix.diagonal _ = Matrix.diagonal _ * cycleMatrix
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cycleMatrix, Matrix.mul_apply, Matrix.diagonal]
  · rw [JacquetKernel.principalSeriesCharacter_sign, JacquetKernel.principalSeriesCharacter_sign,
      Fin.prod_univ_three, Fin.prod_univ_three]
    simp [realPositionCharacter]
    ring

theorem cycleInv_isSignCompatible :
    IsSignCompatible cycleInv (realPositionCharacter [RealBlock.induced d, RealBlock.character c])
      (realPositionCharacter [RealBlock.character c, RealBlock.induced d]) := by
  intro a
  refine ⟨![a 1, a 2, a 0], ?_, ?_⟩
  · apply Subtype.ext
    show cycleInvMatrix * Matrix.diagonal _ = Matrix.diagonal _ * cycleInvMatrix
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cycleInvMatrix, Matrix.mul_apply, Matrix.diagonal]
  · rw [JacquetKernel.principalSeriesCharacter_sign, JacquetKernel.principalSeriesCharacter_sign,
      Fin.prod_univ_three, Fin.prod_univ_three]
    simp [realPositionCharacter]
    ring

theorem cycle_landing :
    ∀ f ∈ kFiniteFunctions (realStandardModule 3 [RealBlock.character c, RealBlock.induced d])
        (unitaryCompact ℝ 3),
      extension (shiftedExponent 3
          (realPositionExponent [RealBlock.induced d, RealBlock.character c]))
          (transport cycle f) ∈
        kFiniteFunctions (realStandardModule 3 [RealBlock.induced d, RealBlock.character c])
          (unitaryCompact ℝ 3) := by
  intro f hf
  have hE := extension_transport_mem (realStandardModule_le_principalSeries _ _) (cycle_isSignCompatible c d)
    (realPositionCharacter_eq_signUnit_mul _) hf
  refine Submodule.mem_inf.mpr ⟨mem_realStandardModule_of_unitaryCompact (n := 3) rfl
    (Submodule.mem_inf.mp hE).1 ?_, (Submodule.mem_inf.mp hE).2⟩
  have hg : ∀ κ : Matrix.unitaryGroup (Fin 3) ℝ,
      extension (shiftedExponent 3
          (realPositionExponent [RealBlock.induced d, RealBlock.character c]))
          (transport cycle f) (Unitary.toUnits κ) = f (Unitary.toUnits (cycle * κ)) :=
    fun κ => extension_unitary _ _ κ
  intro p d' hd j hj k hk
  rcases p with _ | _ | _ | p
  · simp only [realInducedBlockAt, Option.some.injEq] at hd
    subst hd
    rw [blockFourierCoefficient_of_transport hg cycle_mul_blockRotation j hk]
    exact (Submodule.mem_inf.mp hf).1.2 1 d (by simp [realInducedBlockAt]) j hj _
  all_goals simp [realInducedBlockAt] at hd

theorem cycleInv_landing :
    ∀ f ∈ kFiniteFunctions (realStandardModule 3 [RealBlock.induced d, RealBlock.character c])
        (unitaryCompact ℝ 3),
      extension (shiftedExponent 3
          (realPositionExponent [RealBlock.character c, RealBlock.induced d]))
          (transport cycleInv f) ∈
        kFiniteFunctions (realStandardModule 3 [RealBlock.character c, RealBlock.induced d])
          (unitaryCompact ℝ 3) := by
  intro f hf
  have hE := extension_transport_mem (realStandardModule_le_principalSeries _ _) (cycleInv_isSignCompatible c d)
    (realPositionCharacter_eq_signUnit_mul _) hf
  refine Submodule.mem_inf.mpr ⟨mem_realStandardModule_of_unitaryCompact (n := 3) rfl
    (Submodule.mem_inf.mp hE).1 ?_, (Submodule.mem_inf.mp hE).2⟩
  have hg : ∀ κ : Matrix.unitaryGroup (Fin 3) ℝ,
      extension (shiftedExponent 3
          (realPositionExponent [RealBlock.character c, RealBlock.induced d]))
          (transport cycleInv f) (Unitary.toUnits κ) = f (Unitary.toUnits (cycleInv * κ)) :=
    fun κ => extension_unitary _ _ κ
  intro p d' hd j hj k hk
  rcases p with _ | _ | _ | p
  · simp [realInducedBlockAt] at hd
  · simp only [realInducedBlockAt, Option.some.injEq] at hd
    subst hd
    show blockFourierCoefficient 3 1 j _ k = 0
    rw [blockFourierCoefficient_of_transport hg cycleInv_mul_blockRotation j hk]
    exact (Submodule.mem_inf.mp hf).1.2 0 d (by simp [realInducedBlockAt]) j hj _
  all_goals simp [realInducedBlockAt] at hd

/-- The transport by `w` from `[χ, D]` to `[D, χ]`. -/
def cycleMap :
    kFiniteFunctions (realStandardModule 3 [RealBlock.character c, RealBlock.induced d])
        (unitaryCompact ℝ 3) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule 3 [RealBlock.induced d, RealBlock.character c])
        (unitaryCompact ℝ 3) :=
  transportMap _ _ cycle _ (cycle_landing c d)

/-- The transport by `w⁻¹` from `[D, χ]` to `[χ, D]`. -/
def cycleInvMap :
    kFiniteFunctions (realStandardModule 3 [RealBlock.induced d, RealBlock.character c])
        (unitaryCompact ℝ 3) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule 3 [RealBlock.character c, RealBlock.induced d])
        (unitaryCompact ℝ 3) :=
  transportMap _ _ cycleInv _ (cycleInv_landing c d)

theorem cycleMap_injective : Function.Injective (cycleMap c d) :=
  transportMap_injective (realStandardModule_le_principalSeries _ _)

theorem cycleInvMap_injective : Function.Injective (cycleInvMap c d) :=
  transportMap_injective (realStandardModule_le_principalSeries _ _)

theorem cycleMap_isRealKEquivariant : IsRealKEquivariant _ _ (cycleMap c d) :=
  transportMap_isRealKEquivariant (realStandardModule_le_principalSeries _ _)
    (fun _ hk _ hf => rightTranslation_mem_kFiniteFunctions_realStandardModule 3 _ hf hk)
    (cycle_isSignCompatible c d) (realPositionCharacter_eq_signUnit_mul _)

theorem cycleInvMap_isRealKEquivariant : IsRealKEquivariant _ _ (cycleInvMap c d) :=
  transportMap_isRealKEquivariant (realStandardModule_le_principalSeries _ _)
    (fun _ hk _ hf => rightTranslation_mem_kFiniteFunctions_realStandardModule 3 _ hf hk)
    (cycleInv_isSignCompatible c d) (realPositionCharacter_eq_signUnit_mul _)

/-- **K-count on `GL_3(ℝ)`, from `[D, χ]` to `[χ, D]`.** An injective linear map from the
`O(3)`-finite functions of the standard module of `[D, χ]` to those of `[χ, D]` that commutes
with right translation by `O(3)` is surjective. -/
theorem surjective_of_injective_induced_character
    {T : kFiniteFunctions (realStandardModule 3 [RealBlock.induced d, RealBlock.character c])
        (unitaryCompact ℝ 3) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule 3 [RealBlock.character c, RealBlock.induced d])
        (unitaryCompact ℝ 3)}
    (hT : IsRealKEquivariant _ _ T) (hTi : Function.Injective T) : Function.Surjective T :=
  RealKTypeCount.surjective_of_injective (realStandardModule_le_principalSeries _ _) (realStandardModule_le_principalSeries _ _) hT hTi
    (cycleMap_isRealKEquivariant c d) (cycleMap_injective c d)

/-- **K-count on `GL_3(ℝ)`, from `[χ, D]` to `[D, χ]`.** An injective linear map from the
`O(3)`-finite functions of the standard module of `[χ, D]` to those of `[D, χ]` that commutes
with right translation by `O(3)` is surjective. -/
theorem surjective_of_injective_character_induced
    {T : kFiniteFunctions (realStandardModule 3 [RealBlock.character c, RealBlock.induced d])
        (unitaryCompact ℝ 3) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule 3 [RealBlock.induced d, RealBlock.character c])
        (unitaryCompact ℝ 3)}
    (hT : IsRealKEquivariant _ _ T) (hTi : Function.Injective T) : Function.Surjective T :=
  RealKTypeCount.surjective_of_injective (realStandardModule_le_principalSeries _ _) (realStandardModule_le_principalSeries _ _) hT hTi
    (cycleInvMap_isRealKEquivariant c d) (cycleInvMap_injective c d)

end RealKTypeTransport

end Langlands.Archimedean
