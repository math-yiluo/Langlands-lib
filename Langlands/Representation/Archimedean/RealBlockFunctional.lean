import Langlands.Representation.Archimedean.RealBlockDual
import Langlands.Representation.Archimedean.JacquetNonvanishing
import Langlands.Representation.Archimedean.JacquetKernel

/-!
# The block Jacquet functional on `GL_n(ℝ)` and its vanishing on proper submodules

For a decomposition of `n` into consecutive blocks (`ks`, block sizes `k+1`, last block first)
such that the exponents are tied within each block and strictly decrease between blocks
(`RealBlockFunctional.BlockOrdered`), the functional `RealBlockFunctional.jac` peels off the
last block with `RealBlockJacquet.blockPair` against a fixed sign vector of the dual principal
series of that block, and evaluates at `1` on `GL_0`. If the principal series of all tied blocks
are irreducible (`RealBlockFunctional.TiedIrreducible`), `jac` vanishes on every function
orthogonal to a nonzero `(𝔤, K)`-stable space of the dual principal series
(`RealBlockFunctional.jac_eq_zero`), hence on every proper `(𝔤, K)`-stable subspace
(`RealBlockFunctional.jac_eq_zero_of_proper`). The statements of `RealBlockLimit` and
`RealBlockJacquet` enter through `RealBlockChartIntegrableStatement` and
`RealBlockParabolicIntegrationStatement`.
-/

noncomputable section

open MeasureTheory Matrix Filter Topology

open scoped Matrix Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealBlockFunctional

open RealBlockParabolic RealBlockChart RealBlockLimit RealBlockJacquet RealBlockDual
  PartialJacquet JacquetLimit GramFormula PrincipalSeriesExtension RealPrincipalSeriesDuality
  JacquetNonvanishing JacquetKernel Langlands.GeneralLinear

attribute [local instance] measurableSpaceK

/-! ## Block decompositions -/

/-- The size `∑ (k+1)` of a block decomposition `ks` (last block first). -/
def dim : List ℕ → ℕ
  | [] => 0
  | k :: ks => dim ks + (k + 1)

/-- The exponents are tied within each block and decrease strictly between blocks. -/
def BlockOrdered : List ℕ → (ℕ → ℂ) → Prop
  | [], _ => True
  | k :: ks, e => IsBlockDominant e (dim ks) k ∧ BlockOrdered ks e

theorem BlockOrdered.shift : ∀ {ks : List ℕ} {e : ℕ → ℂ} (c : ℂ), BlockOrdered ks e →
    BlockOrdered ks (fun l => e l - c)
  | [], _, _, _ => trivial
  | _ :: _, _, c, ⟨he, hks⟩ =>
    ⟨⟨fun j hj => by simp only [Complex.sub_re, he.tie j hj],
      fun l hl => by simp only [Complex.sub_re]; linarith [he.ord l hl],
      fun l hl => by simp only [Complex.sub_re]; linarith [he.gap l hl]⟩, hks.shift c⟩

/-- Irreducibility of every principal series of signed-power characters with signs
`ψ_l(−1) = (−1)^{q_l}` and tied exponents. -/
def TiedIrreducible : Prop :=
  ∀ (b : ℕ) (ψ : ℕ → ℝˣ → ℂ) (f : ℕ → ℂ) (q : ℕ → ℕ), IsSignedPower ψ f →
    (∀ l : ℕ, ψ l (-1) = (-1) ^ q l) →
    (∀ l : ℕ, l < b → (f l).re = (f 0).re) →
    IsIrreducibleGKModule (principalSeriesRep ℝ b ψ) (principalSeriesLie ℝ b ψ)

/-! ## Characters -/

variable {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ} {p : ℕ → ℕ}

theorem isSignedPower_blockDualChar (hχ : IsSignedPower χ e) (a : ℕ) :
    IsSignedPower (blockDualChar a χ) (fun l => -(e (a + l)) - (a : ℂ) / 2) where
  eq l x := by
    have hx : ((|(x : ℝ)| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.mpr x.ne_zero
    rw [blockDualChar, blockDualChar, hχ.eq (a + l) x, abs_signUnit, Complex.ofReal_one,
      Complex.one_cpow, mul_one, mul_inv, ← Complex.cpow_neg, mul_assoc,
      ← Complex.cpow_add _ _ hx]
    congr 2
  one l := by simp [blockDualChar, hχ.one]
  norm_neg_one l := by simp [blockDualChar, hχ.norm_neg_one]

theorem blockDualChar_neg_one (hp : ∀ l : ℕ, χ l (-1) = (-1) ^ p l) (a l : ℕ) :
    blockDualChar a χ l (-1) = (-1) ^ p (a + l) := by
  rw [blockDualChar, hp]
  simp only [Units.val_neg, Units.val_one, abs_neg, abs_one, Complex.ofReal_one,
    Complex.one_cpow, mul_one]
  rcases neg_one_pow_eq_or ℂ (p (a + l)) with h | h <;> rw [h] <;> norm_num

theorem blockShiftChar_neg_one (k : ℕ) (hp : ∀ l : ℕ, χ l (-1) = (-1) ^ p l) (l : ℕ) :
    blockShiftChar k χ l (-1) = (-1) ^ p l := by
  rw [blockShiftChar, hp]
  simp only [Units.val_neg, Units.val_one, abs_neg, abs_one, Complex.ofReal_one,
    Complex.one_cpow, mul_one]

/-! ## The functional -/

/-- The sign vector of the dual principal series of the block `a, …, a+k`: exponents
`-(e_{a+l} + a/2)`, signs `p_{a+l}`. -/
def blockVector (a k : ℕ) (e : ℕ → ℂ) (p : ℕ → ℕ) : Langlands.GeneralLinear (k + 1) ℝ → ℂ :=
  signVector (k + 1) (fun l => -(e (a + l)) - (a : ℂ) / 2) (fun l => p (a + l)) 0

theorem blockVector_mem (hχ : IsSignedPower χ e) (hp : ∀ l : ℕ, χ l (-1) = (-1) ^ p l)
    (a k : ℕ) :
    blockVector a k e p ∈ kFiniteFunctions (principalSeries ℝ (k + 1) (blockDualChar a χ))
      (unitaryCompact ℝ (k + 1)) :=
  signVector_mem _ 0 (isSignedPower_blockDualChar hχ a) (blockDualChar_neg_one hp a)

/-- **The block Jacquet functional.** `jac [] h = h(1)`, and `jac (k :: ks)` applies
`blockPair` against `blockVector` for the last block and recurses with exponents shifted by
`-(k+1)/2`. -/
def jac : (ks : List ℕ) → (ℕ → ℂ) → (ℕ → ℕ) → (Langlands.GeneralLinear (dim ks) ℝ → ℂ) → ℂ
  | [], _, _, h => h 1
  | k :: ks, e, p, h => jac ks (fun l => e l - ((k : ℂ) + 1) / 2) p
      (blockPair (blockVector (dim ks) k e p) h)

theorem jac_cons (k : ℕ) (ks : List ℕ) (e : ℕ → ℂ) (p : ℕ → ℕ)
    (h : Langlands.GeneralLinear (dim ks + (k + 1)) ℝ → ℂ) :
    jac (k :: ks) e p h = jac ks (fun l => e l - ((k : ℂ) + 1) / 2) p
      (blockPair (blockVector (dim ks) k e p) h) := rfl

/-! ## Linearity -/

theorem blockPair_smul {a k : ℕ} (φ : Langlands.GeneralLinear (k + 1) ℝ → ℂ) (c : ℂ)
    (f : Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ) :
    blockPair φ (c • f) = c • blockPair φ f := by
  funext g
  simp only [blockPair, blockStep, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun κ₂ => ?_)
  simp only
  rw [integral_const_mul]
  ring

theorem blockPair_add {a k : ℕ} (hT1 : RealBlockChartIntegrableStatement)
    (hχ : IsSignedPower χ e) (he : IsBlockDominant e a k)
    {φ : Langlands.GeneralLinear (k + 1) ℝ → ℂ} (hφ : Continuous φ)
    {f g : Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ}
    (hf : f ∈ kFiniteFunctions (principalSeries ℝ (a + (k + 1)) χ)
      (unitaryCompact ℝ (a + (k + 1))))
    (hg : g ∈ kFiniteFunctions (principalSeries ℝ (a + (k + 1)) χ)
      (unitaryCompact ℝ (a + (k + 1)))) :
    blockPair φ (f + g) = blockPair φ f + blockPair φ g := by
  refine eq_of_eqOn_unitaryCompact_of_mem_principalSeries
    (blockPair_mem hT1 hχ he (add_mem hf hg) hφ).1
    (add_mem (blockPair_mem hT1 hχ he hf hφ).1 (blockPair_mem hT1 hχ he hg hφ).1) fun κ hκ => ?_
  have h := congrFun ((blockPairOn hT1 hχ he hφ
    (kFiniteFunctions (principalSeries ℝ (a + (k + 1)) χ) (unitaryCompact ℝ (a + (k + 1))))
    (fun _ h => h.1)).map_add ⟨f, hf⟩ ⟨g, hg⟩) ⟨(κ : Matrix (Fin a) (Fin a) ℝ), hκ⟩
  have hku : Unitary.toUnits (⟨(κ : Matrix (Fin a) (Fin a) ℝ), hκ⟩ :
      Matrix.unitaryGroup (Fin a) ℝ) = κ := Units.ext rfl
  simp only [blockPairOn, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_add, Pi.add_apply,
    hku] at h
  exact h

theorem jac_smul : ∀ (ks : List ℕ) (e : ℕ → ℂ) (p : ℕ → ℕ) (c : ℂ)
    (f : Langlands.GeneralLinear (dim ks) ℝ → ℂ), jac ks e p (c • f) = c * jac ks e p f
  | [], _, _, _, _ => rfl
  | k :: ks, e, p, c, f => by
    rw [jac_cons, jac_cons, blockPair_smul]
    exact jac_smul ks _ p c _

theorem jac_add (hT1 : RealBlockChartIntegrableStatement) :
    ∀ (ks : List ℕ) {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ} (p : ℕ → ℕ), IsSignedPower χ e →
    (∀ l : ℕ, χ l (-1) = (-1) ^ p l) →
    BlockOrdered ks e → ∀ {f g : Langlands.GeneralLinear (dim ks) ℝ → ℂ},
    f ∈ kFiniteFunctions (principalSeries ℝ (dim ks) χ) (unitaryCompact ℝ (dim ks)) →
    g ∈ kFiniteFunctions (principalSeries ℝ (dim ks) χ) (unitaryCompact ℝ (dim ks)) →
    jac ks e p (f + g) = jac ks e p f + jac ks e p g
  | [], _, _, _, _, _, _, _, _, _, _ => rfl
  | k :: ks, χ, e, p, hχ, hp, ⟨he, hks⟩, f, g, hf, hg => by
    have hφ : Continuous (blockVector (dim ks) k e p) :=
      (blockVector_mem hχ hp (dim ks) k).1.1.continuous
    rw [jac_cons, jac_cons, jac_cons, blockPair_add hT1 hχ he hφ hf hg]
    exact jac_add hT1 ks p (isSignedPower_blockShift hχ) (blockShiftChar_neg_one k hp)
      (hks.shift _) (blockPair_mem hT1 hχ he hf hφ) (blockPair_mem hT1 hχ he hg hφ)

/-! ## Vanishing -/

/-- **Vanishing on annihilators.** Under `TiedIrreducible` and the block statements, `jac`
vanishes on every `O(n)`-finite function of the principal series of `χ` that is orthogonal to a
nonzero `(𝔤, K)`-stable space of `O(n)`-finite functions of the principal series of `χ⁻¹`. -/
theorem jac_eq_zero (hT1 : RealBlockChartIntegrableStatement)
    (hT3 : RealBlockParabolicIntegrationStatement) (hirr : TiedIrreducible) :
    ∀ (ks : List ℕ) {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ} (p : ℕ → ℕ), IsSignedPower χ e →
    (∀ l : ℕ, χ l (-1) = (-1) ^ p l) →
    BlockOrdered ks e →
    ∀ {U : Submodule ℂ (Langlands.GeneralLinear (dim ks) ℝ → ℂ)},
    U ≤ kFiniteFunctions (principalSeries ℝ (dim ks) (dualChar χ)) (unitaryCompact ℝ (dim ks)) →
    (∀ κ ∈ unitaryCompact ℝ (dim ks), ∀ u ∈ U,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (dim ks) ℝ) κ u ∈ U) →
    (∀ (X : Matrix (Fin (dim ks)) (Fin (dim ks)) ℝ), ∀ u ∈ U,
      rightDerivative (matrixModel ℝ (dim ks)) X u ∈ U) →
    U ≠ ⊥ →
    ∀ {h : Langlands.GeneralLinear (dim ks) ℝ → ℂ},
    h ∈ kFiniteFunctions (principalSeries ℝ (dim ks) χ) (unitaryCompact ℝ (dim ks)) →
    (∀ u ∈ U, ∫ κ, u (κ : Langlands.GeneralLinear (dim ks) ℝ) * h κ ∂haarK (dim ks) = 0) →
    jac ks e p h = 0
  | [], χ, e, p, _, _, _, U, _, _, _, hU0, h, _, horth => by
      obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
      have hsub : ∀ g : Langlands.GeneralLinear (dim []) ℝ, g = 1 := fun g => by
        apply Units.ext
        ext i j
        exact i.elim0
      have hu1 : u 1 ≠ 0 := fun h1 => hu0 (funext fun g => by rw [hsub g]; exact h1)
      have hint := horth u huU
      have hconst : (fun κ : unitaryCompact ℝ (dim []) =>
          u (κ : Langlands.GeneralLinear (dim []) ℝ) * h κ) = fun _ => u 1 * h 1 :=
        funext fun κ => by rw [hsub κ]
      rw [hconst, integral_const, probReal_univ, one_smul] at hint
      exact (mul_eq_zero.mp hint).resolve_left hu1
  | k :: ks, χ, e, p, hχ, hp, ⟨he, hks⟩, U, hU, hUK, hUD, hU0, h, hh, horth => by
      have hφ := blockVector_mem hχ hp (dim ks) k
      have hirrT := hirr (k + 1) (blockDualChar (dim ks) χ)
        (fun l => -(e (dim ks + l)) - ((dim ks : ℕ) : ℂ) / 2) (fun l => p (dim ks + l))
        (isSignedPower_blockDualChar hχ (dim ks)) (blockDualChar_neg_one hp (dim ks))
        (fun l hl => by
          simp only [Complex.sub_re, Complex.neg_re, add_zero]
          rw [he.tie l (by omega)])
      obtain ⟨hUM, hUMK, hUMD, hUM0⟩ := map_restrictBlock (k := k) hχ hU hUK hUD hU0
      rw [jac_cons]
      exact jac_eq_zero hT1 hT3 hirr ks p (isSignedPower_blockShift hχ)
        (blockShiftChar_neg_one k hp) (hks.shift _) hUM hUMK hUMD hUM0
        (blockPair_mem hT1 hχ he hh hφ.1.1.continuous)
        (by
          rintro _ ⟨u, hu, rfl⟩
          exact integral_restrictBlock_mul_blockPair_eq_zero hT1 hT3 hχ he
            (χT := blockDualChar (dim ks) χ) (fun _ _ _ => rfl) hirrT hU hUK hUD hh horth
            ⟨_, hφ⟩ hu)

/-- The kernel of `jac` on the `O(n)`-finite functions of the principal series of `χ`. -/
def jacKernel (hT1 : RealBlockChartIntegrableStatement) (ks : List ℕ) (p : ℕ → ℕ)
    (hχ : IsSignedPower χ e) (hp : ∀ l : ℕ, χ l (-1) = (-1) ^ p l)
    (hks : BlockOrdered ks e) : Submodule ℂ (Langlands.GeneralLinear (dim ks) ℝ → ℂ) where
  carrier := {f | f ∈ kFiniteFunctions (principalSeries ℝ (dim ks) χ) (unitaryCompact ℝ (dim ks)) ∧
    jac ks e p f = 0}
  zero_mem' := ⟨Submodule.zero_mem _, by
    have := jac_smul ks e p 0 0
    rwa [zero_smul, zero_mul] at this⟩
  add_mem' {f g} hf hg := ⟨add_mem hf.1 hg.1, by
    rw [jac_add hT1 ks p hχ hp hks hf.1 hg.1, hf.2, hg.2, add_zero]⟩
  smul_mem' c f hf := ⟨Submodule.smul_mem _ c hf.1, by
    rw [jac_smul, hf.2, mul_zero]⟩

/-- **Proper submodules lie in the kernel of `jac`.** -/
theorem jac_eq_zero_of_proper (hT1 : RealBlockChartIntegrableStatement)
    (hT3 : RealBlockParabolicIntegrationStatement) (hirr : TiedIrreducible) {ks : List ℕ}
    (p : ℕ → ℕ) (hχ : IsSignedPower χ e) (hp : ∀ l : ℕ, χ l (-1) = (-1) ^ p l)
    (hks : BlockOrdered ks e)
    (W : Submodule ℂ (Langlands.GeneralLinear (dim ks) ℝ → ℂ))
    (hW : W ≤ kFiniteFunctions (principalSeries ℝ (dim ks) χ) (unitaryCompact ℝ (dim ks)))
    (hWK : ∀ κ ∈ unitaryCompact ℝ (dim ks), ∀ w ∈ W,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (dim ks) ℝ) κ w ∈ W)
    (hWD : ∀ (X : Matrix (Fin (dim ks)) (Fin (dim ks)) ℝ), ∀ w ∈ W,
      rightDerivative (matrixModel ℝ (dim ks)) X w ∈ W)
    {f : Langlands.GeneralLinear (dim ks) ℝ → ℂ}
    (hf : f ∈ kFiniteFunctions (principalSeries ℝ (dim ks) χ) (unitaryCompact ℝ (dim ks)))
    (hfW : f ∉ W) : W ≤ jacKernel hT1 ks p hχ hp hks := fun w hw =>
  ⟨hW hw, jac_eq_zero hT1 hT3 hirr ks p hχ hp hks (annihilator_le W hW)
    (annihilator_rightTranslation W hW hWK) (annihilator_rightDerivative hχ W hW hWD)
    (annihilator_ne_bot hχ W hW hWK hf hfW) (hW hw) fun _ hu => hu.2 w hw⟩

end RealBlockFunctional

/-- **Proper submodules lie in the kernel of the block Jacquet functional** (assuming
`RealBlockChartIntegrableStatement`, `RealBlockParabolicIntegrationStatement` and
`RealBlockFunctional.TiedIrreducible`). Let `ks` be a block decomposition of
`n = RealBlockFunctional.dim ks` and `χ` characters with `χ_l(x) = χ_l(sgn x) |x|^{e_l}`,
`χ_l(1) = 1` and `χ_l(−1) = (−1)^{p_l}`, such that the exponents are tied within each block and
strictly decrease between consecutive blocks (`RealBlockFunctional.BlockOrdered ks e`). Let `W`
be a subspace of the `O(n)`-finite functions of the principal series of `χ`, stable under right
translation by `O(n)` and right derivatives, and proper. Then the block Jacquet functional
`RealBlockFunctional.jac ks e p` vanishes on `W`. -/
def RealBlockFunctionalStatement : Prop :=
  RealBlockChartIntegrableStatement → RealBlockParabolicIntegrationStatement →
  RealBlockFunctional.TiedIrreducible →
  ∀ (ks : List ℕ) (χ : ℕ → ℝˣ → ℂ) (e : ℕ → ℂ) (p : ℕ → ℕ),
    (∀ (l : ℕ) (x : ℝˣ), χ l x =
      χ l (GramFormula.signUnit x) * ((|(x : ℝ)| : ℝ) : ℂ) ^ e l) →
    (∀ l : ℕ, χ l 1 = 1) →
    (∀ l : ℕ, χ l (-1) = (-1) ^ p l) →
    RealBlockFunctional.BlockOrdered ks e →
    ∀ W : Submodule ℂ (Langlands.GeneralLinear (RealBlockFunctional.dim ks) ℝ → ℂ),
    W ≤ kFiniteFunctions (principalSeries ℝ (RealBlockFunctional.dim ks) χ)
      (unitaryCompact ℝ (RealBlockFunctional.dim ks)) →
    (∀ κ ∈ unitaryCompact ℝ (RealBlockFunctional.dim ks), ∀ w ∈ W,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (RealBlockFunctional.dim ks) ℝ)
        κ w ∈ W) →
    (∀ (X : Matrix (Fin (RealBlockFunctional.dim ks)) (Fin (RealBlockFunctional.dim ks)) ℝ),
      ∀ w ∈ W, rightDerivative (matrixModel ℝ (RealBlockFunctional.dim ks)) X w ∈ W) →
    (∃ f ∈ kFiniteFunctions (principalSeries ℝ (RealBlockFunctional.dim ks) χ)
      (unitaryCompact ℝ (RealBlockFunctional.dim ks)), f ∉ W) →
    ∀ w ∈ W, RealBlockFunctional.jac ks e p w = 0

theorem realBlockFunctional : RealBlockFunctionalStatement := by
  intro hT1 hT3 hirr ks χ e p heq hone hp hks W hW hWK hWD ⟨f, hf, hfW⟩ w hw
  have hχ : PartialJacquet.IsSignedPower χ e :=
    ⟨heq, hone, fun l => by rw [hp, norm_pow, norm_neg, norm_one, one_pow]⟩
  exact (RealBlockFunctional.jac_eq_zero_of_proper hT1 hT3 hirr p hχ hp hks W hW hWK hWD hf
    hfW hw).2

end Langlands.Archimedean
