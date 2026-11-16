import Langlands.Representation.Archimedean.ComplexBlockDual
import Langlands.Representation.Archimedean.ComplexJacquetNonvanishing
import Langlands.Representation.Archimedean.ComplexJacquetKernel

/-!
# The block Jacquet functional and its vanishing on proper submodules

For a decomposition of `n` into consecutive blocks (`ks`, block sizes `k+1`, last block first)
such that the exponents are tied within each block and strictly decrease between blocks
(`ComplexBlockFunctional.BlockOrdered`), the functional `ComplexBlockFunctional.jac` peels off the
last block with `ComplexBlockJacquet.blockPair` against a fixed phase vector of the dual principal
series of that block, and evaluates at `1` on `GL_0`. If the principal series of all tied blocks
are irreducible (`ComplexBlockFunctional.TiedIrreducible`), `jac` vanishes on every function
orthogonal to a nonzero `(𝔤, K)`-stable space of the dual principal series
(`ComplexBlockFunctional.jac_eq_zero`), hence on every proper `(𝔤, K)`-stable subspace
(`ComplexBlockFunctional.jac_eq_zero_of_proper`). The statements of `ComplexBlockLimit` and
`ComplexBlockJacquet` enter through `ComplexBlockChartIntegrableStatement` and
`ComplexBlockParabolicIntegrationStatement`.
-/

noncomputable section

open MeasureTheory Matrix Filter Topology

open scoped Matrix ComplexOrder Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

namespace ComplexBlockFunctional

open ComplexBlockParabolic ComplexBlockChart ComplexBlockLimit ComplexBlockJacquet ComplexBlockDual
  ComplexPartialJacquet ComplexJacquetLimit ComplexGramFormula ComplexPrincipalSeriesExtension
  ComplexDuality ComplexJacquetNonvanishing ComplexJacquetKernel Langlands.GeneralLinear

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

/-- Irreducibility of every principal series of phase-power characters with tied exponents. -/
def TiedIrreducible : Prop :=
  ∀ (b : ℕ) (ψ : ℕ → ℂˣ → ℂ) (f : ℕ → ℂ) (q : ℕ → ℤ), IsPhasePower ψ f →
    (∀ (l : ℕ) (z : ℂˣ), ψ l (phaseUnit z) = ((phaseUnit z : ℂˣ) : ℂ) ^ (q l)) →
    (∀ l : ℕ, l < b → (f l).re = (f 0).re) →
    IsIrreducibleGKModule (principalSeriesRep ℂ b ψ) (principalSeriesLie ℂ b ψ)

/-! ## Characters -/

variable {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ} {p : ℕ → ℤ}

theorem isPhasePower_blockDualChar (hχ : IsPhasePower χ e) (a : ℕ) :
    IsPhasePower (blockDualChar a χ) (fun l => -(e (a + l)) - (a : ℂ) / 2) where
  eq l z := by
    have hz : ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr z.ne_zero)
    rw [blockDualChar, blockDualChar, hχ.eq (a + l) z, norm_phaseUnit, one_pow,
      Complex.ofReal_one, Complex.one_cpow, mul_one, mul_inv, ← Complex.cpow_neg, mul_assoc,
      ← Complex.cpow_add _ _ hz]
    congr 2
  one l := by simp [blockDualChar, hχ.one]
  norm_phase l z := by simp [blockDualChar, hχ.norm_phase, norm_phaseUnit]

theorem blockDualChar_phase
    (hp : ∀ (l : ℕ) (z : ℂˣ), χ l (phaseUnit z) = ((phaseUnit z : ℂˣ) : ℂ) ^ (p l)) (a : ℕ)
    (l : ℕ) (z : ℂˣ) :
    blockDualChar a χ l (phaseUnit z) = ((phaseUnit z : ℂˣ) : ℂ) ^ (-(p (a + l))) := by
  rw [blockDualChar, hp, norm_phaseUnit, one_pow, Complex.ofReal_one, Complex.one_cpow, mul_one,
    _root_.zpow_neg]

theorem blockShiftChar_phase (k : ℕ)
    (hp : ∀ (l : ℕ) (z : ℂˣ), χ l (phaseUnit z) = ((phaseUnit z : ℂˣ) : ℂ) ^ (p l)) (l : ℕ)
    (z : ℂˣ) : blockShiftChar k χ l (phaseUnit z) = ((phaseUnit z : ℂˣ) : ℂ) ^ (p l) := by
  rw [blockShiftChar, hp, norm_phaseUnit, one_pow, Complex.ofReal_one, Complex.one_cpow, mul_one]

/-! ## The functional -/

/-- The phase vector of the dual principal series of the block `a, …, a+k`: exponents
`-(e_{a+l} + a/2)`, weights `-p_{a+l}`. -/
def blockVector (a k : ℕ) (e : ℕ → ℂ) (p : ℕ → ℤ) : Langlands.GeneralLinear (k + 1) ℂ → ℂ :=
  phaseVector (k + 1) (fun l => -(e (a + l)) - (a : ℂ) / 2) (fun l => -(p (a + l))) 0

theorem blockVector_mem (hχ : IsPhasePower χ e)
    (hp : ∀ (l : ℕ) (z : ℂˣ), χ l (phaseUnit z) = ((phaseUnit z : ℂˣ) : ℂ) ^ (p l)) (a k : ℕ) :
    blockVector a k e p ∈ kFiniteFunctions (principalSeries ℂ (k + 1) (blockDualChar a χ))
      (unitaryCompact ℂ (k + 1)) :=
  phaseVector_mem _ 0 (isPhasePower_blockDualChar hχ a) (blockDualChar_phase hp a)

/-- **The block Jacquet functional.** `jac [] h = h(1)`, and `jac (k :: ks)` applies
`blockPair` against `blockVector` for the last block and recurses with exponents shifted by
`-(k+1)/2`. -/
def jac : (ks : List ℕ) → (ℕ → ℂ) → (ℕ → ℤ) → (Langlands.GeneralLinear (dim ks) ℂ → ℂ) → ℂ
  | [], _, _, h => h 1
  | k :: ks, e, p, h => jac ks (fun l => e l - ((k : ℂ) + 1) / 2) p
      (blockPair (blockVector (dim ks) k e p) h)

theorem jac_cons (k : ℕ) (ks : List ℕ) (e : ℕ → ℂ) (p : ℕ → ℤ)
    (h : Langlands.GeneralLinear (dim ks + (k + 1)) ℂ → ℂ) :
    jac (k :: ks) e p h = jac ks (fun l => e l - ((k : ℂ) + 1) / 2) p
      (blockPair (blockVector (dim ks) k e p) h) := rfl

/-! ## Linearity -/

theorem blockPair_smul {a k : ℕ} (φ : Langlands.GeneralLinear (k + 1) ℂ → ℂ) (c : ℂ)
    (f : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ) :
    blockPair φ (c • f) = c • blockPair φ f := by
  funext g
  simp only [blockPair, blockStep, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun κ₂ => ?_)
  simp only
  rw [integral_const_mul]
  ring

theorem blockPair_add {a k : ℕ} (hT1 : ComplexBlockChartIntegrableStatement)
    (hχ : IsPhasePower χ e) (he : IsBlockDominant e a k)
    {φ : Langlands.GeneralLinear (k + 1) ℂ → ℂ} (hφ : Continuous φ)
    {f g : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}
    (hf : f ∈ kFiniteFunctions (principalSeries ℂ (a + (k + 1)) χ) (unitaryCompact ℂ (a + (k + 1))))
    (hg : g ∈ kFiniteFunctions (principalSeries ℂ (a + (k + 1)) χ) (unitaryCompact ℂ (a + (k + 1)))) :
    blockPair φ (f + g) = blockPair φ f + blockPair φ g := by
  refine eq_of_eqOn_unitary (blockPair_mem hT1 hχ he (add_mem hf hg) hφ).1
    (add_mem (blockPair_mem hT1 hχ he hf hφ).1 (blockPair_mem hT1 hχ he hg hφ).1) fun κ hκ => ?_
  have h := congrFun ((blockPairOn hT1 hχ he hφ
    (kFiniteFunctions (principalSeries ℂ (a + (k + 1)) χ) (unitaryCompact ℂ (a + (k + 1))))
    (fun _ h => h.1)).map_add ⟨f, hf⟩ ⟨g, hg⟩) ⟨(κ : Matrix (Fin a) (Fin a) ℂ), hκ⟩
  have hku : Unitary.toUnits (⟨(κ : Matrix (Fin a) (Fin a) ℂ), hκ⟩ :
      Matrix.unitaryGroup (Fin a) ℂ) = κ := Units.ext rfl
  simp only [blockPairOn, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_add, Pi.add_apply,
    hku] at h
  exact h

theorem jac_smul : ∀ (ks : List ℕ) (e : ℕ → ℂ) (p : ℕ → ℤ) (c : ℂ)
    (f : Langlands.GeneralLinear (dim ks) ℂ → ℂ), jac ks e p (c • f) = c * jac ks e p f
  | [], _, _, _, _ => rfl
  | k :: ks, e, p, c, f => by
    rw [jac_cons, jac_cons, blockPair_smul]
    exact jac_smul ks _ p c _

theorem jac_add (hT1 : ComplexBlockChartIntegrableStatement) :
    ∀ (ks : List ℕ) {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ} (p : ℕ → ℤ), IsPhasePower χ e →
    (∀ (l : ℕ) (z : ℂˣ), χ l (phaseUnit z) = ((phaseUnit z : ℂˣ) : ℂ) ^ (p l)) →
    BlockOrdered ks e → ∀ {f g : Langlands.GeneralLinear (dim ks) ℂ → ℂ},
    f ∈ kFiniteFunctions (principalSeries ℂ (dim ks) χ) (unitaryCompact ℂ (dim ks)) →
    g ∈ kFiniteFunctions (principalSeries ℂ (dim ks) χ) (unitaryCompact ℂ (dim ks)) →
    jac ks e p (f + g) = jac ks e p f + jac ks e p g
  | [], _, _, _, _, _, _, _, _, _, _ => rfl
  | k :: ks, χ, e, p, hχ, hp, ⟨he, hks⟩, f, g, hf, hg => by
    have hφ : Continuous (blockVector (dim ks) k e p) :=
      (blockVector_mem hχ hp (dim ks) k).1.1.continuous
    rw [jac_cons, jac_cons, jac_cons, blockPair_add hT1 hχ he hφ hf hg]
    exact jac_add hT1 ks p (isPhasePower_blockShift hχ) (blockShiftChar_phase k hp)
      (hks.shift _) (blockPair_mem hT1 hχ he hf hφ) (blockPair_mem hT1 hχ he hg hφ)

/-! ## Vanishing -/

/-- **Vanishing on annihilators.** Under `TiedIrreducible` and the block statements, `jac`
vanishes on every `U(n)`-finite function of the principal series of `χ` that is orthogonal to a
nonzero `(𝔤, K)`-stable space of `U(n)`-finite functions of the principal series of `χ⁻¹`. -/
theorem jac_eq_zero (hT1 : ComplexBlockChartIntegrableStatement)
    (hT3 : ComplexBlockParabolicIntegrationStatement) (hirr : TiedIrreducible) :
    ∀ (ks : List ℕ) {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ} (p : ℕ → ℤ), IsPhasePower χ e →
    (∀ (l : ℕ) (z : ℂˣ), χ l (phaseUnit z) = ((phaseUnit z : ℂˣ) : ℂ) ^ (p l)) →
    BlockOrdered ks e →
    ∀ {U : Submodule ℂ (Langlands.GeneralLinear (dim ks) ℂ → ℂ)},
    U ≤ kFiniteFunctions (principalSeries ℂ (dim ks) (dualChar χ)) (unitaryCompact ℂ (dim ks)) →
    (∀ κ ∈ unitaryCompact ℂ (dim ks), ∀ u ∈ U,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (dim ks) ℂ) κ u ∈ U) →
    (∀ (X : Matrix (Fin (dim ks)) (Fin (dim ks)) ℂ), ∀ u ∈ U,
      rightDerivative (matrixModel ℂ (dim ks)) X u ∈ U) →
    U ≠ ⊥ →
    ∀ {h : Langlands.GeneralLinear (dim ks) ℂ → ℂ},
    h ∈ kFiniteFunctions (principalSeries ℂ (dim ks) χ) (unitaryCompact ℂ (dim ks)) →
    (∀ u ∈ U, ∫ κ, u (κ : Langlands.GeneralLinear (dim ks) ℂ) * h κ ∂unitaryHaar (dim ks) = 0) →
    jac ks e p h = 0
  | [], χ, e, p, _, _, _, U, _, _, _, hU0, h, _, horth => by
      obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
      have hsub : ∀ g : Langlands.GeneralLinear (dim []) ℂ, g = 1 := fun g => by
        apply Units.ext
        ext i j
        exact i.elim0
      have hu1 : u 1 ≠ 0 := fun h1 => hu0 (funext fun g => by rw [hsub g]; exact h1)
      have hint := horth u huU
      have hconst : (fun κ : unitaryCompact ℂ (dim []) =>
          u (κ : Langlands.GeneralLinear (dim []) ℂ) * h κ) = fun _ => u 1 * h 1 :=
        funext fun κ => by rw [hsub κ]
      rw [hconst, integral_const, probReal_univ, one_smul] at hint
      exact (mul_eq_zero.mp hint).resolve_left hu1
  | k :: ks, χ, e, p, hχ, hp, ⟨he, hks⟩, U, hU, hUK, hUD, hU0, h, hh, horth => by
      have hφ := blockVector_mem hχ hp (dim ks) k
      have hirrT := hirr (k + 1) (blockDualChar (dim ks) χ)
        (fun l => -(e (dim ks + l)) - ((dim ks : ℕ) : ℂ) / 2) (fun l => -(p (dim ks + l)))
        (isPhasePower_blockDualChar hχ (dim ks)) (blockDualChar_phase hp (dim ks))
        (fun l hl => by
          simp only [Complex.sub_re, Complex.neg_re, add_zero]
          rw [he.tie l (by omega)])
      obtain ⟨hUM, hUMK, hUMD, hUM0⟩ := map_restrictBlock (k := k) hχ hU hUK hUD hU0
      rw [jac_cons]
      exact jac_eq_zero hT1 hT3 hirr ks p (isPhasePower_blockShift hχ) (blockShiftChar_phase k hp)
        (hks.shift _) hUM hUMK hUMD hUM0 (blockPair_mem hT1 hχ he hh hφ.1.1.continuous)
        (by
          rintro _ ⟨u, hu, rfl⟩
          exact integral_restrictBlock_mul_blockPair_eq_zero hT1 hT3 hχ he
            (χT := blockDualChar (dim ks) χ) (fun _ _ _ => rfl) hirrT hU hUK hUD hh horth
            ⟨_, hφ⟩ hu)

/-- The kernel of `jac` on the `U(n)`-finite functions of the principal series of `χ`. -/
def jacKernel (hT1 : ComplexBlockChartIntegrableStatement) (ks : List ℕ) (p : ℕ → ℤ)
    (hχ : IsPhasePower χ e)
    (hp : ∀ (l : ℕ) (z : ℂˣ), χ l (phaseUnit z) = ((phaseUnit z : ℂˣ) : ℂ) ^ (p l))
    (hks : BlockOrdered ks e) : Submodule ℂ (Langlands.GeneralLinear (dim ks) ℂ → ℂ) where
  carrier := {f | f ∈ kFiniteFunctions (principalSeries ℂ (dim ks) χ) (unitaryCompact ℂ (dim ks)) ∧
    jac ks e p f = 0}
  zero_mem' := ⟨Submodule.zero_mem _, by
    have := jac_smul ks e p 0 0
    rwa [zero_smul, zero_mul] at this⟩
  add_mem' {f g} hf hg := ⟨add_mem hf.1 hg.1, by
    rw [jac_add hT1 ks p hχ hp hks hf.1 hg.1, hf.2, hg.2, add_zero]⟩
  smul_mem' c f hf := ⟨Submodule.smul_mem _ c hf.1, by
    rw [jac_smul, hf.2, mul_zero]⟩

/-- **Proper submodules lie in the kernel of `jac`.** -/
theorem jac_eq_zero_of_proper (hT1 : ComplexBlockChartIntegrableStatement)
    (hT3 : ComplexBlockParabolicIntegrationStatement) (hirr : TiedIrreducible) {ks : List ℕ}
    (p : ℕ → ℤ) (hχ : IsPhasePower χ e)
    (hp : ∀ (l : ℕ) (z : ℂˣ), χ l (phaseUnit z) = ((phaseUnit z : ℂˣ) : ℂ) ^ (p l))
    (hks : BlockOrdered ks e)
    (W : Submodule ℂ (Langlands.GeneralLinear (dim ks) ℂ → ℂ))
    (hW : W ≤ kFiniteFunctions (principalSeries ℂ (dim ks) χ) (unitaryCompact ℂ (dim ks)))
    (hWK : ∀ κ ∈ unitaryCompact ℂ (dim ks), ∀ w ∈ W,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (dim ks) ℂ) κ w ∈ W)
    (hWD : ∀ (X : Matrix (Fin (dim ks)) (Fin (dim ks)) ℂ), ∀ w ∈ W,
      rightDerivative (matrixModel ℂ (dim ks)) X w ∈ W)
    {f : Langlands.GeneralLinear (dim ks) ℂ → ℂ}
    (hf : f ∈ kFiniteFunctions (principalSeries ℂ (dim ks) χ) (unitaryCompact ℂ (dim ks)))
    (hfW : f ∉ W) : W ≤ jacKernel hT1 ks p hχ hp hks := fun w hw =>
  ⟨hW hw, jac_eq_zero hT1 hT3 hirr ks p hχ hp hks (annihilator_le W hW)
    (annihilator_rightTranslation W hW hWK) (annihilator_rightDerivative hχ W hW hWD)
    (annihilator_ne_bot hχ W hW hWK hf hfW) (hW hw) fun _ hu => hu.2 w hw⟩

end ComplexBlockFunctional

open ComplexDuality in
/-- **Proper submodules lie in the kernel of the block Jacquet functional** (assuming
`ComplexBlockChartIntegrableStatement`, `ComplexBlockParabolicIntegrationStatement` and
`ComplexBlockFunctional.TiedIrreducible`). Let `ks` be a block decomposition of
`n = ComplexBlockFunctional.dim ks` and `χ` phase-power characters with exponents `e`, with
`χ_l(u) = u^{p_l}` on the unit circle, such that the exponents are tied within each block and
strictly decrease between consecutive blocks (`ComplexBlockFunctional.BlockOrdered ks e`). Let `W`
be a subspace of the `U(n)`-finite functions of the principal series of `χ`, stable under right
translation by `U(n)` and right derivatives, and proper. Then the block Jacquet functional
`ComplexBlockFunctional.jac ks e p` vanishes on `W`. -/
def ComplexBlockFunctionalStatement : Prop :=
  ComplexBlockChartIntegrableStatement → ComplexBlockParabolicIntegrationStatement →
  ComplexBlockFunctional.TiedIrreducible →
  ∀ (ks : List ℕ) (χ : ℕ → ℂˣ → ℂ) (e : ℕ → ℂ) (p : ℕ → ℤ),
    (∀ (l : ℕ) (z : ℂˣ), χ l z =
      χ l (ComplexGramFormula.phaseUnit z) * ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ e l) →
    (∀ l : ℕ, χ l 1 = 1) →
    (∀ (l : ℕ) (z : ℂˣ), χ l (ComplexGramFormula.phaseUnit z) =
      ((ComplexGramFormula.phaseUnit z : ℂˣ) : ℂ) ^ (p l)) →
    ComplexBlockFunctional.BlockOrdered ks e →
    ∀ W : Submodule ℂ (Langlands.GeneralLinear (ComplexBlockFunctional.dim ks) ℂ → ℂ),
    W ≤ kFiniteFunctions (principalSeries ℂ (ComplexBlockFunctional.dim ks) χ)
      (unitaryCompact ℂ (ComplexBlockFunctional.dim ks)) →
    (∀ κ ∈ unitaryCompact ℂ (ComplexBlockFunctional.dim ks), ∀ w ∈ W,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (ComplexBlockFunctional.dim ks) ℂ)
        κ w ∈ W) →
    (∀ (X : Matrix (Fin (ComplexBlockFunctional.dim ks)) (Fin (ComplexBlockFunctional.dim ks)) ℂ),
      ∀ w ∈ W, rightDerivative (matrixModel ℂ (ComplexBlockFunctional.dim ks)) X w ∈ W) →
    (∃ f ∈ kFiniteFunctions (principalSeries ℂ (ComplexBlockFunctional.dim ks) χ)
      (unitaryCompact ℂ (ComplexBlockFunctional.dim ks)), f ∉ W) →
    ∀ w ∈ W, ComplexBlockFunctional.jac ks e p w = 0

theorem complexBlockFunctional : ComplexBlockFunctionalStatement := by
  intro hT1 hT3 hirr ks χ e p heq hone hp hks W hW hWK hWD ⟨f, hf, hfW⟩ w hw
  have hχ : ComplexPartialJacquet.IsPhasePower χ e :=
    ⟨heq, hone, fun l z => by rw [hp, norm_zpow, ComplexGramFormula.norm_phaseUnit,
      _root_.one_zpow]⟩
  exact (ComplexBlockFunctional.jac_eq_zero_of_proper hT1 hT3 hirr p hχ hp hks W hW hWK hWD hf
    hfW hw).2

end Langlands.Archimedean
