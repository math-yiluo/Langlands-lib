import Langlands.Representation.Archimedean.ComplexBlockLanglandsQuotient
import Langlands.Representation.Archimedean.ComplexBlockChartIntegralProof
import Langlands.Representation.Archimedean.ComplexBlockParabolicIntegrationProof

/-!
# The block Jacquet functional with irreducibility only at the block sizes

`ComplexBlockFunctional.jac_eq_zero_of_proper` assumes `ComplexBlockFunctional.TiedIrreducible`:
the irreducibility of tied principal series of every size. Its proof uses this only at the sizes
`k + 1` of the blocks `k ∈ ks`. This module records that refinement.

* `ComplexBlockFunctionalSized.TiedIrreducibleAt b`: `TiedIrreducible` at the single size `b`.
* `ComplexBlockFunctionalSized.TemperedIrreducibleAt b`:
  `ComplexTemperedStandardIrreducibleStatement` at the single size `b`.
* `ComplexBlockFunctionalSized.jac_eq_zero_of_proper_sized`: the block Jacquet functional
  `ComplexBlockFunctional.jac ks e p` vanishes on every proper `(𝔤, K)`-stable subspace,
  assuming `TiedIrreducibleAt (k + 1)` for every `k ∈ ks` only.

`ComplexBlockFunctionalSizedStatement` states the result with the integration statements
discharged by `complexBlockChartIntegrable` and `complexBlockParabolicIntegration`, and with
`TemperedIrreducibleAt (k + 1)` for the blocks `k ∈ ks` as the only hypothesis on
irreducibility.
-/

noncomputable section

open MeasureTheory Matrix Filter Topology

open scoped Matrix TensorProduct Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

namespace ComplexBlockFunctionalSized

open ComplexBlockJacquet ComplexBlockFunctional ComplexBlockDual ComplexBlockLanglandsQuotient
  ComplexPartialJacquet ComplexGramFormula ComplexDuality ComplexJacquetKernel
  Langlands.LocalFactor.Archimedean

/-! ## Irreducibility at a single size -/

/-- `ComplexBlockFunctional.TiedIrreducible` at the single size `b`: every principal series of
`GL_b(ℂ)` of phase-power characters `ψ` with exponents `f`, integral phase weights `q`, and
`Re f_l = Re f_0` for `l < b`, is irreducible. -/
def TiedIrreducibleAt (b : ℕ) : Prop :=
  ∀ (ψ : ℕ → ℂˣ → ℂ) (f : ℕ → ℂ) (q : ℕ → ℤ), IsPhasePower ψ f →
    (∀ (l : ℕ) (z : ℂˣ), ψ l (phaseUnit z) = ((phaseUnit z : ℂˣ) : ℂ) ^ (q l)) →
    (∀ l : ℕ, l < b → (f l).re = (f 0).re) →
    IsIrreducibleGKModule (principalSeriesRep ℂ b ψ) (principalSeriesLie ℂ b ψ)

theorem tiedIrreducible_iff : TiedIrreducible ↔ ∀ b, TiedIrreducibleAt b :=
  Iff.rfl

/-- `ComplexTemperedStandardIrreducibleStatement` at the single size `b`. -/
def TemperedIrreducibleAt (b : ℕ) : Prop :=
  ∀ ds : List ComplexCharacterData, ds.length = b →
    (∀ d ∈ ds, ∀ e ∈ ds, d.exponent.re = e.exponent.re) →
      IsIrreducibleGKModule (complexStandardRep b ds) (complexStandardLie b ds)

theorem temperedIrreducibleAt_of (hU : ComplexTemperedStandardIrreducibleStatement) (b : ℕ) :
    TemperedIrreducibleAt b :=
  hU b

/-- The tempered statement at size `b` gives `TiedIrreducibleAt b`, through the list of
characters with parameters `(q_i, f_i)` (as in `ComplexBlockLanglandsQuotient.tiedIrreducible`). -/
theorem tiedIrreducibleAt_of {b : ℕ} (hU : TemperedIrreducibleAt b) : TiedIrreducibleAt b := by
  intro ψ f q hψ hq htie
  set ds : List ComplexCharacterData := List.ofFn fun i : Fin b => characterOfParams (q i) (f i)
    with hds
  have hlen : ds.length = b := List.length_ofFn
  have hexp : ∀ d ∈ ds, ∀ d' ∈ ds, d.exponent.re = d'.exponent.re := by
    intro d hd d' hd'
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
    obtain ⟨i', rfl⟩ := List.mem_ofFn.mp hd'
    simp only [characterOfParams_exponent]
    rw [htie i i.isLt, htie i' i'.isLt]
  have h := hU ds hlen hexp
  exact isIrreducible_kFinite_congr
    (principalSeries_congr fun j z => complexPositionCharacter_ofFn_params hψ hq j z)
    _ _ _ _ _ _ h

/-! ## Vanishing with irreducibility at the block sizes -/

/-- `ComplexBlockFunctional.jac_eq_zero` with `TiedIrreducibleAt (k + 1)` for the blocks
`k ∈ ks` in place of `TiedIrreducible`. The proof is the same induction on `ks`. -/
theorem jac_eq_zero_sized (hT1 : ComplexBlockChartIntegrableStatement)
    (hT3 : ComplexBlockParabolicIntegrationStatement) :
    ∀ (ks : List ℕ), (∀ k ∈ ks, TiedIrreducibleAt (k + 1)) →
    ∀ {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ} (p : ℕ → ℤ), IsPhasePower χ e →
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
  | [], _, χ, e, p, _, _, _, U, _, _, _, hU0, h, _, horth => by
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
  | k :: ks, hirr, χ, e, p, hχ, hp, ⟨he, hks⟩, U, hU, hUK, hUD, hU0, h, hh, horth => by
      have hφ := blockVector_mem hχ hp (dim ks) k
      have hirrT := hirr k List.mem_cons_self (blockDualChar (dim ks) χ)
        (fun l => -(e (dim ks + l)) - ((dim ks : ℕ) : ℂ) / 2) (fun l => -(p (dim ks + l)))
        (isPhasePower_blockDualChar hχ (dim ks)) (blockDualChar_phase hp (dim ks))
        (fun l hl => by
          simp only [Complex.sub_re, Complex.neg_re, add_zero]
          rw [he.tie l (by omega)])
      obtain ⟨hUM, hUMK, hUMD, hUM0⟩ := map_restrictBlock (k := k) hχ hU hUK hUD hU0
      rw [jac_cons]
      exact jac_eq_zero_sized hT1 hT3 ks (fun k' hk' => hirr k' (List.mem_cons_of_mem _ hk')) p
        (isPhasePower_blockShift hχ) (blockShiftChar_phase k hp)
        (hks.shift _) hUM hUMK hUMD hUM0 (blockPair_mem hT1 hχ he hh hφ.1.1.continuous)
        (by
          rintro _ ⟨u, hu, rfl⟩
          exact integral_restrictBlock_mul_blockPair_eq_zero hT1 hT3 hχ he
            (χT := blockDualChar (dim ks) χ) (fun _ _ _ => rfl) hirrT hU hUK hUD hh horth
            ⟨_, hφ⟩ hu)

variable {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ}

/-- **Proper submodules lie in the kernel of `jac`**, assuming irreducibility only at the block
sizes. -/
theorem jac_eq_zero_of_proper_sized (hT1 : ComplexBlockChartIntegrableStatement)
    (hT3 : ComplexBlockParabolicIntegrationStatement) {ks : List ℕ}
    (hirr : ∀ k ∈ ks, TiedIrreducibleAt (k + 1))
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
  ⟨hW hw, jac_eq_zero_sized hT1 hT3 ks hirr p hχ hp hks (annihilator_le W hW)
    (annihilator_rightTranslation W hW hWK) (annihilator_rightDerivative hχ W hW hWD)
    (annihilator_ne_bot hχ W hW hWK hf hfW) (hW hw) fun _ hu => hu.2 w hw⟩

end ComplexBlockFunctionalSized

/-- **Proper submodules lie in the kernel of the block Jacquet functional, with irreducibility
only at the block sizes.** Let `ks` be a block decomposition of
`n = ComplexBlockFunctional.dim ks` (block sizes `k + 1`), and let `χ` be phase-power characters
with exponents `e` (`χ_l(z) = χ_l(z/|z|)(|z|²)^{e_l}`, `χ_l(1) = 1`) and `χ_l(u) = u^{p_l}` on the
unit circle. Suppose the exponents are tied within each block and strictly decrease between
consecutive blocks (`ComplexBlockFunctional.BlockOrdered ks e`). Suppose also that for every block
`k ∈ ks`, the complex standard modules of size `k + 1` whose exponents have equal real parts
are irreducible (`ComplexBlockFunctionalSized.TemperedIrreducibleAt (k + 1)`). Let `W` be a
proper subspace of the `U(n)`-finite functions of the principal series of `χ`, stable under
right translation by `U(n)` and right derivatives. Then the block Jacquet functional
`ComplexBlockFunctional.jac ks e p` vanishes on `W`. -/
def ComplexBlockFunctionalSizedStatement : Prop :=
  ∀ (ks : List ℕ), (∀ k ∈ ks, ComplexBlockFunctionalSized.TemperedIrreducibleAt (k + 1)) →
  ∀ (χ : ℕ → ℂˣ → ℂ) (e : ℕ → ℂ) (p : ℕ → ℤ),
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

theorem complexBlockFunctionalSized : ComplexBlockFunctionalSizedStatement := by
  intro ks hU χ e p heq hone hp hks W hW hWK hWD ⟨f, hf, hfW⟩ w hw
  have hχ : ComplexPartialJacquet.IsPhasePower χ e :=
    ⟨heq, hone, fun l z => by rw [hp, norm_zpow, ComplexGramFormula.norm_phaseUnit,
      _root_.one_zpow]⟩
  exact (ComplexBlockFunctionalSized.jac_eq_zero_of_proper_sized complexBlockChartIntegrable
    complexBlockParabolicIntegration
    (fun k hk => ComplexBlockFunctionalSized.tiedIrreducibleAt_of (hU k hk)) p hχ hp hks W hW hWK
    hWD hf hfW hw).2

end Langlands.Archimedean
