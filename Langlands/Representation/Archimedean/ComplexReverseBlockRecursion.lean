import Langlands.Representation.Archimedean.ComplexBlockLimitSum
import Langlands.Representation.Archimedean.ComplexBlockSlice
import Langlands.Representation.Archimedean.ComplexBlockFunctional
import Langlands.Representation.Archimedean.ComplexReverseTwist

/-!
# Transposed matrix coefficients and the block Jacquet functional

Write `M_{x,y}(g) = ∫_{U(n)} x(κ g) y(κ) dκ`. Let `ks` be a block decomposition with tied blocks
(`ComplexBlockFunctional.BlockOrdered`), `U` a `(𝔤, K)`-stable space of `U(n)`-finite functions of
the principal series of `χ⁻¹`, and `y` a `U(n)`-finite function of the principal series of `χ`.
Assume that for every `x ∈ U` the coefficient `M_{x,y}(g)` equals a finite sum
`∑_i M_{α_i,β_i}(gᵀ)` of transposed matrix coefficients in which every `β_i` is orthogonal to a
nonzero `(𝔤, K)`-stable space of the dual principal series (`HasTransposeExpansion`). Then
`x(1) · jac(y) = 0` for every `x ∈ U` (`ComplexReverseBlockRecursion.mul_jac_eq_zero`), where `jac`
is the block Jacquet functional `ComplexBlockFunctional.jac`.
-/

noncomputable section

open MeasureTheory Matrix Filter Topology

open scoped Matrix ComplexOrder Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

namespace ComplexReverseBlockRecursion

open ComplexBlockParabolic ComplexBlockChart ComplexBlockLimit ComplexBlockJacquet ComplexBlockDual
  ComplexBlockFunctional ComplexBlockLimitSum ComplexBlockSlice ComplexPartialJacquet
  ComplexJacquetLimit ComplexGramFormula ComplexDuality Langlands.GeneralLinear ComplexReverseTwist

/-! ## Matrix coefficients and the hypothesis of the recursion -/

/-- The matrix coefficient `M_{x,y}(g) = ∫_{U(n)} x(κ g) y(κ) dκ`. -/
def coeff {n : ℕ} (x y : Langlands.GeneralLinear n ℂ → ℂ) (g : Langlands.GeneralLinear n ℂ) : ℂ :=
  ∫ κ : unitaryCompact ℂ n, x ((κ : Langlands.GeneralLinear n ℂ) * g) * y κ ∂unitaryHaar n

/-- `y` is orthogonal to a nonzero `(𝔤, K)`-stable space of `U(n)`-finite functions of the principal
series of `χ⁻¹`. -/
def IsOrthStable (n : ℕ) (χ : ℕ → ℂˣ → ℂ) (y : Langlands.GeneralLinear n ℂ → ℂ) : Prop :=
  ∃ V : Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ),
    V ≤ kFiniteFunctions (principalSeries ℂ n (dualChar χ)) (unitaryCompact ℂ n) ∧
    (∀ κ ∈ unitaryCompact ℂ n, ∀ v ∈ V,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) κ v ∈ V) ∧
    (∀ (X : Matrix (Fin n) (Fin n) ℂ), ∀ v ∈ V, rightDerivative (matrixModel ℂ n) X v ∈ V) ∧
    V ≠ ⊥ ∧
    ∀ v ∈ V, ∫ κ : unitaryCompact ℂ n, v κ * y κ ∂unitaryHaar n = 0

/-- `M_{x,y}(g) = ∑_i M_{α_i,β_i}(gᵀ)` for all `g`, for finitely many `U(n)`-finite `α_i` of the
principal series of `χ⁻¹` and `β_i` of the principal series of `χ`, each `β_i` orthogonal to a
nonzero `(𝔤, K)`-stable space. -/
def HasTransposeExpansion (n : ℕ) (χ : ℕ → ℂˣ → ℂ) (x y : Langlands.GeneralLinear n ℂ → ℂ) :
    Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (α β : ι → Langlands.GeneralLinear n ℂ → ℂ),
    (∀ i, α i ∈ kFiniteFunctions (principalSeries ℂ n (dualChar χ)) (unitaryCompact ℂ n)) ∧
    (∀ i, β i ∈ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)) ∧
    (∀ i, IsOrthStable n χ (β i)) ∧
    ∀ g, coeff x y g = ∑ i, coeff (α i) (β i) (transposeGL g)

/-! ## Transposition of block matrices -/

theorem transposeGL_one {n : ℕ} : transposeGL (1 : Langlands.GeneralLinear n ℂ) = 1 :=
  Units.ext (by rw [transposeGL_val, Units.val_one, Matrix.transpose_one])

theorem transposeGL_blockDiagGL {a k : ℕ} (g₁ : Langlands.GeneralLinear a ℂ)
    (g₂ : Langlands.GeneralLinear k ℂ) :
    transposeGL (blockDiagGL g₁ g₂) = blockDiagGL (transposeGL g₁) (transposeGL g₂) := by
  apply Units.ext
  rw [transposeGL_val, ComplexBlockLimit.blockDiagGL_val, ComplexBlockLimit.blockDiagGL_val,
    transposeGL_val, transposeGL_val, ComplexBlockParabolic.blockDiag,
    ComplexBlockParabolic.blockDiag, Matrix.transpose_reindex, Matrix.fromBlocks_transpose,
    Matrix.transpose_zero, Matrix.transpose_zero]

theorem transposeGL_dTail {a k : ℕ} (s : ℂˣ) :
    transposeGL (dTail (a := a) (k := k) s) = dTail s := by
  apply Units.ext
  rw [transposeGL_val, dTail, Iwasawa.diagonalUnits_val, Matrix.diagonal_transpose]

/-! ## The limit along `P_{a,k+1}` as an identity -/

variable {a k : ℕ} {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ}

theorem blockTerm_neg (u h : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ) :
    blockTerm (-u) h = -blockTerm u h := by
  simp only [blockTerm, Pi.neg_apply, neg_mul, integral_neg]

/-- **The limit identity for sums.** If `∫ u₀(κ d(s)) h₀(κ) dκ = ∑_i ∫ u_i(κ d(s)) h_i(κ) dκ` for
every `s`, then `blockTerm u₀ h₀ = ∑_i blockTerm u_i h_i`. -/
theorem blockTerm_eq_sum_of_ray (hT1 : ComplexBlockChartIntegrableStatement)
    (hT3 : ComplexBlockParabolicIntegrationStatement)
    (hχ : IsPhasePower χ e) (he : IsBlockDominant e a k) {ι : Type} [Fintype ι]
    {u₀ h₀ : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}
    {u h : ι → Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}
    (hu₀ : u₀ ∈ principalSeries ℂ (a + (k + 1)) (dualChar χ))
    (hh₀ : h₀ ∈ principalSeries ℂ (a + (k + 1)) χ)
    (hu : ∀ i, u i ∈ principalSeries ℂ (a + (k + 1)) (dualChar χ))
    (hh : ∀ i, h i ∈ principalSeries ℂ (a + (k + 1)) χ)
    (heq : ∀ s : ℂˣ,
      ∫ κ, u₀ ((κ : Langlands.GeneralLinear (a + (k + 1)) ℂ) * dTail (a := a) (k := k + 1) s) *
        h₀ κ ∂unitaryHaar (a + (k + 1)) =
      ∑ i, ∫ κ, u i ((κ : Langlands.GeneralLinear (a + (k + 1)) ℂ) *
        dTail (a := a) (k := k + 1) s) * h i κ ∂unitaryHaar (a + (k + 1))) :
    blockTerm u₀ h₀ = ∑ i, blockTerm (u i) (h i) := by
  have H := sum_blockTerm_eq_zero hT1 hT3 hχ he.tie he.ord he.gap (Finset.univ : Finset (Option ι))
    (u := fun o => Option.elim o u₀ fun i => -u i) (h := fun o => Option.elim o h₀ h)
    (fun o _ => by
      cases o with
      | none => exact hu₀
      | some i => exact (principalSeries ℂ (a + (k + 1)) (dualChar χ)).neg_mem (hu i))
    (fun o _ => by
      cases o with
      | none => exact hh₀
      | some i => exact hh i)
    (fun s => by
      rw [Fintype.sum_option]
      simp only [Option.elim_none, Option.elim_some, Pi.neg_apply, neg_mul, integral_neg,
        Finset.sum_neg_distrib, heq s, add_neg_cancel])
  rw [Fintype.sum_option] at H
  simp only [Option.elim_none, Option.elim_some, blockTerm_neg, Finset.sum_neg_distrib] at H
  exact sub_eq_zero.mp (by rw [sub_eq_add_neg]; exact H)

/-! ## Evaluation of the leading terms -/

/-- The leading term of a function of product form `x'(diag(g₁, g₂)) = x(diag(g₁, 1)) φ(g₂)`,
translated by `diag(g₁, 1)`, is the matrix coefficient of the restriction of `x` and
`blockPair φ y` at `g₁`. -/
theorem blockTerm_translate_eq_of_product (g₁ : Langlands.GeneralLinear a ℂ)
    {x x' y : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}
    {φ : Langlands.GeneralLinear (k + 1) ℂ → ℂ}
    (hx' : ∀ (h₁ : Langlands.GeneralLinear a ℂ) (h₂ : Langlands.GeneralLinear (k + 1) ℂ),
      x' (blockDiagGL h₁ h₂) = x (blockDiagGL h₁ 1) * φ h₂) :
    blockTerm (fun z => x' (z * blockDiagGL g₁ (1 : Langlands.GeneralLinear (k + 1) ℂ))) y =
      coeff (restrictBlock (k := k) x) (blockPair φ y) g₁ := by
  simp only [blockTerm, coeff, blockPair]
  refine integral_congr_ae (ae_of_all _ fun κ₁ => ?_)
  simp only
  rw [restrictBlock_apply, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun κ₂ => ?_)
  simp only
  rw [← ComplexBlockJacquet.blockDiagGL_mul, mul_one, hx']
  simp only [blockStep]
  ring

/-- The leading term of a function with a finite slice decomposition
`α(diag(h₁, g₂)) = ∑_j P_j(diag(h₁, 1)) S_j(g₂)`, translated by `diag(g₁, 1)`, is the sum of the
matrix coefficients of the restrictions of `P_j` and `blockPair S_j β` at `g₁`. -/
theorem blockTerm_translate_eq_sum (hT1 : ComplexBlockChartIntegrableStatement)
    (hχ : IsPhasePower χ e) (he : IsBlockDominant e a k) (g₁ : Langlands.GeneralLinear a ℂ)
    {α β : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}
    (hβ : β ∈ kFiniteFunctions (principalSeries ℂ (a + (k + 1)) χ)
      (unitaryCompact ℂ (a + (k + 1))))
    {d : ℕ} {P : Fin d → Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}
    {S : Fin d → Langlands.GeneralLinear (k + 1) ℂ → ℂ}
    (hP : ∀ j, Continuous (P j)) (hS : ∀ j, Continuous (S j))
    (hα : ∀ (h₁ : Langlands.GeneralLinear a ℂ) (h₂ : Langlands.GeneralLinear (k + 1) ℂ),
      α (blockDiagGL h₁ h₂) = ∑ j, P j (blockDiagGL h₁ 1) * S j h₂) :
    blockTerm (fun z => α (z * blockDiagGL g₁ (1 : Langlands.GeneralLinear (k + 1) ℂ))) β =
      ∑ j, coeff (restrictBlock (k := k) (P j)) (blockPair (S j) β) g₁ := by
  simp only [blockTerm, coeff]
  -- integrability of the terms in `κ₂`
  have hint2 : ∀ (κ₁ : unitaryCompact ℂ a) (j : Fin d), Integrable (fun κ₂ :
      unitaryCompact ℂ (k + 1) => P j (blockDiagGL ((κ₁ : Langlands.GeneralLinear a ℂ) * g₁) 1) *
        (S j κ₂ * blockStep β (blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ)
          (κ₂ : Langlands.GeneralLinear (k + 1) ℂ)))) (unitaryHaar (k + 1)) := fun κ₁ j =>
    integrable_of_continuous_unitary (continuous_const.mul
      (((hS j).comp continuous_subtype_val).mul (continuous_blockStep hT1 hχ he hβ.1
        (f₁ := fun _ => (κ₁ : Langlands.GeneralLinear a ℂ)) continuous_const continuous_subtype_val
        (fun _ => κ₁.2) (fun t => t.2))))
  -- integrability of the terms in `κ₁`
  have hint1 : ∀ j : Fin d, Integrable (fun κ₁ : unitaryCompact ℂ a =>
      restrictBlock (k := k) (P j) ((κ₁ : Langlands.GeneralLinear a ℂ) * g₁) *
        blockPair (S j) β κ₁) (unitaryHaar a) := fun j => by
    refine integrable_of_continuous_unitary (Continuous.mul ?_ ?_)
    · exact (hP j).comp (continuous_blockDiagGL.comp
        (((continuous_subtype_val).mul continuous_const).prodMk continuous_const))
    · exact (blockPair_mem hT1 hχ he hβ (hS j)).1.1.continuous.comp continuous_subtype_val
  rw [← integral_finsetSum _ fun j _ => hint1 j]
  refine integral_congr_ae (ae_of_all _ fun κ₁ => ?_)
  simp only
  have hpt : ∀ κ₂ : unitaryCompact ℂ (k + 1),
      α (blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ) (κ₂ : Langlands.GeneralLinear (k + 1) ℂ) *
          blockDiagGL g₁ 1) *
        (∫ X : Fin (k + 1) → Fin a → ℂ, β (blockLowerGL (a := a) (k := k + 1) (Matrix.of X) *
          blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ) (κ₂ : Langlands.GeneralLinear (k + 1) ℂ))) =
      ∑ j, P j (blockDiagGL ((κ₁ : Langlands.GeneralLinear a ℂ) * g₁) 1) *
        (S j κ₂ * blockStep β (blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ)
          (κ₂ : Langlands.GeneralLinear (k + 1) ℂ))) := by
    intro κ₂
    rw [← ComplexBlockJacquet.blockDiagGL_mul, mul_one, hα, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [blockStep]
    ring
  rw [integral_congr_ae (ae_of_all _ hpt), integral_finsetSum _ fun j _ => hint2 κ₁ j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, restrictBlock_apply]
  rfl

/-! ## The recursion -/

/-- **Transposed expansions and the block Jacquet functional.** Under the block statements and
`TiedIrreducible`, let `ks` be a block decomposition with `BlockOrdered ks e`, `U` a
`(𝔤, K)`-stable space of `U(n)`-finite functions of the principal series of `χ⁻¹`, and `y` a
`U(n)`-finite function of the principal series of `χ` such that `M_{x,y}` has a transposed
expansion for every `x ∈ U`. Then `x(1) · jac ks e p y = 0` for every `x ∈ U`. -/
theorem mul_jac_eq_zero (hT1 : ComplexBlockChartIntegrableStatement)
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
    ∀ {y : Langlands.GeneralLinear (dim ks) ℂ → ℂ},
    y ∈ kFiniteFunctions (principalSeries ℂ (dim ks) χ) (unitaryCompact ℂ (dim ks)) →
    (∀ x ∈ U, HasTransposeExpansion (dim ks) χ x y) →
    ∀ x ∈ U, x 1 * jac ks e p y = 0
  | [], χ, e, p, _, _, _, U, _, _, _, y, _, hexp => by
      intro x hx
      have hsub : ∀ g : Langlands.GeneralLinear (dim []) ℂ, g = 1 := fun g => by
        apply Units.ext
        ext i j
        exact i.elim0
      have hcoeff : ∀ (u v : Langlands.GeneralLinear (dim []) ℂ → ℂ)
          (g : Langlands.GeneralLinear (dim []) ℂ), coeff u v g = u 1 * v 1 := by
        intro u v g
        have hc : (fun κ : unitaryCompact ℂ (dim []) =>
            u ((κ : Langlands.GeneralLinear (dim []) ℂ) * g) * v κ) = fun _ => u 1 * v 1 :=
          funext fun κ => by
            rw [hsub ((κ : Langlands.GeneralLinear (dim []) ℂ) * g),
              hsub (κ : Langlands.GeneralLinear (dim []) ℂ)]
        rw [coeff, hc, integral_const, probReal_univ, one_smul]
      obtain ⟨ι, _, α, β, -, -, hβo, hM⟩ := hexp x hx
      have hβ1 : ∀ i, β i 1 = 0 := by
        intro i
        obtain ⟨V, -, -, -, hV0, hVorth⟩ := hβo i
        obtain ⟨v, hvV, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV0
        have hv1 : v 1 ≠ 0 := fun h1 => hv0 (funext fun g => by rw [hsub g]; exact h1)
        have hint := hVorth v hvV
        have hconst : (fun κ : unitaryCompact ℂ (dim []) =>
            v (κ : Langlands.GeneralLinear (dim []) ℂ) * β i κ) = fun _ => v 1 * β i 1 :=
          funext fun κ => by rw [hsub κ]
        rw [hconst, integral_const, probReal_univ, one_smul] at hint
        exact (mul_eq_zero.mp hint).resolve_left hv1
      have h1 := hM 1
      simp only [hcoeff, hβ1, mul_zero, Finset.sum_const_zero] at h1
      exact h1
  | k :: ks, χ, e, p, hχ, hp, ⟨he, hks⟩, U, hU, hUK, hUD, y, hy, hexp => by
      set a := dim ks with ha
      have hφ := blockVector_mem hχ hp a k
      have hT : ∀ l : ℕ, l < k + 1 → ∀ z : ℂˣ,
          blockDualChar a χ l z = blockDualChar a χ l z := fun _ _ _ => rfl
      have hirrT := hirr (k + 1) (blockDualChar a χ)
        (fun l => -(e (a + l)) - ((a : ℕ) : ℂ) / 2) (fun l => -(p (a + l)))
        (isPhasePower_blockDualChar hχ a) (blockDualChar_phase hp a)
        (fun l hl => by
          simp only [Complex.sub_re, Complex.neg_re, add_zero]
          rw [he.tie l (by omega)])
      by_cases hU0 : U = ⊥
      · intro x hx
        rw [hU0, Submodule.mem_bot] at hx
        subst hx
        simp
      obtain ⟨hUM, hUMK, hUMD, -⟩ := map_restrictBlock (k := k) hχ hU hUK hUD hU0
      have hy' := blockPair_mem hT1 hχ he hy hφ.1.1.continuous
      have hexp' : ∀ x' ∈ U.map (restrictBlock (k := k)),
          HasTransposeExpansion a (blockShiftChar k χ) x' (blockPair (blockVector a k e p) y) := by
        rintro _ ⟨x, hx, rfl⟩
        obtain ⟨x'', hx''U, hx''⟩ := exists_mem_blockDiag_eq hχ hT hirrT hU hUK hUD hx hφ
        obtain ⟨ι, _, α, β, hα, hβ, hβo, hM⟩ := hexp x'' hx''U
        choose d P S hPm _ hSm hdec using fun i => exists_blockDiag_decomposition hχ hT (hα i)
        refine ⟨Σ i, Fin (d i), inferInstance, fun ij => restrictBlock (k := k) (P ij.1 ij.2),
          fun ij => blockPair (S ij.1 ij.2) (β ij.1),
          fun ij => restrictBlock_mem hχ (hPm ij.1 ij.2),
          fun ij => blockPair_mem hT1 hχ he (hβ ij.1) (hSm ij.1 ij.2).1.1.continuous,
          fun ij => ?_, fun g₁ => ?_⟩
        · obtain ⟨V, hV, hVK, hVD, hV0, hVorth⟩ := hβo ij.1
          obtain ⟨hVM, hVMK, hVMD, hVM0⟩ := map_restrictBlock (k := k) hχ hV hVK hVD hV0
          refine ⟨V.map (restrictBlock (k := k)), hVM, hVMK, hVMD, hVM0, ?_⟩
          rintro _ ⟨v, hv, rfl⟩
          exact integral_restrictBlock_mul_blockPair_eq_zero hT1 hT3 hχ he hT hirrT hV hVK hVD
            (hβ ij.1) hVorth ⟨_, hSm ij.1 ij.2⟩ hv
        · set b : Langlands.GeneralLinear (a + (k + 1)) ℂ :=
            blockDiagGL g₁ (1 : Langlands.GeneralLinear (k + 1) ℂ) with hb
          set bT : Langlands.GeneralLinear (a + (k + 1)) ℂ :=
            blockDiagGL (transposeGL g₁) (1 : Langlands.GeneralLinear (k + 1) ℂ) with hbT
          have hray : ∀ s : ℂˣ,
              ∫ κ, Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (a + (k + 1)) ℂ) b x''
                ((κ : Langlands.GeneralLinear (a + (k + 1)) ℂ) * dTail (a := a) (k := k + 1) s) *
                y (κ : Langlands.GeneralLinear (a + (k + 1)) ℂ) ∂unitaryHaar (a + (k + 1)) =
              ∑ i, ∫ κ, Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (a + (k + 1)) ℂ)
                bT (α i) ((κ : Langlands.GeneralLinear (a + (k + 1)) ℂ) *
                  dTail (a := a) (k := k + 1) s) * β i (κ : Langlands.GeneralLinear (a + (k + 1)) ℂ)
                  ∂unitaryHaar (a + (k + 1)) := by
            intro s
            have h := hM (dTail (a := a) (k := k + 1) s * b)
            rw [transposeGL_mul, hb, transposeGL_blockDiagGL, transposeGL_one, transposeGL_dTail,
              ComplexBlockLimit.blockDiagGL_mul_dTail] at h
            simp only [coeff, ← mul_assoc] at h
            exact h
          have hlim := blockTerm_eq_sum_of_ray hT1 hT3 hχ he
            (rightTranslation_mem_principalSeries (χ := dualChar χ) (hU hx''U).1 b) hy.1
            (fun i => rightTranslation_mem_principalSeries (χ := dualChar χ) (hα i).1 bT)
            (fun i => (hβ i).1) hray
          have hL := blockTerm_translate_eq_of_product (y := y) g₁ hx''
          have hR := fun i => blockTerm_translate_eq_sum hT1 hχ he (transposeGL g₁) (hβ i)
            (fun j => (hPm i j).1.1.continuous) (fun j => (hSm i j).1.1.continuous) (hdec i)
          change blockTerm (fun z => x'' (z * b)) y =
            ∑ i, blockTerm (fun z => α i (z * bT)) (β i) at hlim
          rw [hL, Finset.sum_congr rfl fun i _ => hR i] at hlim
          rw [hlim, Fintype.sum_sigma]
      have IH := mul_jac_eq_zero hT1 hT3 hirr ks p (isPhasePower_blockShift (k := k) hχ)
        (blockShiftChar_phase k hp) (hks.shift (((k : ℂ) + 1) / 2)) hUM hUMK hUMD hy' hexp'
      intro x hx
      have h := IH (restrictBlock (k := k) x) ⟨x, hx, rfl⟩
      rw [restrictBlock_apply, blockDiagGL_one_one] at h
      rw [jac_cons]
      exact h

end ComplexReverseBlockRecursion

end Langlands.Archimedean
