import Langlands.Representation.Archimedean.ComplexBlockNonvanishing
import Langlands.Representation.Archimedean.ComplexStrictLanglandsQuotient
import Langlands.Representation.Archimedean.ComplexTemperedIrreducibleStatement
import Langlands.Representation.Archimedean.ComplexJacquetBorel
import Langlands.Representation.Archimedean.ComplexLargeStandardIrreducibleReduction

/-!
# The Langlands quotient of a Langlands-ordered complex standard module, from the block statements

`ComplexBlockLanglandsQuotientStatement`: the statements `ComplexBlockChartIntegrableStatement`,
`ComplexBlockParabolicIntegrationStatement` and `ComplexTemperedStandardIrreducibleStatement`
imply `ComplexStandardLanglandsQuotientStatement`. A Langlands-ordered list is cut into maximal
blocks of exponents with equal real parts; the block Jacquet functional
`ComplexBlockFunctional.jac` vanishes on every proper `(𝔤, K)`-submodule and is nonzero, so the
sum of all proper submodules is proper.
-/

noncomputable section

open MeasureTheory Matrix Filter Topology

open scoped Matrix TensorProduct Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

namespace ComplexBlockLanglandsQuotient

open ComplexBlockJacquet ComplexBlockFunctional ComplexBlockNonvanishing ComplexStrictLanglandsQuotient
  ComplexPartialJacquet ComplexGramFormula ComplexDuality Langlands.LocalFactor.Archimedean

/-! ## Block decompositions of Langlands-ordered exponents -/

/-- Weakly decreasing real parts have a decomposition into maximal tied blocks. -/
theorem exists_blockOrdered : ∀ (n : ℕ) (e : ℕ → ℂ),
    (∀ l : ℕ, l + 1 < n → (e (l + 1)).re ≤ (e l).re) →
    ∃ ks : List ℕ, dim ks = n ∧ BlockOrdered ks e := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro e hord
    cases n with
    | zero => exact ⟨[], rfl, trivial⟩
    | succ m =>
      have hP : ∃ a : ℕ, a ≤ m ∧ ∀ j : ℕ, a ≤ j → j ≤ m → (e j).re = (e m).re :=
        ⟨m, le_rfl, fun j h1 h2 => by rw [show j = m by omega]⟩
      classical
      set a := Nat.find hP with ha
      have hPa : a ≤ m ∧ ∀ j : ℕ, a ≤ j → j ≤ m → (e j).re = (e m).re := Nat.find_spec hP
      obtain ⟨ks', hdim, hks'⟩ := ih a (by omega) e fun l hl => hord l (by omega)
      refine ⟨(m - a) :: ks', ?_, ?_, hks'⟩
      · change dim ks' + (m - a + 1) = m + 1
        omega
      · rw [hdim]
        refine ⟨fun j hj => ?_, fun l hl => hord l (by omega), fun l hl => ?_⟩
        · rw [hPa.2 (a + j) (by omega) (by omega), hPa.2 a le_rfl hPa.1]
        · have hmin : ¬ (l ≤ m ∧ ∀ j : ℕ, l ≤ j → j ≤ m → (e j).re = (e m).re) :=
            Nat.find_min hP (by omega)
          have hne : (e l).re ≠ (e m).re := by
            intro heq
            refine hmin ⟨by omega, fun j hj1 hj2 => ?_⟩
            rcases Nat.eq_or_lt_of_le hj1 with rfl | hlt
            · exact heq
            · exact hPa.2 j (by omega) hj2
          have hle := hord l (by omega)
          rw [hl] at hle ⊢
          rw [hPa.2 a le_rfl hPa.1] at hle ⊢
          exact lt_of_le_of_ne hle (Ne.symm hne)

/-! ## Irreducibility of tied principal series from the tempered statement -/

theorem complexPositionWeight_ofFn :
    ∀ {n : ℕ} (d : Fin n → ComplexCharacterData) (j : Fin n),
      complexPositionWeight (List.ofFn d) j = (d j).weight
  | 0, _, j => j.elim0
  | n + 1, d, j => by
    rw [List.ofFn_succ]
    induction j using Fin.cases with
    | zero => rfl
    | succ j => exact complexPositionWeight_ofFn (fun i => d i.succ) j

theorem complexPositionExponent_ofFn :
    ∀ {n : ℕ} (d : Fin n → ComplexCharacterData) (j : Fin n),
      complexPositionExponent (List.ofFn d) j = (d j).exponent
  | 0, _, j => j.elim0
  | n + 1, d, j => by
    rw [List.ofFn_succ]
    induction j using Fin.cases with
    | zero => rfl
    | succ j => exact complexPositionExponent_ofFn (fun i => d i.succ) j

theorem complexPositionCharacter_ofFn_params {b : ℕ} {ψ : ℕ → ℂˣ → ℂ} {f : ℕ → ℂ} {q : ℕ → ℤ}
    (hψ : IsPhasePower ψ f)
    (hq : ∀ (l : ℕ) (z : ℂˣ), ψ l (phaseUnit z) = ((phaseUnit z : ℂˣ) : ℂ) ^ (q l))
    (j : Fin b) (z : ℂˣ) :
    complexPositionCharacter (List.ofFn fun i : Fin b => characterOfParams (q i) (f i)) j z =
      ψ j z := by
  rw [complexPositionCharacter_eq_phaseUnit_mul, complexPositionCharacter_phase,
    complexPositionWeight_ofFn, complexPositionExponent_ofFn, characterOfParams_weight,
    characterOfParams_exponent, hψ.eq j z, hq]

theorem isIrreducible_kFinite_congr {N : ℕ} {V₁ V₂ : Submodule ℂ (Langlands.GeneralLinear N ℂ → ℂ)}
    (h : V₁ = V₂)
    (hV₁ : ∀ f ∈ V₁, ContMDiff (matrixModel ℂ N) 𝓘(ℝ, ℂ) ∞ f)
    (hVK₁ : ∀ k ∈ unitaryCompact ℂ N, ∀ f ∈ V₁,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℂ) k f ∈ V₁)
    (hVX₁ : ∀ (X : Matrix (Fin N) (Fin N) ℂ), ∀ f ∈ V₁,
      rightDerivative (matrixModel ℂ N) X f ∈ V₁)
    (hV₂ : ∀ f ∈ V₂, ContMDiff (matrixModel ℂ N) 𝓘(ℝ, ℂ) ∞ f)
    (hVK₂ : ∀ k ∈ unitaryCompact ℂ N, ∀ f ∈ V₂,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℂ) k f ∈ V₂)
    (hVX₂ : ∀ (X : Matrix (Fin N) (Fin N) ℂ), ∀ f ∈ V₂,
      rightDerivative (matrixModel ℂ N) X f ∈ V₂) :
    IsIrreducibleGKModule (kFiniteRep V₁ hVK₁) (kFiniteLie V₁ hV₁ hVK₁ hVX₁) →
      IsIrreducibleGKModule (kFiniteRep V₂ hVK₂) (kFiniteLie V₂ hV₂ hVK₂ hVX₂) := by
  subst h
  exact id

theorem principalSeries_congr {N : ℕ} {χ₁ χ₂ : ℕ → ℂˣ → ℂ}
    (h : ∀ (j : Fin N) (z : ℂˣ), χ₁ j z = χ₂ j z) :
    principalSeries ℂ N χ₁ = principalSeries ℂ N χ₂ := by
  have hc : principalSeriesCharacter ℂ N χ₁ = principalSeriesCharacter ℂ N χ₂ := by
    funext z
    rw [principalSeriesCharacter, principalSeriesCharacter]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [h i (z i)]
  ext f
  simp only [mem_principalSeries_iff, hc]

/-- The exponents of a Langlands-ordered list have weakly decreasing real parts. -/
theorem exponent_ordered : ∀ {ds : List ComplexCharacterData}, IsComplexLanglandsOrdered ds →
    ∀ l : ℕ, l + 1 < ds.length →
      (complexPositionExponent ds (l + 1)).re ≤ (complexPositionExponent ds l).re
  | [], _ => fun l hl => by simp at hl
  | d :: ds, hs => by
      have hs' : IsComplexLanglandsOrdered ds := (List.pairwise_cons.mp hs).2
      have ih := exponent_ordered hs'
      intro l hl
      simp only [List.length_cons] at hl
      cases l with
      | zero =>
          cases ds with
          | nil => simp at hl
          | cons b ds'' =>
              have hrel := (List.pairwise_cons.mp hs).1 _ (List.mem_cons_self ..)
              simpa [complexPositionExponent] using hrel
      | succ l =>
          simp only [complexPositionExponent]
          exact ih l (by omega)

/-- `ComplexTemperedStandardIrreducibleStatement` gives `TiedIrreducible`. -/
theorem tiedIrreducible (hU : ComplexTemperedStandardIrreducibleStatement) : TiedIrreducible := by
  intro b ψ f q hψ hq htie
  set ds : List ComplexCharacterData := List.ofFn fun i : Fin b => characterOfParams (q i) (f i)
    with hds
  have hlen : ds.length = b := List.length_ofFn
  have hexp : ∀ d ∈ ds, ∀ d' ∈ ds, d.exponent.re = d'.exponent.re := by
    intro d hd d' hd'
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
    obtain ⟨i', rfl⟩ := List.mem_ofFn.mp hd'
    simp only [characterOfParams_exponent]
    rw [htie i i.isLt, htie i' i'.isLt]
  have h := hU b ds hlen hexp
  exact isIrreducible_kFinite_congr
    (principalSeries_congr fun j z => complexPositionCharacter_ofFn_params hψ hq j z)
    _ _ _ _ _ _ h

end ComplexBlockLanglandsQuotient

open ComplexBlockLanglandsQuotient ComplexStrictLanglandsQuotient ComplexBlockFunctional
  ComplexGramFormula ComplexPartialJacquet Langlands.LocalFactor.Archimedean

/-- **The Langlands quotient from the block statements.** The statements
`ComplexBlockChartIntegrableStatement`, `ComplexBlockParabolicIntegrationStatement` and
`ComplexTemperedStandardIrreducibleStatement` imply `ComplexStandardLanglandsQuotientStatement`:
for a Langlands-ordered list `ds` of `n` complex characters, the `U(n)`-finite functions of the
standard module of `ds` have a largest proper `(𝔤𝔩_n(ℂ), U(n))`-submodule. -/
def ComplexBlockLanglandsQuotientStatement : Prop :=
  ComplexBlockChartIntegrableStatement → ComplexBlockParabolicIntegrationStatement →
    ComplexTemperedStandardIrreducibleStatement → ComplexStandardLanglandsQuotientStatement

theorem complexBlockLanglandsQuotient : ComplexBlockLanglandsQuotientStatement := by
  intro hT1 hT3 hU n ds hn hord
  set χ := complexPositionCharacter ds with hχdef
  set e := complexPositionExponent ds with hedef
  set p := complexPositionWeight ds with hpdef
  have hχ := isPhasePower ds
  have hp := complexPositionCharacter_phase ds
  have hdom : ∀ l : ℕ, l + 1 < n → (e (l + 1)).re ≤ (e l).re := by
    subst hn
    exact exponent_ordered hord
  obtain ⟨ks, hdim, hks⟩ := exists_blockOrdered n e hdom
  subst hdim
  set N := dim ks
  have hker : largestProper N χ ≤ jacKernel hT1 ks p hχ hp hks := iSup_le fun W => by
    obtain ⟨⟨hWX, hWK, hWD⟩, f, hf, hfW⟩ := W.2
    exact jac_eq_zero_of_proper hT1 hT3 (tiedIrreducible hU) p hχ hp hks _ hWX hWK hWD hf hfW
  obtain ⟨av, L, -, hne⟩ := ComplexBlockNonvanishing.exists_jac_testVector_ne_zero hT1 ks p hχ hp hks
  have hf₀ := ComplexBlockNonvanishing.testVector_mem (n := N) hχ hp av L
  set f₀ := ComplexBlockNonvanishing.testVector N e p av L
  have hf₀R : f₀ ∉ largestProper N χ := fun hfR => hne (hker hfR).2
  obtain ⟨hRX, hRK, hRD⟩ := (isGKStable_largestProper : IsGKStable N χ (largestProper N χ))
  set S := kFiniteFunctions (complexStandardModule N ds) (unitaryCompact ℂ N) with hSdef
  refine ⟨(largestProper N χ).comap S.subtype, ⟨fun κ f hf => ?_, fun Y => ?_⟩, ?_,
    fun W hW hW' => ?_⟩
  · change ((complexStandardRep N ds κ f : S) : Langlands.GeneralLinear N ℂ → ℂ) ∈
      largestProper N χ
    rw [principalSeriesRep_apply_coe]
    exact hRK (Unitary.toUnits κ) κ.2 _ hf
  · induction Y using TensorProduct.inductionOn with
    | tmul c X =>
        intro w hw
        have hc : (c ⊗ₜ[ℝ] X : ℂ ⊗[ℝ] Matrix (Fin N) (Fin N) ℂ) = c • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [hc, map_smul, LinearMap.smul_apply]
        refine Submodule.smul_mem _ c ?_
        change ((complexStandardLie N ds (1 ⊗ₜ X) w : S) : Langlands.GeneralLinear N ℂ → ℂ) ∈
          largestProper N χ
        rw [principalSeriesLie_one_tmul_apply_coe]
        exact hRD X _ hw
    | add Y Z hY hZ =>
        intro w hw
        rw [map_add, LinearMap.add_apply]
        exact add_mem (hY w hw) (hZ w hw)
  · intro htop
    have : (⟨f₀, hf₀⟩ : S) ∈ (largestProper N χ).comap S.subtype := by
      rw [htop]
      trivial
    exact hf₀R this
  · obtain ⟨⟨g, hgS⟩, hgW⟩ : ∃ g : S, g ∉ W := by
      by_contra hcon
      exact hW' (eq_top_iff.mpr fun g _ => by_contra fun h => hcon ⟨g, h⟩)
    have hWX : W.map S.subtype ≤ kFiniteFunctions (principalSeries ℂ N χ) (unitaryCompact ℂ N) := by
      rintro _ ⟨w, -, rfl⟩
      exact w.2
    have hprop : IsProperGKStable N χ (W.map S.subtype) := by
      refine ⟨⟨hWX, fun k hk _ hw => ?_, fun X _ hw => ?_⟩, g, hgS, ?_⟩
      · obtain ⟨w, hwW, rfl⟩ := hw
        refine ⟨complexStandardRep N ds ⟨(k : Matrix (Fin N) (Fin N) ℂ), hk⟩ w,
          hW.1 _ w hwW, ?_⟩
        change ((complexStandardRep N ds _ w : S) : Langlands.GeneralLinear N ℂ → ℂ) = _
        rw [principalSeriesRep_apply_coe]
        have hku : Unitary.toUnits (⟨(k : Matrix (Fin N) (Fin N) ℂ), hk⟩ :
            Matrix.unitaryGroup (Fin N) ℂ) = k := Units.ext rfl
        rw [hku]
        rfl
      · obtain ⟨w, hwW, rfl⟩ := hw
        exact ⟨complexStandardLie N ds (1 ⊗ₜ X) w, hW.2 _ w hwW,
          principalSeriesLie_one_tmul_apply_coe ℂ N χ X w⟩
      · rintro ⟨w, hwW, hw⟩
        apply hgW
        have : w = ⟨g, hgS⟩ := Subtype.ext hw
        rw [← this]
        exact hwW
    intro w hw
    exact le_largestProper hprop ⟨w, hw, rfl⟩

end Langlands.Archimedean
