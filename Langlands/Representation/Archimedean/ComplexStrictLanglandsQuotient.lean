import Langlands.Representation.Archimedean.ComplexJacquetNonvanishing
import Langlands.Representation.Archimedean.ComplexLargeStandardIrreducibleReduction

/-!
# The Langlands quotient of a strictly ordered complex standard module

If the real parts of the exponents of a list `ds` of complex characters strictly decrease, the
`U(n)`-finite functions of the standard module of `ds` have a largest proper
`(𝔤𝔩_n(ℂ), U(n))`-submodule (`complexStrictLanglandsQuotient`).
-/

noncomputable section

open scoped TensorProduct Matrix Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

namespace ComplexStrictLanglandsQuotient

open ComplexPartialJacquet ComplexJacquetDual ComplexJacquetKernel ComplexJacquetNonvanishing
  ComplexGramFormula Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

variable {n : ℕ} {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ}

/-! ## The largest proper submodule of a strictly dominant principal series -/

/-- `W` is a `(𝔤, K)`-stable subspace of the `U(n)`-finite principal series of `χ`. -/
def IsGKStable (n : ℕ) (χ : ℕ → ℂˣ → ℂ) (W : Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ)) :
    Prop :=
  W ≤ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n) ∧
    (∀ k ∈ unitaryCompact ℂ n, ∀ w ∈ W,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) k w ∈ W) ∧
    ∀ (X : Matrix (Fin n) (Fin n) ℂ), ∀ w ∈ W, rightDerivative (matrixModel ℂ n) X w ∈ W

/-- `W` is a proper `(𝔤, K)`-stable subspace. -/
def IsProperGKStable (n : ℕ) (χ : ℕ → ℂˣ → ℂ)
    (W : Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ)) : Prop :=
  IsGKStable n χ W ∧ ∃ f ∈ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n), f ∉ W

/-- The sum of all proper `(𝔤, K)`-stable subspaces. -/
def largestProper (n : ℕ) (χ : ℕ → ℂˣ → ℂ) : Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ) :=
  ⨆ W : {W : Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ) // IsProperGKStable n χ W},
    (W : Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ))

theorem le_largestProper {W : Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ)}
    (hW : IsProperGKStable n χ W) : W ≤ largestProper n χ :=
  le_iSup (fun W : {W : Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ) //
    IsProperGKStable n χ W} => (W : Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ))) ⟨W, hW⟩

theorem largestProper_le :
    largestProper n χ ≤ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n) :=
  iSup_le fun W => W.2.1.1

theorem rightDerivative_zero (X : Matrix (Fin n) (Fin n) ℂ) :
    rightDerivative (matrixModel ℂ n) X (0 : Langlands.GeneralLinear n ℂ → ℂ) = 0 := by
  have h := rightDerivative_smul (contMDiff_const (c := (0 : ℂ))) 0 X
  rw [zero_smul, zero_smul] at h
  exact h

theorem isGKStable_largestProper : IsGKStable n χ (largestProper n χ) := by
  refine ⟨largestProper_le, fun k hk w hw => ?_, fun X w hw => ?_⟩
  · refine Submodule.iSup_induction (fun W : {W : Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ) //
      IsProperGKStable n χ W} => (W : Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ)))
      (motive := fun w => Whittaker.rightTranslation ℂ
        (Langlands.GeneralLinear n ℂ) k w ∈ largestProper n χ) hw (fun W x hx => ?_) ?_
      (fun x y hx hy => ?_)
    · exact le_largestProper W.2 (W.2.1.2.1 k hk x hx)
    · rw [map_zero]
      exact Submodule.zero_mem _
    · rw [map_add]
      exact add_mem hx hy
  · have key : w ∈ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n) ∧
        rightDerivative (matrixModel ℂ n) X w ∈ largestProper n χ := by
      refine Submodule.iSup_induction (fun W : {W : Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ) //
        IsProperGKStable n χ W} => (W : Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ)))
        (motive := fun w =>
        w ∈ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n) ∧
          rightDerivative (matrixModel ℂ n) X w ∈ largestProper n χ) hw
        (fun W x hx => ⟨W.2.1.1 hx, le_largestProper W.2 (W.2.1.2.2 X x hx)⟩) ?_
        (fun x y hx hy => ?_)
      · exact ⟨Submodule.zero_mem _, by rw [rightDerivative_zero]; exact Submodule.zero_mem _⟩
      · refine ⟨add_mem hx.1 hy.1, ?_⟩
        rw [rightDerivative_add hx.1.1.1 hy.1.1.1]
        exact add_mem hx.2 hy.2
    exact key.2

/-- **The largest proper submodule.** For strictly dominant phase-power characters `χ` with
`χ_l(u) = u^{p_l}` on the unit circle, the sum of all proper `(𝔤, K)`-stable subspaces of the
`U(n)`-finite principal series of `χ` is proper and `(𝔤, K)`-stable, and it lies in the kernel
of the Jacquet integral. -/
theorem isProperGKStable_largestProper (hχ : IsPhasePower χ e)
    (he : IsStrictlyDominant e (n - 1)) {p : ℕ → ℤ}
    (hp : ∀ (l : ℕ) (z : ℂˣ), χ l (phaseUnit z) = ((phaseUnit z : ℂˣ) : ℂ) ^ (p l)) :
    IsProperGKStable n χ (largestProper n χ) ∧ largestProper n χ ≤ jacquetKernel n hχ he := by
  have hker : largestProper n χ ≤ jacquetKernel n hχ he := iSup_le fun W => by
    obtain ⟨⟨hWX, hWK, hWD⟩, f, hf, hfW⟩ := W.2
    exact jacquet_eq_zero_of_proper hχ he _ hWX hWK hWD hf hfW
  refine ⟨⟨isGKStable_largestProper, ?_⟩, hker⟩
  obtain ⟨f, hf, hf0⟩ := exists_jacquet_ne_zero hχ he hp
  exact ⟨f, hf, fun hfR => hf0 (hker hfR).2⟩

/-! ## The characters of a list of complex characters -/

/-- The weight `l` of the character at each diagonal position of a list of complex characters;
`0` past the end. -/
def complexPositionWeight : List ComplexCharacterData → ℕ → ℤ
  | [], _ => 0
  | d :: _, 0 => d.weight
  | _ :: ds, p + 1 => complexPositionWeight ds p

theorem complexPositionCharacter_one : ∀ (ds : List ComplexCharacterData) (l : ℕ),
    complexPositionCharacter ds l 1 = 1
  | [], _ => rfl
  | d :: _, 0 => by simp [complexPositionCharacter]
  | _ :: ds, l + 1 => complexPositionCharacter_one ds l

theorem complexPositionCharacter_phase : ∀ (ds : List ComplexCharacterData) (l : ℕ) (z : ℂˣ),
    complexPositionCharacter ds l (phaseUnit z) =
      ((phaseUnit z : ℂˣ) : ℂ) ^ (complexPositionWeight ds l)
  | [], _, z => by simp [complexPositionCharacter, complexPositionWeight]
  | d :: _, 0, z => by
      simp only [complexPositionCharacter, complexPositionWeight]
      rw [d.character_eq, norm_phaseUnit, Complex.ofReal_one, div_one, Complex.one_cpow, mul_one]
  | _ :: ds, l + 1, z => by
      simp only [complexPositionCharacter, complexPositionWeight]
      exact complexPositionCharacter_phase ds l z

theorem isPhasePower (ds : List ComplexCharacterData) :
    IsPhasePower (complexPositionCharacter ds) (complexPositionExponent ds) where
  eq := complexPositionCharacter_eq_phaseUnit_mul ds
  one := complexPositionCharacter_one ds
  norm_phase l z := by
    rw [complexPositionCharacter_phase, norm_zpow, norm_phaseUnit, _root_.one_zpow]

/-- The real parts of the exponents of `ds` strictly decrease. -/
def IsStrictlyOrdered (ds : List ComplexCharacterData) : Prop :=
  ds.Pairwise fun d e => e.exponent.re < d.exponent.re

theorem isStrictlyDominant : ∀ {ds : List ComplexCharacterData}, IsStrictlyOrdered ds →
    IsStrictlyDominant (complexPositionExponent ds) (ds.length - 1)
  | [], _ => fun l hl => by simp at hl
  | d :: ds, hs => by
      have hs' : IsStrictlyOrdered ds := (List.pairwise_cons.mp hs).2
      have ih := isStrictlyDominant hs'
      intro l hl
      simp only [List.length_cons, Nat.add_sub_cancel] at hl
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

end ComplexStrictLanglandsQuotient

open ComplexStrictLanglandsQuotient Langlands.LocalFactor.Archimedean

/-- **Statement (Langlands quotient of a strictly ordered complex standard module).** Let `ds`
be a list of `n` complex characters `z ↦ (z/|z|)^{l_i} |z|^{2 t_i}` whose exponents have strictly
decreasing real parts, `Re t_0 > Re t_1 > ⋯`. Then the `U(n)`-finite functions of the standard
module of `ds` have a largest proper `(𝔤𝔩_n(ℂ), U(n))`-submodule: a proper `(𝔤, K)`-submodule
containing every proper `(𝔤, K)`-submodule. -/
def ComplexStrictLanglandsQuotientStatement : Prop :=
  ∀ (n : ℕ) (ds : List ComplexCharacterData), ds.length = n →
    ds.Pairwise (fun d e => e.exponent.re < d.exponent.re) →
    ∃ R : Submodule ℂ (kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)),
      IsGKSubmodule (complexStandardRep n ds) (complexStandardLie n ds) R ∧ R ≠ ⊤ ∧
        ∀ W : Submodule ℂ (kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)),
          IsGKSubmodule (complexStandardRep n ds) (complexStandardLie n ds) W → W ≠ ⊤ → W ≤ R

theorem complexStrictLanglandsQuotient : ComplexStrictLanglandsQuotientStatement := by
  intro n ds hn hord
  subst hn
  set n := ds.length
  set χ := complexPositionCharacter ds
  have hχ := isPhasePower ds
  have he := isStrictlyDominant hord
  obtain ⟨⟨⟨hRX, hRK, hRD⟩, f₀, hf₀, hf₀R⟩, -⟩ :=
    isProperGKStable_largestProper hχ he (complexPositionCharacter_phase ds)
  set S := kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) with hSdef
  refine ⟨(largestProper n χ).comap S.subtype, ⟨fun κ f hf => ?_, fun Y => ?_⟩, ?_,
    fun W hW hW' => ?_⟩
  · change ((complexStandardRep n ds κ f : S) : Langlands.GeneralLinear n ℂ → ℂ) ∈
      largestProper n χ
    rw [principalSeriesRep_apply_coe]
    exact hRK (Unitary.toUnits κ) κ.2 _ hf
  · induction Y using TensorProduct.inductionOn with
    | tmul c X =>
        intro w hw
        have hc : (c ⊗ₜ[ℝ] X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) = c • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [hc, map_smul, LinearMap.smul_apply]
        refine Submodule.smul_mem _ c ?_
        change ((complexStandardLie n ds (1 ⊗ₜ X) w : S) : Langlands.GeneralLinear n ℂ → ℂ) ∈
          largestProper n χ
        rw [principalSeriesLie_one_tmul_apply_coe]
        exact hRD X _ hw
    | add Y Z hY hZ =>
        intro w hw
        rw [map_add, LinearMap.add_apply]
        exact add_mem (hY w hw) (hZ w hw)
  · intro htop
    have : (⟨f₀, hf₀⟩ : S) ∈ (largestProper n χ).comap S.subtype := by
      rw [htop]
      trivial
    exact hf₀R this
  · obtain ⟨⟨g, hgS⟩, hgW⟩ : ∃ g : S, g ∉ W := by
      by_contra hcon
      exact hW' (eq_top_iff.mpr fun g _ => by_contra fun h => hcon ⟨g, h⟩)
    have hWX : W.map S.subtype ≤ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n) := by
      rintro _ ⟨w, -, rfl⟩
      exact w.2
    have hprop : IsProperGKStable n χ (W.map S.subtype) := by
      refine ⟨⟨hWX, fun k hk _ hw => ?_, fun X _ hw => ?_⟩, g, hgS, ?_⟩
      · obtain ⟨w, hwW, rfl⟩ := hw
        refine ⟨complexStandardRep n ds ⟨(k : Matrix (Fin n) (Fin n) ℂ), hk⟩ w,
          hW.1 _ w hwW, ?_⟩
        change ((complexStandardRep n ds _ w : S) : Langlands.GeneralLinear n ℂ → ℂ) = _
        rw [principalSeriesRep_apply_coe]
        have hku : Unitary.toUnits (⟨(k : Matrix (Fin n) (Fin n) ℂ), hk⟩ :
            Matrix.unitaryGroup (Fin n) ℂ) = k := Units.ext rfl
        rw [hku]
        rfl
      · obtain ⟨w, hwW, rfl⟩ := hw
        exact ⟨complexStandardLie n ds (1 ⊗ₜ X) w, hW.2 _ w hwW,
          principalSeriesLie_one_tmul_apply_coe ℂ n χ X w⟩
      · rintro ⟨w, hwW, hw⟩
        apply hgW
        have : w = ⟨g, hgS⟩ := Subtype.ext hw
        rw [← this]
        exact hwW
    intro w hw
    exact le_largestProper hprop ⟨w, hw, rfl⟩

end Langlands.Archimedean
