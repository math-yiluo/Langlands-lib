import Langlands.Global.RankinSelberg.LocalPointFactorization
import Langlands.Global.RankinSelberg.WhittakerQuotientScaling
import Langlands.Automorphic.CuspidalL2.Basics

/-! # Proof of the one-place Iwasawa cell decomposition of the Whittaker quotient measure

This file proves `WhittakerCellDecompositionStatement`. For `λ ∈ ℤ^m` the left translation
`T_λ : N_m(𝔸) g ↦ N_m(𝔸) ι_v(ϖ^λ) g` carries the classes `U_S` onto the cell `C_λ` of the
classes in `U_(S ∪ {v})` whose `v`-component lies in `N_m(F_v) ϖ^λ GL_m(𝒪_v)`. By the
Library's `WhittakerQuotientScaling.map_leftShift_localPoint_torus` it multiplies
`whittakerQuotientMeasure` by `q_v^(-∑_(i<j)(λ_i-λ_j))`. The Iwasawa decomposition at `v`
makes the cells a countable measurable partition of `U_(S ∪ {v})`. See the paired Markdown.
-/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Topology
open scoped CategoryTheory.MonObj NNReal ENNReal Pointwise
open Classical Function
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.WhittakerCell

local instance cellProofSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance cellProofSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

/-! ## The Iwasawa exponent at one place -/

section Local

variable {F : Type u} [Field F] [NumberField F] (v : FinitePlace F)

theorem mem_localIntegral_iff_mem_integralSubgroup (n : ℕ) (k : FiniteLocalGL F (n + 1) v) :
    k ∈ FiniteAdelicGL.localIntegral F (n + 1) v ↔
      k ∈ Conductor.integralSubgroup
        (Valued.v : Valuation (FiniteCompletion F v) (WithZero (Multiplicative ℤ))).integer n := by
  rw [FiniteAdelicGL.mem_localIntegral, Conductor.mem_integralSubgroup]
  rfl

/-- Conjugation by a diagonal matrix preserves the upper unipotent matrices. -/
theorem diagonalUnits_conj_mem_upperUnipotent {m : ℕ} (d : Fin m → (FiniteCompletion F v)ˣ)
    {n : FiniteLocalGL F m v} (hn : n ∈ GeneralLinear.upperUnipotent m (FiniteCompletion F v)) :
    GeneralLinear.Iwasawa.diagonalUnits d * n * (GeneralLinear.Iwasawa.diagonalUnits d)⁻¹ ∈
      GeneralLinear.upperUnipotent m (FiniteCompletion F v) := by
  rw [← map_inv]
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · change (GeneralLinear.Iwasawa.diagonalUnits d * n *
      GeneralLinear.Iwasawa.diagonalUnits d⁻¹) i j = 0
    rw [GeneralLinear.Iwasawa.diagonalUnits_mul_mul_apply, hn.1 hji, mul_zero, zero_mul]
  · rw [GeneralLinear.Iwasawa.diagonalUnits_mul_mul_apply, hn.2 i, mul_one, Pi.inv_apply,
      Units.mul_inv]

/-- `x ∈ N_m(F_v) GL_m(𝒪_v)`, written with the upper unipotent subgroup. -/
theorem isUnipotentIntegral_iff_exists {m : ℕ} (x : FiniteLocalGL F m v) :
    IsUnipotentIntegral F m v x ↔
      ∃ n ∈ GeneralLinear.upperUnipotent m (FiniteCompletion F v),
        ∃ k ∈ FiniteAdelicGL.localIntegral F m v, n * k = x := by
  rw [isUnipotentIntegral_iff]
  constructor
  · rintro ⟨n, hn, k, hk, h⟩
    exact ⟨n, hn, k, hk, h⟩
  · rintro ⟨n, hn, k, hk, h⟩
    exact ⟨n, hn, k, hk, h⟩

/-- Every `x ∈ GL_m(F_v)` lies in some cell: `ϖ^(-λ) x ∈ N_m(F_v) GL_m(𝒪_v)`. -/
theorem exists_isUnipotentIntegral_torus_inv_mul {m : ℕ} {ϖ : (FiniteCompletion F v)ˣ}
    (hϖ : GeneralLinear.Iwasawa.IsUniformizingElement
      (Valued.v : Valuation (FiniteCompletion F v) (WithZero (Multiplicative ℤ))) ϖ)
    (x : FiniteLocalGL F m v) :
    ∃ lam : Fin m → ℤ,
      IsUnipotentIntegral F m v ((GeneralLinear.Iwasawa.torus ϖ lam)⁻¹ * x) := by
  cases m with
  | zero =>
    refine ⟨fun i => i.elim0, (isUnipotentIntegral_iff_exists v _).mpr
      ⟨1, one_mem _, _, ?_, one_mul _⟩⟩
    rw [FiniteAdelicGL.mem_localIntegral]
    exact ⟨fun i => i.elim0, fun i => i.elim0⟩
  | succ n =>
    obtain ⟨u, hu, lam, k, hk, hx⟩ := GeneralLinear.Iwasawa.exists_iwasawa hϖ x
    refine ⟨lam, (isUnipotentIntegral_iff_exists v _).mpr
      ⟨(GeneralLinear.Iwasawa.torus ϖ lam)⁻¹ * u * GeneralLinear.Iwasawa.torus ϖ lam, ?_, k,
        (mem_localIntegral_iff_mem_integralSubgroup v n k).mpr hk, ?_⟩⟩
    · have h := diagonalUnits_conj_mem_upperUnipotent v (fun i => (ϖ ^ lam i)⁻¹) hu
      rwa [← GeneralLinear.Iwasawa.torus_inv, inv_inv] at h
    · rw [hx]
      group

/-- The cell of `x ∈ GL_m(F_v)` is unique. -/
theorem eq_of_isUnipotentIntegral_torus_inv_mul {m : ℕ} {ϖ : (FiniteCompletion F v)ˣ}
    (hϖ : GeneralLinear.Iwasawa.IsUniformizingElement
      (Valued.v : Valuation (FiniteCompletion F v) (WithZero (Multiplicative ℤ))) ϖ)
    {x : FiniteLocalGL F m v} {lam lam' : Fin m → ℤ}
    (h : IsUnipotentIntegral F m v ((GeneralLinear.Iwasawa.torus ϖ lam)⁻¹ * x))
    (h' : IsUnipotentIntegral F m v ((GeneralLinear.Iwasawa.torus ϖ lam')⁻¹ * x)) :
    lam = lam' := by
  cases m with
  | zero => exact Subsingleton.elim _ _
  | succ n =>
    have key : ∀ l : Fin (n + 1) → ℤ,
        IsUnipotentIntegral F (n + 1) v ((GeneralLinear.Iwasawa.torus ϖ l)⁻¹ * x) →
          GeneralLinear.Iwasawa.exponent hϖ x = l := by
      intro l hl
      obtain ⟨u, hu, k, hk, hx⟩ := (isUnipotentIntegral_iff_exists v _).mp hl
      refine GeneralLinear.Iwasawa.exponent_eq hϖ
        (u := GeneralLinear.Iwasawa.torus ϖ l * u * (GeneralLinear.Iwasawa.torus ϖ l)⁻¹)
        (diagonalUnits_conj_mem_upperUnipotent v (fun i => ϖ ^ l i) hu)
        ((mem_localIntegral_iff_mem_integralSubgroup v n k).mp hk) ?_
      calc x = GeneralLinear.Iwasawa.torus ϖ l *
            ((GeneralLinear.Iwasawa.torus ϖ l)⁻¹ * x) := by group
        _ = _ := by
          rw [← hx]
          group
    exact (key lam h).symm.trans (key lam' h')

end Local

/-! ## The cells -/

section Cells

variable {F : Type u} [Field F] [NumberField F] {m : ℕ}

theorem localPoint_inv (v : FinitePlace F) (h : FiniteLocalGL F m v) :
    localPoint F m v h⁻¹ = (localPoint F m v h)⁻¹ := by
  simp only [localPoint, map_inv]

/-- `N_m(𝔸) ι_v(t)⁻¹ g ∈ U_S` exactly when `g` satisfies the condition of `U_(S ∪ {v})` and
`t⁻¹ g_v ∈ N_m(F_v) GL_m(𝒪_v)`. -/
theorem mk_localPoint_inv_mul_mem_iff {S : Finset (FinitePlace F)} {v : FinitePlace F}
    (hv : v ∉ S) (t : FiniteLocalGL F m v) (g : Points F m) :
    LeftCosetSpace.mk (unipotentAdelic F m) ((localPoint F m v t)⁻¹ * g) ∈
        unipotentIntegralClasses F m S ↔
      g ∈ unipotentIntegralOutside F m (insert v S) ∧
        IsUnipotentIntegral F m v (t⁻¹ * finiteComponent F m v g) := by
  rw [mk_mem_unipotentIntegralClasses_iff, ← localPoint_inv]
  constructor
  · intro h
    refine ⟨fun w hw => ?_, ?_⟩
    · have hwv : w ≠ v := fun e => hw (Finset.mem_insert.mpr (Or.inl e))
      have hwS : w ∉ S := fun e => hw (Finset.mem_insert.mpr (Or.inr e))
      have h1 := h w hwS
      rwa [finiteComponent_mul, LocalPointFactorization.finiteComponent_localPoint_of_ne F m hwv, one_mul] at h1
    · have h1 := h v hv
      rwa [finiteComponent_mul, LocalPointFactorization.finiteComponent_localPoint F m] at h1
  · rintro ⟨h1, h2⟩ w hw
    by_cases hwv : w = v
    · subst hwv
      rw [finiteComponent_mul, LocalPointFactorization.finiteComponent_localPoint F m]
      exact h2
    · rw [finiteComponent_mul, LocalPointFactorization.finiteComponent_localPoint_of_ne F m hwv, one_mul]
      exact h1 w (by simp [Finset.mem_insert, hwv, hw])

variable (m) in
/-- Left translation `T_λ : N_m(𝔸) g ↦ N_m(𝔸) ι_v(ϖ^λ) g`, as the Library's homeomorphism
`WhittakerQuotientScaling.leftShiftHomeomorph`. -/
def cellShift (v : FinitePlace F) (ϖ : (FiniteCompletion F v)ˣ) (lam : Fin m → ℤ) :
    WhittakerQuotient F m ≃ₜ WhittakerQuotient F m :=
  WhittakerQuotientScaling.leftShiftHomeomorph
    (localPoint F m v (GeneralLinear.Iwasawa.torus ϖ lam))
    (UnipotentConjugationModulus.conj_localPoint_torus_mem_iff F v ϖ lam)

theorem cellShift_symm_apply (v : FinitePlace F) (ϖ : (FiniteCompletion F v)ˣ)
    (lam : Fin m → ℤ) (q : WhittakerQuotient F m) :
    (cellShift m v ϖ lam).symm q = LeftCosetSpace.mk (unipotentAdelic F m)
      ((localPoint F m v (GeneralLinear.Iwasawa.torus ϖ lam))⁻¹ * q.out) := by
  rw [Homeomorph.symm_apply_eq, cellShift, WhittakerQuotientScaling.coe_leftShiftHomeomorph,
    WhittakerQuotientScaling.leftShift_mk _
      (UnipotentConjugationModulus.conj_localPoint_torus_mem_iff F v ϖ lam),
    mul_inv_cancel_left]
  exact (Quotient.out_eq q).symm

variable (m) in
/-- The cell `C_λ = T_λ(U_S)`. -/
def cell (S : Finset (FinitePlace F)) (v : FinitePlace F) (ϖ : (FiniteCompletion F v)ˣ)
    (lam : Fin m → ℤ) : Set (WhittakerQuotient F m) :=
  (cellShift m v ϖ lam).symm ⁻¹' unipotentIntegralClasses F m S

theorem mem_cell_iff {S : Finset (FinitePlace F)} {v : FinitePlace F} (hv : v ∉ S)
    (ϖ : (FiniteCompletion F v)ˣ) (lam : Fin m → ℤ) (q : WhittakerQuotient F m) :
    q ∈ cell m S v ϖ lam ↔
      q ∈ unipotentIntegralClasses F m (insert v S) ∧
        IsUnipotentIntegral F m v
          ((GeneralLinear.Iwasawa.torus ϖ lam)⁻¹ * finiteComponent F m v q.out) := by
  change (cellShift m v ϖ lam).symm q ∈ unipotentIntegralClasses F m S ↔ _
  rw [cellShift_symm_apply, mk_localPoint_inv_mul_mem_iff hv]
  rfl

theorem measurableSet_cell (S : Finset (FinitePlace F)) (v : FinitePlace F)
    (ϖ : (FiniteCompletion F v)ˣ) (lam : Fin m → ℤ) : MeasurableSet (cell m S v ϖ lam) :=
  (measurableSet_unipotentIntegralClasses m S).preimage
    (cellShift m v ϖ lam).symm.continuous.measurable

theorem pairwise_disjoint_cell {S : Finset (FinitePlace F)} {v : FinitePlace F} (hv : v ∉ S)
    {ϖ : (FiniteCompletion F v)ˣ}
    (hϖ : GeneralLinear.Iwasawa.IsUniformizingElement
      (Valued.v : Valuation (FiniteCompletion F v) (WithZero (Multiplicative ℤ))) ϖ) :
    Pairwise (Disjoint on fun lam : Fin m → ℤ => cell m S v ϖ lam) := by
  intro lam lam' hne
  refine Set.disjoint_left.mpr fun q h h' => hne ?_
  exact eq_of_isUnipotentIntegral_torus_inv_mul v hϖ ((mem_cell_iff hv ϖ lam q).mp h).2
    ((mem_cell_iff hv ϖ lam' q).mp h').2

theorem iUnion_cell {S : Finset (FinitePlace F)} {v : FinitePlace F} (hv : v ∉ S)
    {ϖ : (FiniteCompletion F v)ˣ}
    (hϖ : GeneralLinear.Iwasawa.IsUniformizingElement
      (Valued.v : Valuation (FiniteCompletion F v) (WithZero (Multiplicative ℤ))) ϖ) :
    ⋃ lam : Fin m → ℤ, cell m S v ϖ lam = unipotentIntegralClasses F m (insert v S) := by
  ext q
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨lam, h⟩
    exact ((mem_cell_iff hv ϖ lam q).mp h).1
  · intro hq
    obtain ⟨lam, hlam⟩ := exists_isUnipotentIntegral_torus_inv_mul v hϖ
      (finiteComponent F m v q.out)
    exact ⟨lam, (mem_cell_iff hv ϖ lam q).mpr ⟨hq, hlam⟩⟩

end Cells

/-! ## Change of variables -/

section ChangeOfVariables

variable {F : Type u} [Field F] [NumberField F] {m : ℕ}

/-- Each translate `f ∘ T_λ` of an integrable `f` is integrable on `U_S`. -/
theorem integrableOn_leftShift (S : Finset (FinitePlace F)) (v : FinitePlace F)
    {ϖ : (FiniteCompletion F v)ˣ}
    (hϖ : GeneralLinear.Iwasawa.IsUniformizingElement
      (Valued.v : Valuation (FiniteCompletion F v) (WithZero (Multiplicative ℤ))) ϖ)
    (lam : Fin m → ℤ) {f : WhittakerQuotient F m → ℂ}
    (hf : Integrable f (whittakerQuotientMeasure F m)) :
    IntegrableOn
      (fun q => f (WhittakerQuotientScaling.leftShift F m
        (localPoint F m v (GeneralLinear.Iwasawa.torus ϖ lam)) q))
      (unipotentIntegralClasses F m S) (whittakerQuotientMeasure F m) :=
  (WhittakerQuotientScaling.integrable_comp_leftShift _
    (UnipotentConjugationModulus.conj_localPoint_torus_mem_iff F v ϖ lam)
    (WhittakerQuotientScaling.map_leftShift_localPoint_torus v hϖ lam) hf).integrableOn

/-- `q_v ^ (∑_(i<j)(λ_i-λ_j)) ∫_(U_S) f ∘ T_λ = ∫_(C_λ) f`. -/
theorem absNorm_zpow_mul_setIntegral_leftShift (S : Finset (FinitePlace F))
    (v : FinitePlace F) {ϖ : (FiniteCompletion F v)ˣ}
    (hϖ : GeneralLinear.Iwasawa.IsUniformizingElement
      (Valued.v : Valuation (FiniteCompletion F v) (WithZero (Multiplicative ℤ))) ϖ)
    (lam : Fin m → ℤ) (f : WhittakerQuotient F m → ℂ) :
    ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ modulusExponent lam *
        ∫ q in unipotentIntegralClasses F m S,
          f (WhittakerQuotientScaling.leftShift F m
            (localPoint F m v (GeneralLinear.Iwasawa.torus ϖ lam)) q)
          ∂whittakerQuotientMeasure F m =
      ∫ q in cell m S v ϖ lam, f q ∂whittakerQuotientMeasure F m := by
  have hNC : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  rw [WhittakerQuotientScaling.setIntegral_comp_leftShift _
      (UnipotentConjugationModulus.conj_localPoint_torus_mem_iff F v ϖ lam)
      (WhittakerQuotientScaling.map_leftShift_localPoint_torus v hϖ lam),
    NNReal.coe_zpow, NNReal.coe_natCast, Complex.real_smul, Complex.ofReal_zpow,
    Complex.ofReal_natCast, ← mul_assoc, ← zpow_add₀ hNC, add_neg_cancel, zpow_zero, one_mul]
  rfl

end ChangeOfVariables

end Langlands.Global.RankinSelbergGlobal.WhittakerCell

namespace Langlands.Global.RankinSelbergGlobal

open WhittakerCell

/-- **One-place Iwasawa cell decomposition of `N_m(𝔸) \ GL_m(𝔸)`.** -/
theorem whittakerCellDecomposition : WhittakerCellDecompositionStatement.{u} := by
  intro F _ _ m S v hv ϖ hϖ f hf shift
  have hs : ∀ lam q, shift lam q = WhittakerQuotientScaling.leftShift F m
      (localPoint F m v (GeneralLinear.Iwasawa.torus ϖ lam)) q := fun _ _ => rfl
  simp only [hs]
  refine ⟨fun lam => integrableOn_leftShift S v hϖ lam hf, ?_⟩
  simp only [absNorm_zpow_mul_setIntegral_leftShift S v hϖ _ f]
  rw [← iUnion_cell hv hϖ]
  exact hasSum_integral_iUnion (measurableSet_cell S v ϖ) (pairwise_disjoint_cell hv hϖ)
    hf.integrableOn

end Langlands.Global.RankinSelbergGlobal
