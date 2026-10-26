import Langlands.Representation.RankinSelberg.UnequalRankZeroRowRootExpansionStatement
import Langlands.Representation.RankinSelberg.RootFiniteFunctionProof
import Langlands.Representation.RankinSelberg.RootSpectralWeightProof
import Langlands.Group.GL.NormalizedCharacter
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear
open scoped BigOperators

universe uF uV uW

private def padOnes {M : Type*} [One M] {r t : ℕ}
    (x : Fin r → M) (i : Fin t) : M :=
  if hi : i.val < r then x ⟨i.val, hi⟩ else 1

private def padOnesHom (M : Type*) [Monoid M] (r t : ℕ) :
    (Fin r → M) →* (Fin t → M) where
  toFun := padOnes
  map_one' := by
    ext i
    simp [padOnes]
  map_mul' x y := by
    ext i
    simp only [padOnes, Pi.mul_apply]
    split_ifs <;> simp

private theorem continuous_padOnes {M : Type*} [One M]
    [TopologicalSpace M] (r t : ℕ) :
    Continuous (padOnes (M := M) (r := r) (t := t)) := by
  apply continuous_pi
  intro i
  dsimp [padOnes]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

private theorem appendIdentity_diagonalUnits {F : Type*} [Field F]
    (n d : ℕ) (b : Fin (n + 1) → Fˣ) :
    appendIdentity n d (Iwasawa.diagonalUnits b) =
      Iwasawa.diagonalUnits (padOnes b) := by
  apply Units.ext
  ext i j
  rw [appendIdentity_entry]
  simp only [Iwasawa.diagonalUnits_val, Matrix.diagonal_apply, padOnes]
  by_cases hij : i = j
  · subst j
    by_cases hi : i.val < n + 1 <;> simp [hi]
  · have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
    split_ifs <;> simp_all

private theorem padded_root_coordinates {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n k : ℕ) :
    letI := T.topology
    let d := fun (a : Fin (n + 1) → F.Carrierˣ) (i : Fin (n + 1)) =>
      ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
    ∀ a, (fun i : Fin (n + (0 + k + 1)) =>
      ((padOnes (t := n + (0 + k + 1) + 1) (d a) i.castSucc /
        padOnes (t := n + (0 + k + 1) + 1) (d a) i.succ : F.Carrierˣ) :
          F.Carrier)) =
        padOnes (t := n + (0 + k + 1)) (fun j => (a j : F.Carrier)) := by
  let := T.topology
  dsimp only
  intro a
  have hcoord := (rootCoordinateChange F T n).2.2.2.2.2.2 a
  funext i
  by_cases hi : i.val < n
  · have hi₀ : i.val < n + 1 := by omega
    have hi₁ : i.val + 1 < n + 1 := by omega
    simpa [padOnes, hi₀, hi₁, Fin.le_def] using
      congrArg (fun x : F.Carrierˣ => (x : F.Carrier))
        (hcoord.1 ⟨i.val, hi⟩)
  · by_cases hin : i.val = n
    · have hi₀ : i.val < n + 1 := by omega
      have hi₁ : ¬ i.val + 1 < n + 1 := by omega
      have he : (⟨i.val, hi₀⟩ : Fin (n + 1)) = Fin.last n := Fin.ext hin
      simp only [padOnes, Fin.val_castSucc, Fin.val_succ, dite_eq_left hi₀,
        dite_eq_right hi₁, div_one, he]
      exact congrArg (fun x : F.Carrierˣ => (x : F.Carrier)) hcoord.2.1
    · have hi₀ : ¬ i.val < n + 1 := by omega
      have hi₁ : ¬ i.val + 1 < n + 1 := by omega
      simp [padOnes, hi₀, hi₁]

private theorem paddedSchwartzProduct {F : Type*} [Field F] [TopologicalSpace F]
    [T2Space F] (n k : ℕ)
    (φ : SchwartzBruhat (Fin (n + (0 + k + 1)) → F))
    (φ' : SchwartzBruhat (Fin n → F)) :
    ∃ Ψ : SchwartzBruhat (Fin (n + 1) → F),
      ∀ x, Ψ x = φ (padOnes x) * φ' (fun i : Fin n => x i.castSucc) := by
  let e : (Fin (n + 1) → F) → (Fin (n + (0 + k + 1)) → F) := padOnes
  let P : (Fin (n + (0 + k + 1)) → F) → (Fin (n + 1) → F) :=
    fun y i => y ⟨i.val, by omega⟩
  have he : Continuous e := continuous_padOnes _ _
  have hP : Continuous P := continuous_pi fun _ => continuous_apply _
  have hPe (x : Fin (n + 1) → F) : P (e x) = x := by
    funext i
    simp [P, e, padOnes, i.isLt]
  let f : (Fin (n + 1) → F) → ℂ :=
    fun x => φ (e x) * φ' (fun i : Fin n => x i.castSucc)
  have hlc : IsLocallyConstant f :=
    (φ.locallyConstant.comp_continuous he).comp₂
      (φ'.locallyConstant.comp_continuous
        (continuous_pi fun _ => continuous_apply _)) (· * ·)
  have hcompact : IsCompact (P '' tsupport (φ : (Fin (n + (0 + k + 1)) → F) → ℂ)) :=
    φ.hasCompactSupport.image hP
  have hsupp : HasCompactSupport f := by
    apply HasCompactSupport.of_support_subset_isCompact hcompact
    intro x hx
    have hxφ : φ (e x) ≠ 0 := (mul_ne_zero_iff.mp hx).1
    exact ⟨e x, subset_tsupport _ hxφ, hPe x⟩
  exact ⟨⟨f, hlc, hsupp⟩, fun _ => rfl⟩

private def rootPowerHom {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) (β : ℂ) :
    (Fin (n + 1) → F.Carrierˣ) →* ℂ where
  toFun a := ∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^
    ((i.val + 1 : ℂ) * β)
  map_one' := by
    simp [T.normalizedAbs_one]
  map_mul' a b := by
    simp only [Pi.mul_apply, Units.val_mul, T.normalizedAbs_mul, Complex.ofReal_mul]
    simp_rw [Complex.mul_cpow_ofReal_nonneg
      (T.normalizedAbs_nonneg _) (T.normalizedAbs_nonneg _)]
    exact Finset.prod_mul_distrib

private theorem continuous_rootPowerHom {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) (β : ℂ) :
    letI := T.topology
    Continuous (rootPowerHom F T n β) := by
  let := T.topology
  have habs : Continuous T.normalizedAbs :=
    continuous_subtype_val.comp T.continuous_normalizedAbsHom
  change Continuous (fun a : Fin (n + 1) → F.Carrierˣ =>
    ∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^ ((i.val + 1 : ℂ) * β))
  apply continuous_finsetProd
  intro i _
  exact (Complex.continuous_ofReal.comp
    (habs.comp (Units.continuous_val.comp (continuous_apply i)))).cpow
      continuous_const (fun a => Complex.ofReal_mem_slitPlane.mpr
        (T.normalizedAbs_pos (a i).ne_zero))

private theorem rootPowerHom_add {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) (s t : ℂ)
    (a : Fin (n + 1) → F.Carrierˣ) :
    rootPowerHom F T n (s + t) a =
      rootPowerHom F T n s a * rootPowerHom F T n t a := by
  change (∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^
    ((i.val + 1 : ℂ) * (s + t))) =
    (∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^ ((i.val + 1 : ℂ) * s)) *
    (∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^ ((i.val + 1 : ℂ) * t))
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [mul_add, Complex.cpow_add]
  exact Complex.ofReal_ne_zero.mpr (T.normalizedAbs_pos (a i).ne_zero).ne'

/-- The two supplied full-torus expansions give the uniform zero-row expansion
of the actual unequal-rank coefficient integrand at integral right translates. -/
theorem unequalRankZeroRowRootExpansion {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n k : ℕ) :
    UnequalRankZeroRowRootExpansionStatement.{uF,uV,uW} F T n k := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have := T.fieldT2
  let A := Fin (n + 1) → F.Carrierˣ
  let B := Fin (n + (0 + k + 1) + 1) → F.Carrierˣ
  let d : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
  let w : A → ℂ := fun a =>
    (∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^
      ((i.val + 1) * (n - i.val)))⁻¹
  let β : ℂ := -(((0 + k + 1 : ℕ) : ℂ) / 2)
  let c : A →* ℂ := rootPowerHom F T n β
  intro V _ _ W _ _ π σ ψ hπ hσ
  obtain ⟨X, hX, hπ⟩ := hπ
  obtain ⟨Y, hY, hσ⟩ := hσ
  let I := {χ // χ ∈ X} × {χ // χ ∈ Y}
  let η : I → A → ℂ := fun t a =>
    t.1.val (padOnes (d a)) * t.2.val (d a) * w a * c a
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  have hη (t : I) : Continuous (η t) ∧
      FiniteDimensional ℂ (Submodule.span ℂ
        (Set.range fun b : A => fun a : A => η t (b * a))) := by
    have hpull := (finiteFunctionClosure B A).2.1
      (padOnesHom F.Carrierˣ (n + 1) (n + (0 + k + 1) + 1))
      (continuous_padOnes _ _) t.1.val (hX _ t.1.property)
    have hprod := (rootCoordinateFiniteFunction F T n).2.2.2
      (fun b : A => t.1.val (padOnes b)) t.2.val hpull (hY _ t.2.property)
    exact (finiteFunctionClosure A A).1 _ _ hprod
      ((finiteFunctionClosure A A).2.2 c (continuous_rootPowerHom F T n β))
  refine ⟨Fintype.card I, fun j => η (e.symm j), fun j => hη (e.symm j), ?_⟩
  intro ℓ ℓ' f f' z
  obtain ⟨φ, hφ⟩ := hπ ℓ
    (modelRepresentation π ℓ (appendIdentity n (0 + k + 1) z.val) f)
  obtain ⟨φ', hφ'⟩ := hσ ℓ' (modelRepresentation σ ℓ' z.val f')
  have hf (a : A) :
      f.val.val (appendIdentity n (0 + k + 1) (Iwasawa.diagonalUnits (d a) * z.val)) =
        ∑ χ : {χ // χ ∈ X},
          φ χ.val (padOnes (fun j => (a j : F.Carrier))) *
            χ.val (padOnes (d a)) := by
    rw [map_mul, appendIdentity_diagonalUnits]
    have h := hφ (padOnes (d a))
    change f.val.val (Iwasawa.diagonalUnits (padOnes (d a)) *
      appendIdentity n (0 + k + 1) z.val) = _ at h
    rw [padded_root_coordinates F T n k a] at h
    exact h.trans (Finset.sum_coe_sort X _).symm
  have hf' (a : A) :
      f'.val.val (Iwasawa.diagonalUnits (d a) * z.val) =
        ∑ χ : {χ // χ ∈ Y},
          φ' χ.val (fun i : Fin n => (a i.castSucc : F.Carrier)) * χ.val (d a) := by
    have h := hφ' (d a)
    change f'.val.val (Iwasawa.diagonalUnits (d a) * z.val) = _ at h
    have hroot : (fun i : Fin n =>
        (((d a) i.castSucc / (d a) i.succ : F.Carrierˣ) : F.Carrier)) =
          (fun i : Fin n => (a i.castSucc : F.Carrier)) := by
      funext i
      exact congrArg (fun x : F.Carrierˣ => (x : F.Carrier))
        (((rootCoordinateChange F T n).2.2.2.2.2.2 a).1 i)
    rw [hroot] at h
    exact h.trans (Finset.sum_coe_sort Y _).symm
  choose Ψ hΨ using fun t : I =>
    paddedSchwartzProduct n k (φ t.1.val) (φ' t.2.val)
  refine ⟨fun j => Ψ (e.symm j), ?_⟩
  intro a s
  have hweight :
      determinantWeight (normalizedAbsoluteValue T)
        (Iwasawa.diagonalUnits (d a) * z.val) (s - ((0 + k + 1 : ℕ) : ℂ) / 2) =
          c a * ∏ j, (T.normalizedAbs (a j : F.Carrier) : ℂ) ^
            ((j.val + 1 : ℂ) * s) := by
    have h := (rootSpectralWeight F T n).2 a z.val
      ((rootSpectralWeight F T n).1 z) (s + β)
    change determinantWeight (normalizedAbsoluteValue T)
      (Iwasawa.diagonalUnits (d a) * z.val) (s + β) = _
    rw [h.1]
    change rootPowerHom F T n (s + β) a =
      rootPowerHom F T n β a * rootPowerHom F T n s a
    rw [rootPowerHom_add, mul_comm]
  calc
    unequalRankFunction ψ (normalizedAbsoluteValue T) 0 k f.val f'.val s 0
        (Iwasawa.diagonalUnits (d a) * z.val) * w a =
      ∑ t : I, Ψ t (fun j => (a j : F.Carrier)) * η t a *
        ∏ j, (T.normalizedAbs (a j : F.Carrier) : ℂ) ^
          ((j.val + 1 : ℂ) * s) := by
            rw [unequalRankFunction, unequalRankMatrix_zero_rows, hf, hf', hweight]
            dsimp only [η]
            simp_rw [hΨ]
            rw [Fintype.sum_prod_type, Fintype.sum_mul_sum]
            simp_rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro χ _
            apply Finset.sum_congr rfl
            intro χ' _
            ring
    _ = ∑ j, Ψ (e.symm j) (fun j => (a j : F.Carrier)) * η (e.symm j) a *
        ∏ j, (T.normalizedAbs (a j : F.Carrier) : ℂ) ^
          ((j.val + 1 : ℂ) * s) :=
      (e.symm.sum_comp (fun t : I =>
        Ψ t (fun j => (a j : F.Carrier)) * η t a *
          ∏ j, (T.normalizedAbs (a j : F.Carrier) : ℂ) ^
            ((j.val + 1 : ℂ) * s))).symm

end Langlands.RankinSelberg
