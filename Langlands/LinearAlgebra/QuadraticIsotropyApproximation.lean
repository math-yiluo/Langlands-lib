import Langlands.Global.AdelicFunctoriality.MixedWeakApproximation
import Langlands.Global.LocalModularCharacter.HaarScaleNorm
import Langlands.LinearAlgebra.LocalQuadraticAnisotropicDimensionBound
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Algebra.Valued.ValuativeRel

/-! # Weak approximation reduces diagonal quadratic isotropy by one variable -/

noncomputable section

universe u

open NumberField QuadraticMap Filter WithZeroTopology
open scoped Topology

namespace Langlands.QuadraticIsotropy

private theorem finiteCompletion_square_neighborhood {F : Type u} [Field F] [NumberField F]
    (v : Global.FinitePlace F) :
    ∃ U : Set (Global.FiniteCompletion F v), IsOpen U ∧ 1 ∈ U ∧
      ∀ z ∈ U, ∃ s, s ^ 2 = z := by
  let A := Global.FiniteCompletion F v
  let := Global.FiniteCompletion.valuativeRel v
  have := Global.FiniteCompletion.isNonarchimedeanLocalField v
  let f : A → A := fun z => (1 - z) / 4
  let U : Set A := (fun z => ValuativeRel.valuation A (f z)) ⁻¹' Set.Iio 1
  have hf : Continuous f := by
    simpa only [f, div_eq_mul_inv, Pi.sub_apply] using
      (continuous_const.sub continuous_id : Continuous (fun z : A => 1 - z)).mul_const
        ((4 : A)⁻¹)
  refine ⟨U, WithZeroTopology.isOpen_Iio.preimage
    (IsValuativeTopology.continuous_valuation.comp hf), ?_, ?_⟩
  · change ValuativeRel.valuation A (f 1) < 1
    simp [f]
  · intro z hz
    change ValuativeRel.valuation A (f z) < 1 at hz
    obtain ⟨s, hs⟩ := LocalQuadraticAnisotropic.exists_root_sq_add_self_add (f z) hz
    refine ⟨2 * s + 1, ?_⟩
    have h4 : (4 : A) ≠ 0 := by
      intro h
      have hm : algebraMap F A 4 = algebraMap F A 0 := by simpa only [map_ofNat, map_zero] using h
      exact (by norm_num : (4 : F) ≠ 0) ((algebraMap F A).injective hm)
    have ht : (4 : A) * f z = 1 - z := by
      dsimp only [f]
      rw [mul_comm, div_mul_cancel₀ _ h4]
    linear_combination 4 * hs - ht

private theorem infiniteCompletion_square_neighborhood {F : Type u} [Field F] [NumberField F]
    (v : InfinitePlace F) :
    ∃ U : Set v.Completion, IsOpen U ∧ 1 ∈ U ∧ ∀ z ∈ U, ∃ s, s ^ 2 = z := by
  rcases v.isReal_or_isComplex with hr | hc
  · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hr
    let U : Set v.Completion := e ⁻¹' Set.Ioi 0
    have he : Continuous e :=
      (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hr).continuous
    refine ⟨U, isOpen_Ioi.preimage he, ?_, ?_⟩
    · change (0 : ℝ) < e 1
      rw [map_one]
      exact zero_lt_one
    · intro z hz
      change (0 : ℝ) < e z at hz
      refine ⟨e.symm (Real.sqrt (e z)), e.injective ?_⟩
      rw [map_pow, e.apply_symm_apply, Real.sq_sqrt hz.le]
  · let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hc
    refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun z _ => ?_⟩
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (e z) zero_lt_two
    exact ⟨e.symm s, e.injective (by rw [map_pow, e.apply_symm_apply, hs])⟩

private theorem placeCompletion_square_neighborhood {F : Type u} [Field F] [NumberField F]
    (v : Global.Place F) :
    ∃ U : Set (Global.placeCompletion F v), IsOpen U ∧ 1 ∈ U ∧
      ∀ z ∈ U, ∃ s, s ^ 2 = z := by
  rcases v with v | v
  · exact infiniteCompletion_square_neighborhood v
  · exact finiteCompletion_square_neighborhood v

private theorem exists_open_rectangle {A : Type*} [TopologicalSpace A] {U : Set (A × A)}
    (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ X Y : Set A, IsOpen X ∧ X.Nonempty ∧ IsOpen Y ∧ Y.Nonempty ∧ Set.prod X Y ⊆ U := by
  obtain ⟨⟨x, y⟩, hxy⟩ := hne
  obtain ⟨X, hX, Y, hY, hsub⟩ := mem_nhds_prod_iff.mp (hU.mem_nhds hxy)
  refine ⟨interior X, interior Y, isOpen_interior, ⟨x, mem_interior_iff_mem_nhds.mpr hX⟩,
    isOpen_interior, ⟨y, mem_interior_iff_mem_nhds.mpr hY⟩, ?_⟩
  exact (Set.prod_mono interior_subset interior_subset).trans hsub

private theorem exists_pair_mem_open {F : Type u} [Field F] [NumberField F]
    (S : Finset (Global.FinitePlace F))
    (finiteOpens : ∀ p : S, Set (Global.FiniteCompletion F p.1 × Global.FiniteCompletion F p.1))
    (infiniteOpens : ∀ v : InfinitePlace F, Set (v.Completion × v.Completion))
    (hf : ∀ p, IsOpen (finiteOpens p) ∧ (finiteOpens p).Nonempty)
    (ha : ∀ v, IsOpen (infiniteOpens v) ∧ (infiniteOpens v).Nonempty) :
    ∃ x y : F,
      (∀ p, (algebraMap F (Global.FiniteCompletion F p.1) x,
        algebraMap F (Global.FiniteCompletion F p.1) y) ∈ finiteOpens p) ∧
      (∀ v, (algebraMap F v.Completion x, algebraMap F v.Completion y) ∈ infiniteOpens v) := by
  choose X Y hX hXne hY hYne hXY using fun p => exists_open_rectangle (hf p).1 (hf p).2
  choose U V hU hUne hV hVne hUV using fun v => exists_open_rectangle (ha v).1 (ha v).2
  obtain ⟨x, hxf, hxa⟩ :=
    Global.AdelicFunctoriality.exists_algebraMap_mem_open S X hX hXne U hU hUne
  obtain ⟨y, hyf, hya⟩ :=
    Global.AdelicFunctoriality.exists_algebraMap_mem_open S Y hY hYne V hV hVne
  exact ⟨x, y, fun p => hXY p ⟨hxf p, hyf p⟩, fun v => hUV v ⟨hxa v, hya v⟩⟩

section Evaluation

variable {K : Type*} [CommRing K] {n : ℕ}

/-- Evaluating a weighted sum of squares after adding a scalar coordinate. -/
theorem weightedSumSquares_cons (a : K) (w : Fin n → K) (s : K) (x : Fin n → K) :
    weightedSumSquares K (Fin.cons a w) (Fin.cons s x) =
      a * s ^ 2 + weightedSumSquares K w x := by
  simp [weightedSumSquares_apply, Fin.sum_univ_succ, pow_two]

private def binaryValue (a b : K) (z : K × K) : K :=
  a * z.1 ^ 2 + b * z.2 ^ 2

private theorem weightedSumSquares_two_cons (a b : K) (w : Fin n → K) (s t : K) (x : Fin n → K) :
    weightedSumSquares K (Fin.cons a (Fin.cons b w)) (Fin.cons s (Fin.cons t x)) =
      binaryValue a b (s, t) + weightedSumSquares K w x := by
  rw [weightedSumSquares_cons, weightedSumSquares_cons, binaryValue, add_assoc]

private theorem zero_of_zero_cons {s : K} {x : Fin n → K}
    (h : (Fin.cons s x : Fin (n + 1) → K) = 0) :
    s = 0 ∧ x = 0 := by
  exact ⟨by simpa using congrFun h 0, funext fun i => by simpa using congrFun h i.succ⟩

private theorem cons_eq_zero {s : K} {x : Fin n → K} (hs : s = 0) (hx : x = 0) :
    (Fin.cons s x : Fin (n + 1) → K) = 0 := by
  subst s x
  ext i
  exact Fin.cases (by simp) (fun j => by simp) i

private theorem isotropic_cons_of_isotropic (c : K) {w : Fin n → K}
    (h : ¬ (weightedSumSquares K w).Anisotropic) :
    ¬ (weightedSumSquares K (Fin.cons c w)).Anisotropic := by
  obtain ⟨x, hx, hz⟩ := (not_anisotropic_iff_exists _).mp h
  refine (not_anisotropic_iff_exists _).mpr ⟨Fin.cons 0 x, fun e => hx (zero_of_zero_cons e).2, ?_⟩
  rw [weightedSumSquares_cons, hz]
  simp

end Evaluation

section Diagonal

variable {K : Type*} [Field K] {n : ℕ}

private theorem binary_represents_of_isotropic (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (h2 : (2 : K) ≠ 0) (s t : K) (hne : s ≠ 0 ∨ t ≠ 0) (hz : binaryValue a b (s, t) = 0)
    (c : K) : ∃ z : K × K, binaryValue a b z = c := by
  have hs : s ≠ 0 := by
    intro hs
    have hh : b * t ^ 2 = 0 := by simpa [binaryValue, hs] using hz
    exact (hne.resolve_left (not_not_intro hs))
      (sq_eq_zero_iff.mp ((mul_eq_zero.mp hh).resolve_left hb))
  let k := (c - a) / (2 * a * s)
  refine ⟨(1 + k * s, k * t), ?_⟩
  calc
    binaryValue a b (1 + k * s, k * t) =
        a + k * (2 * a * s) + k ^ 2 * binaryValue a b (s, t) := by simp only [binaryValue]; ring
    _ = c := by
      rw [hz, mul_zero, add_zero]
      dsimp only [k]
      rw [div_mul_cancel₀ _ (mul_ne_zero (mul_ne_zero h2 ha) hs)]
      ring

private theorem common_nonzero_value {n : ℕ} (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (h2 : (2 : K) ≠ 0) (w : Fin (n + 1) → K) (hw : (weightedSumSquares K w).Anisotropic)
    (hloc : ¬ (weightedSumSquares K (Fin.cons a (Fin.cons b w))).Anisotropic) :
    ∃ z : K × K, ∃ x : Fin (n + 1) → K,
      binaryValue a b z ≠ 0 ∧ binaryValue a b z + weightedSumSquares K w x = 0 := by
  obtain ⟨y, hy, hz⟩ := (not_anisotropic_iff_exists _).mp hloc
  let x := Fin.tail (Fin.tail y)
  let z := (y 0, Fin.tail y 0)
  have he : y = Fin.cons z.1 (Fin.cons z.2 x) := by
    simp only [z, x, Fin.cons_self_tail]
  have hzero : binaryValue a b z + weightedSumSquares K w x = 0 := by
    rw [he, weightedSumSquares_two_cons] at hz
    exact hz
  by_cases hx : x = 0
  · have hbin : binaryValue a b z = 0 := by simpa [hx] using hzero
    have hne : z.1 ≠ 0 ∨ z.2 ≠ 0 := by
      by_contra! hh
      exact hy (he.trans (cons_eq_zero hh.1 (cons_eq_zero hh.2 hx)))
    let x' : Fin (n + 1) → K := fun _ => 1
    have hx' : x' ≠ 0 := by intro h; simpa [x'] using congrFun h 0
    have hv : weightedSumSquares K w x' ≠ 0 := fun h => hx' (hw x' h)
    obtain ⟨z', hrep⟩ := binary_represents_of_isotropic a b ha hb h2 z.1 z.2 hne hbin
      (-(weightedSumSquares K w x'))
    exact ⟨z', x', hrep.symm ▸ neg_ne_zero.mpr hv, by rw [hrep, neg_add_cancel]⟩
  · refine ⟨z, x, fun h => hx (hw x ?_), hzero⟩
    simpa [h] using hzero

private theorem exists_open_reduced_isotropy [TopologicalSpace K] [IsTopologicalRing K] [T1Space K]
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) (h2 : (2 : K) ≠ 0)
    (w : Fin (n + 1) → K)
    (hsq : ∃ U : Set K, IsOpen U ∧ 1 ∈ U ∧ ∀ z ∈ U, ∃ s, s ^ 2 = z)
    (hloc : ¬ (weightedSumSquares K (Fin.cons a (Fin.cons b w))).Anisotropic) :
    ∃ U : Set (K × K), IsOpen U ∧ U.Nonempty ∧
      ∀ z ∈ U, binaryValue a b z ≠ 0 ∧
        ¬ (weightedSumSquares K (Fin.cons (binaryValue a b z) w)).Anisotropic := by
  have hc : Continuous (binaryValue a b) :=
    (continuous_const.mul (continuous_fst.pow 2)).add (continuous_const.mul (continuous_snd.pow 2))
  let nz := binaryValue a b ⁻¹' {0}ᶜ
  have hnz : IsOpen nz := isOpen_compl_singleton.preimage hc
  by_cases hw : (weightedSumSquares K w).Anisotropic
  · obtain ⟨z, x, hd, hzero⟩ := common_nonzero_value a b ha hb h2 w hw hloc
    obtain ⟨U, hU, h₁, hs⟩ := hsq
    let d := binaryValue a b z
    let W := (fun p => binaryValue a b p * d⁻¹) ⁻¹' U ∩ nz
    refine ⟨W, (hU.preimage (hc.mul_const _)).inter hnz, ⟨z, ?_⟩, ?_⟩
    · exact ⟨by simpa [d, hd] using h₁, hd⟩
    · intro p hp
      obtain ⟨s, hs⟩ := hs _ hp.1
      have he : binaryValue a b p = s ^ 2 * d := by
        rw [hs, mul_assoc, inv_mul_cancel₀ hd, mul_one]
      refine ⟨hp.2, (not_anisotropic_iff_exists _).mpr ⟨Fin.cons 1 (s • x), ?_, ?_⟩⟩
      · exact fun h => one_ne_zero (zero_of_zero_cons h).1
      · rw [weightedSumSquares_cons, one_pow, mul_one, QuadraticMap.map_smul, smul_eq_mul, he,
          ← pow_two, ← mul_add]
        change s ^ 2 * (binaryValue a b z + weightedSumSquares K w x) = 0
        rw [hzero, mul_zero]
  · refine ⟨nz, hnz, ⟨(1, 0), ?_⟩, fun p hp => ⟨hp, isotropic_cons_of_isotropic _ hw⟩⟩
    change binaryValue a b (1, 0) ≠ 0
    simpa [binaryValue]

private theorem isotropic_of_reduced_isotropy {a b : K} {w : Fin n → K} (p : K × K)
    (hc : binaryValue a b p ≠ 0)
    (h : ¬ (weightedSumSquares K (Fin.cons (binaryValue a b p) w)).Anisotropic) :
    ¬ (weightedSumSquares K (Fin.cons a (Fin.cons b w))).Anisotropic := by
  obtain ⟨x, hx, hz⟩ := (not_anisotropic_iff_exists _).mp h
  let s := x 0
  let y := Fin.tail x
  have he : x = Fin.cons s y := (Fin.cons_self_tail x).symm
  rw [he, weightedSumSquares_cons] at hz
  refine (not_anisotropic_iff_exists _).mpr
    ⟨Fin.cons (s * p.1) (Fin.cons (s * p.2) y), ?_, ?_⟩
  · intro hzero
    obtain ⟨h₁, h₂⟩ := zero_of_zero_cons hzero
    obtain ⟨h₂, h₃⟩ := zero_of_zero_cons h₂
    have hs : s = 0 := by
      by_contra hs
      apply hc
      simp [binaryValue, (mul_eq_zero.mp h₁).resolve_left hs, (mul_eq_zero.mp h₂).resolve_left hs]
    exact hx (he.trans (cons_eq_zero hs h₃))
  · rw [weightedSumSquares_two_cons, ← hz]
    congr 1
    simp only [binaryValue]
    ring

end Diagonal

/-- Reduce two diagonal coordinates to their value on a global vector. Weak approximation makes
this reduction preserve local isotropy whenever the tail is isotropic at almost every finite
place. The supplied local-to-global implication then applies to the shorter form. -/
def DiagonalIsotropyRankReductionStatement : Prop :=
  ∀ {F : Type u} [Field F] [NumberField F] {n : ℕ}
    (a b : F), a ≠ 0 → b ≠ 0 → ∀ (w : Fin (n + 1) → F),
      (∀ᶠ v : Global.FinitePlace F in cofinite,
        ¬ (weightedSumSquares (Global.FiniteCompletion F v)
          (fun i => algebraMap F (Global.FiniteCompletion F v) (w i))).Anisotropic) →
      (∀ v : Global.Place F, ¬ (weightedSumSquares (Global.placeCompletion F v)
        (Fin.cons (algebraMap F (Global.placeCompletion F v) a)
          (Fin.cons (algebraMap F (Global.placeCompletion F v) b)
            (fun i => algebraMap F (Global.placeCompletion F v) (w i))))).Anisotropic) →
      (∀ c : F, c ≠ 0 →
        (∀ v : Global.Place F, ¬ (weightedSumSquares (Global.placeCompletion F v)
          (Fin.cons (algebraMap F (Global.placeCompletion F v) c)
            (fun i => algebraMap F (Global.placeCompletion F v) (w i)))).Anisotropic) →
        ¬ (weightedSumSquares F (Fin.cons c w)).Anisotropic) →
      ¬ (weightedSumSquares F (Fin.cons a (Fin.cons b w))).Anisotropic

/-- Weak approximation gives the rank reduction for diagonal isotropy. -/
theorem diagonal_isotropic_of_tail_cofinite : DiagonalIsotropyRankReductionStatement.{u} := by
  intro F _ _ n a b ha hb w hcofinite hloc hsmaller
  classical
  have hU (v : Global.Place F) :
      ∃ U : Set (Global.placeCompletion F v × Global.placeCompletion F v),
        IsOpen U ∧ U.Nonempty ∧ ∀ p ∈ U,
          binaryValue (algebraMap F (Global.placeCompletion F v) a)
              (algebraMap F (Global.placeCompletion F v) b) p ≠ 0 ∧
          ¬ (weightedSumSquares (Global.placeCompletion F v)
            (Fin.cons (binaryValue (algebraMap F (Global.placeCompletion F v) a)
              (algebraMap F (Global.placeCompletion F v) b) p)
              (fun i => algebraMap F (Global.placeCompletion F v) (w i)))).Anisotropic := by
    let A := Global.placeCompletion F v
    let : Field A := (Global.placeCompletion.isField F v).toField
    have map_nonzero (d : F) (hd : d ≠ 0) : algebraMap F A d ≠ 0 :=
      fun h => hd ((algebraMap F A).injective (h.trans (map_zero _).symm))
    have h2 : (2 : A) ≠ 0 := by simpa only [map_ofNat] using map_nonzero 2 two_ne_zero
    exact exists_open_reduced_isotropy _ _ (map_nonzero a ha) (map_nonzero b hb) h2 _
      (placeCompletion_square_neighborhood v) (hloc v)
  choose U hUopen hUne hUcondition using hU
  let S := (Filter.eventually_cofinite.mp hcofinite).toFinset
  obtain ⟨x, y, hfin, hinf⟩ := exists_pair_mem_open S
    (fun p => U (.inr p.1)) (fun v => U (.inl v))
    (fun p => ⟨hUopen _, hUne _⟩) (fun v => ⟨hUopen _, hUne _⟩)
  let c := binaryValue a b (x, y)
  have hmap (v : Global.Place F) :
      algebraMap F (Global.placeCompletion F v) c =
        binaryValue (algebraMap F (Global.placeCompletion F v) a)
          (algebraMap F (Global.placeCompletion F v) b)
          (algebraMap F (Global.placeCompletion F v) x,
            algebraMap F (Global.placeCompletion F v) y) := by
    simp [c, binaryValue]
  have hc : c ≠ 0 := by
    let v : InfinitePlace F := Classical.choice inferInstance
    have h := (hUcondition (.inl v) _ (hinf v)).1
    exact fun hz => h ((hmap (.inl v)).symm.trans (by rw [hz, map_zero]))
  apply isotropic_of_reduced_isotropy (x, y) hc
  apply hsmaller c hc
  intro v
  rw [hmap]
  rcases v with v | v
  · exact (hUcondition (.inl v) _ (hinf v)).2
  · by_cases hv : v ∈ S
    · exact (hUcondition (.inr v) _ (hfin ⟨v, hv⟩)).2
    · apply isotropic_cons_of_isotropic
      change ¬ (weightedSumSquares (Global.FiniteCompletion F v)
        (fun i => algebraMap F (Global.FiniteCompletion F v) (w i))).Anisotropic
      simpa [S] using hv

end Langlands.QuadraticIsotropy
