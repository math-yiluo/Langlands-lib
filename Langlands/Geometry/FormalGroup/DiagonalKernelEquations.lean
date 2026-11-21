import Langlands.Geometry.FormalGroup.FormalCyclicCoordinates
import Langlands.Geometry.FormalGroup.RationalHeightRankCongruence

/-! # Diagonally equivariant equations of actual formal kernels -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.RationalHeightRankCongruence

open CategoryTheory FiniteKernelComposition RationalHeightJets RationalHeightLinearization
open MvPolynomial

attribute [local instance] coefficientAlgebra coefficientScalarTower

set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

variable {k : Type v} [Field k] {σ : Type} [Finite σ] {p : ℕ} [ExpChar k p]
variable {O : Type u} [CommRing O] [Algebra O k]
variable {M N : ModuleLaw O k σ}
variable (c : σ → k)

/-- The same diagonal action on a rectangular characteristic-power jet. -/
def diagonalScaleJet (e : ℕ) : truncAlg k σ (p ^ e) →ₐ[k] truncAlg k σ (p ^ e) :=
  substitute e (fun i => c i • truncProj k σ (p ^ e) (X i)) fun i =>
    Submodule.smul_of_tower_mem _ _ (truncProj_X_mem_augmentation _ i)

@[simp]
theorem diagonalScaleJet_X (e : ℕ) (i : σ) :
    diagonalScaleJet c e (truncProj k σ (p ^ e) (X i)) = c i • truncProj k σ (p ^ e) (X i) :=
  substitute_X _ _ _ _

private theorem diagonalScaleJet_truncProj (e : ℕ) (F : MvPolynomial σ k) :
    diagonalScaleJet c e (truncProj k σ (p ^ e) F) =
      truncProj k σ (p ^ e) (diagonalScale c F) :=
  DFunLike.congr_fun (show (diagonalScaleJet c e).comp (truncProj k σ (p ^ e)) =
    (truncProj k σ (p ^ e)).comp (diagonalScale c) from
      MvPolynomial.algHom_ext fun i => by simp) F

/-- An actual diagonal formal endomorphism induces the same scaling on the jets. -/
theorem mapJet_eq_diagonalScaleJet (e : ℕ) (a : Hom M M)
    (ha : a.toHom.toCoordinateMap = CoordinateMap.ofLinearMap (CoordinateMap.diagonalLinear c)) :
    mapJet (p := p) e a = diagonalScaleJet c e := by
  apply truncAlg_hom_ext
  intro i
  rw [mapJet_X, diagonalScaleJet_X]
  let A := truncAlg k σ (p ^ e)
  let x := truncPoint M (p ^ e)
  have hs : a.toHom.toCoordinateMap.series i = c i • MvPowerSeries.X i := by
    have h := CoordinateMap.diagonal_comp_series c (CoordinateMap.id : CoordinateMap k σ σ) i
    rw [CoordinateMap.comp_id] at h
    exact (congrArg (fun F : CoordinateMap k σ σ => F.series i) ha).trans h
  have hmap : (a.toHom.toCoordinateMap.map (algebraMap k A)).series i =
      algebraMap k A (c i) • MvPowerSeries.X i := by
    change MvPowerSeries.map (algebraMap k A) (a.toHom.toCoordinateMap.series i) = _
    rw [hs, MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.map_C, MvPowerSeries.map_X,
      MvPowerSeries.smul_eq_C_mul]
  change MvPowerSeries.constantCoeff
    ((SeriesPoint.eval (a.toHom.toCoordinateMap.map (algebraMap k A)) x).val i) = _
  rw [SeriesPoint.eval_val, hmap, MvPowerSeries.smul_eq_C_mul,
    ← MvPowerSeries.substAlgHom_apply x.property, map_mul,
    MvPowerSeries.substAlgHom_X, MvPowerSeries.substAlgHom_apply, MvPowerSeries.subst_C,
    map_mul, MvPowerSeries.constantCoeff_C]
  rw [Algebra.smul_def]
  exact congrArg (algebraMap k A (c i) * ·) (coord_truncPoint (M := M) (p ^ e) i)

/-- Every actual intertwining map between the same diagonal actions has polynomial
kernel equations with the specified weights at all smaller characteristic-power widths. -/
theorem exists_diagonal_kernelEquations {m : ℕ}
    (hm : (m : k) ≠ 0) (hc : ∀ i, c i ^ m = 1) (hc₀ : ∀ i, c i ≠ 0)
    (e : ℕ) (f : Hom M N) (a : Hom M M) (b : Hom N N)
    (ha : a.toHom.toCoordinateMap = CoordinateMap.ofLinearMap (CoordinateMap.diagonalLinear c))
    (hb : b.toHom.toCoordinateMap = CoordinateMap.ofLinearMap (CoordinateMap.diagonalLinear c))
    (hf : f.comp a = b.comp f) :
    ∃ F : σ → MvPolynomial σ k, (∀ i, diagonalScale c (F i) = c i • F i) ∧
      ∀ j : ℕ, p ^ j ≤ p ^ e →
        Module.finrank k (truncAlg k σ (p ^ j) ⧸
          Ideal.span (Set.range fun i => truncProj k σ (p ^ j) (F i))) =
          Module.finrank k (kerAlg f (p ^ j)) := by
  let y := fun i => mapJet e f (truncProj k σ (p ^ e) (X i))
  have hy (i : σ) : diagonalScaleJet c e (y i) = c i • y i := by
    rw [← mapJet_eq_diagonalScaleJet c e a ha]
    have h := congrArg (mapJet (p := p) e) hf
    rw [mapJet_comp, mapJet_comp, mapJet_eq_diagonalScaleJet c e b hb] at h
    have h' := DFunLike.congr_fun h (truncProj k σ (p ^ e) (X i))
    rw [AlgHom.comp_apply, AlgHom.comp_apply, diagonalScaleJet_X, map_smul] at h'
    exact h'
  choose Q hQ using fun i => truncProj_surjective (p ^ e) (y i)
  let F := fun i => weightedAverage m (c i) (fun j => diagonalScale (fun v => c v ^ j) (Q i))
  have shift (j : ℕ) (i : σ) :
      diagonalScale c (diagonalScale (fun v => c v ^ j) (Q i)) =
        diagonalScale (fun v => c v ^ (j + 1)) (Q i) := by
    simpa only [AlgHom.comp_apply, pow_succ] using
      DFunLike.congr_fun (diagonalScale_comp c (fun v => c v ^ j)) (Q i)
  have hF (i : σ) : diagonalScale c (F i) = c i • F i := by
    change (diagonalScale c).toLinearMap (weightedAverage m (c i) (fun j =>
      diagonalScale (fun v => c v ^ j) (Q i))) = _
    rw [map_weightedAverage]
    have hs : (diagonalScale c).toLinearMap ∘ (fun j => diagonalScale (fun v => c v ^ j) (Q i)) =
        (fun j => diagonalScale (fun v => c v ^ (j + 1)) (Q i)) := funext fun j => shift j i
    rw [hs]
    refine weightedAverage_shift (fun h => hm (by simp [h])) (hc i)
      (fun j => diagonalScale (fun v => c v ^ j) (Q i)) ?_
    simp only [hc, pow_zero]
  have hLift (i : σ) : truncProj k σ (p ^ e) (F i) = y i := by
    have he (j : ℕ) : truncProj k σ (p ^ e) (diagonalScale (fun v => c v ^ j) (Q i)) = c i ^ j • y i := by
      induction j with
      | zero => simp only [pow_zero, diagonalScale_const, scale_one, AlgHom.id_apply, one_smul, hQ]
      | succ j hj =>
        rw [← shift j i, ← diagonalScaleJet_truncProj, hj, map_smul, hy, smul_smul, pow_succ]
    change (truncProj k σ (p ^ e)).toLinearMap
      (weightedAverage m (c i) (fun j => diagonalScale (fun v => c v ^ j) (Q i))) = _
    rw [map_weightedAverage]
    rw [show (truncProj k σ (p ^ e)).toLinearMap ∘ (fun j => diagonalScale (fun v => c v ^ j) (Q i)) =
      (fun j => c i ^ j • y i) from funext he]
    exact weightedAverage_smul_pows hm (hc₀ i) _
  refine ⟨F, hF, fun j hj => ?_⟩
  have h (i : σ) : truncProj k σ (p ^ j) (F i) = mapJet j f (truncProj k σ (p ^ j) (X i)) := by
    have he := DFunLike.congr_fun (restrictJet_mapJet (p := p) hj f)
      (truncProj k σ (p ^ e) (X i))
    simp only [AlgHom.comp_apply, restrictJet_truncProj] at he
    rw [← restrictJet_truncProj hj (F i), hLift]
    exact he
  rw [show (fun i => truncProj k σ (p ^ j) (F i)) =
    (fun i => mapJet j f (truncProj k σ (p ^ j) (X i))) from funext h]
  have hI : Ideal.span (Set.range fun i => mapJet j f (truncProj k σ (p ^ j) (X i))) =
      kerIdeal M f (p ^ j) := by
    rw [← map_augmentation_eq_kerIdeal (p := p) j f, augmentation_eq_span, Ideal.map_span, ← Set.range_comp]
    rfl
  exact congrArg (fun I : Ideal (truncAlg k σ (p ^ j)) => Module.finrank k ((truncAlg k σ (p ^ j)) ⧸ I)) hI


/-- A represented actual kernel has rank congruent to one when the two formal
coordinate actions have the same diagonal weights of order `m`. -/
theorem finrank_modEq_of_diagonal_formal_kernel {m : ℕ} (hm : (m : k) ≠ 0)
    (horder : ∀ i, orderOf (c i) = m) (hc : ∀ i, c i ≠ 0) (hp : 2 ≤ p)
    (f : Hom M N) (a : Hom M M) (b : Hom N N)
    (ha : a.toHom.toCoordinateMap = CoordinateMap.ofLinearMap (CoordinateMap.diagonalLinear c))
    (hb : b.toHom.toCoordinateMap = CoordinateMap.ofLinearMap (CoordinateMap.diagonalLinear c))
    (hf : f.comp a = b.comp f) (P : f.FiniteKernelModel) :
    Module.finrank k P.coordinateAlgebra ≡ 1 [MOD m] := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  have hm₀ : m ≠ 0 := fun h => hm (by simp [h])
  have hc₁ (i : σ) : c i ^ m = 1 := by rw [← horder i, pow_orderOf_eq_one]
  obtain ⟨b₀, hb₀⟩ := exists_kernel_bound P.represents
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (max 1 (b₀ + 1)) (show 1 < p from hp)
  have hj₁ : 1 < p ^ j := (le_max_left _ _).trans_lt hj
  have hwidth : 2 * p ^ j ≤ p ^ (j + 1) := by
    rw [pow_succ, mul_comm (p ^ j) p]
    exact Nat.mul_le_mul_right _ hp
  have hjle : p ^ j ≤ p ^ (j + 1) := by omega
  obtain ⟨F, hF, hFr⟩ := exists_diagonal_kernelEquations (p := p) c hm hc₁ hc (j + 1) f a b ha hb hf
  have hr (l : ℕ) (hl : b₀ + 1 ≤ p ^ l) (hl' : p ^ l ≤ p ^ (j + 1)) :
      Module.finrank k (truncAlg k σ (p ^ l) ⧸
        Ideal.span (Set.range fun i => truncProj k σ (p ^ l) (F i))) =
        Module.finrank k P.coordinateAlgebra := by
    rw [hFr l hl']
    exact finrank_kerAlg_eq P fun A x hx i => pow_eq_zero_of_le hl (hb₀ A x hx i)
  let v := max (p ^ (j + 1)) (Finset.univ.sup fun i : σ => (F i).totalDegree)
  let l := v * m + 1
  have hv : v ≤ v * m := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hm₀)
  have hl : p ^ (j + 1) ≤ l := (le_max_left _ _).trans (hv.trans (Nat.le_succ _))
  have hdeg (i : σ) : (F i).totalDegree < l :=
    ((Finset.le_sup (f := fun i : σ => (F i).totalDegree) (Finset.mem_univ i)).trans
      ((le_max_right _ _).trans hv)).trans_lt (Nat.lt_succ_self _)
  have hpow (i : σ) : c i ^ l = c i := by rw [show l = v * m + 1 from rfl, pow_add, mul_comm v m,
    pow_mul, hc₁, one_pow, pow_one, one_mul]
  have hL : l ≡ 1 [MOD m] := by
    change v * m + 1 ≡ 1 [MOD m]
    rw [Nat.ModEq, mul_comm v m, Nat.mul_add_mod]
  have hj₀ : b₀ + 1 ≤ p ^ j := (le_max_right _ _).trans hj.le
  have hh := finrank_modEq_of_diagonal_equations F c hc horder hF (zero_lt_one.trans hj₁)
    hwidth hl hdeg hpow (hr j hj₀ hjle) (hr (j + 1) (hj₀.trans hjle) le_rfl)
  exact hh.symm.trans (by simpa only [one_pow] using hL.pow (Nat.card σ))

end Langlands.FormalGroup.ModuleLaw.RationalHeightRankCongruence
