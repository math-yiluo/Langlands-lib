import Langlands.BaseChange.RegularOrbitParameters
import Langlands.BaseChange.OrbitalIntegral
import Langlands.Group.GL.LocalFieldTopology
import Langlands.HarmonicAnalysis.Distribution.TransposeInvariantProof
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.RingTheory.Valuation.Integral

/-! Openness of regular elliptic elements in the native topology of a local field. -/

noncomputable section

namespace Langlands.BaseChange

open _root_.Polynomial Langlands.JacquetLanglands
open Langlands.HarmonicAnalysis.Distribution (charpolyCoeffs continuous_charpolyCoeffs)
open scoped BigOperators

universe u

section Polynomial

variable {K : Type u} [Field K]

private theorem irreducible_scaleRoots_of_ne_zero {p : K[X]} (hp : p.Monic)
    (hirr : Irreducible p) {a : K} (ha : a ≠ 0) : Irreducible (p.scaleRoots a) := by
  have hmonic : (p.scaleRoots a).Monic := (monic_scaleRoots_iff a).mpr hp
  apply hmonic.irreducible_iff_natDegree.mpr
  constructor
  · intro he
    have hd := congrArg natDegree he
    rw [natDegree_scaleRoots, natDegree_one] at hd
    exact hirr.natDegree_pos.ne' hd
  · intro f g hf hg he
    have hmul := congrArg (fun q : K[X] => q.scaleRoots a⁻¹) he
    change (f * g).scaleRoots a⁻¹ = (p.scaleRoots a).scaleRoots a⁻¹ at hmul
    rw [mul_scaleRoots_of_noZeroDivisors, ← scaleRoots_mul, mul_inv_cancel₀ ha, scaleRoots_one] at hmul
    have hmF : (f.scaleRoots a⁻¹).Monic := (monic_scaleRoots_iff _).mpr hf
    have hmG : (g.scaleRoots a⁻¹).Monic := (monic_scaleRoots_iff _).mpr hg
    simpa only [natDegree_scaleRoots] using
      (hp.irreducible_iff_natDegree.mp hirr).2 _ _ hmF hmG hmul

private theorem irreducible_scaleRoots_iff {p : K[X]} (hp : p.Monic) {a : K} (ha : a ≠ 0) :
    Irreducible (p.scaleRoots a) ↔ Irreducible p := by
  constructor
  · intro hirr
    have h := irreducible_scaleRoots_of_ne_zero ((monic_scaleRoots_iff a).mpr hp) hirr (inv_ne_zero ha)
    rwa [← scaleRoots_mul, mul_inv_cancel₀ ha, scaleRoots_one] at h
  · intro hirr
    exact irreducible_scaleRoots_of_ne_zero hp hirr ha

end Polynomial

section Coefficients

variable {R : Type u} [CommRing R]

private theorem monic_monicPolynomialFromCoefficients {k : ℕ} (a : Fin k → R) :
    (polynomialOfCoefficients a).Monic := by
  exact monic_X_pow_add (degree_sum_fin_lt a)

private theorem natDegree_monicPolynomialFromCoefficients [Nontrivial R] {k : ℕ} (a : Fin k → R) :
    (polynomialOfCoefficients a).natDegree = k := by
  have hlt := degree_sum_fin_lt a
  unfold polynomialOfCoefficients
  rw [natDegree_add_eq_left_of_degree_lt (by simpa only [degree_X_pow] using hlt), natDegree_X_pow]

private theorem monicPolynomialFromCoefficients_eq {k : ℕ} (p : R[X]) (hp : p.Monic)
    (hd : p.natDegree = k) : polynomialOfCoefficients (fun i : Fin k => p.coeff i) = p := by
  subst k
  calc
    _ = X ^ p.natDegree + ∑ i ∈ Finset.range p.natDegree, C (p.coeff i) * X ^ i :=
      congrArg (fun q : R[X] => X ^ p.natDegree + q)
        (Fin.sum_univ_eq_sum_range (fun i : ℕ => C (p.coeff i) * X ^ i) p.natDegree)
    _ = p := hp.as_sum.symm

private theorem map_monicPolynomialFromCoefficients {S : Type*} [CommRing S]
    (f : R →+* S) {k : ℕ} (a : Fin k → R) :
    (polynomialOfCoefficients a).map f = polynomialOfCoefficients (fun i => f (a i)) := by
  simp only [polynomialOfCoefficients, Polynomial.map_add, Polynomial.map_sum,
    Polynomial.map_mul, Polynomial.map_pow, map_X, map_C]

private theorem eq_of_monic_of_lower_coefficients {p q : R[X]} (hp : p.Monic) (hq : q.Monic)
    {n : ℕ} (hnp : p.natDegree = n) (hnq : q.natDegree = n)
    (h : ∀ i : Fin n, p.coeff i = q.coeff i) : p = q := by
  rw [hp.as_sum, hq.as_sum, hnp, hnq]
  congr 1
  refine Finset.sum_congr rfl (fun i hi => ?_)
  exact congrArg (fun c => C c * X ^ i) (h ⟨i, Finset.mem_range.mp hi⟩)

variable [TopologicalSpace R] [IsTopologicalRing R]

private theorem continuous_coeff_monicPolynomialFromCoefficients {X : Type*} [TopologicalSpace X]
    {k : ℕ} {a : X → Fin k → R} (ha : Continuous a) (j : ℕ) :
    Continuous (fun x => (polynomialOfCoefficients (a x)).coeff j) := by
  simp only [polynomialOfCoefficients, coeff_add, finsetSum_coeff, coeff_C_mul_X_pow]
  apply continuous_const.add
  apply continuous_finsetSum _
  intro i _
  split
  · exact (continuous_apply i).comp ha
  · exact continuous_const

end Coefficients

section LocalField

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local notation "𝒪F" => Valuation.integer (ValuativeRel.valuation F)

private abbrev ProperFactorDegree (n : ℕ) := {k : Fin n // 0 < (k : ℕ)}

private def factorCoefficientMap {n : ℕ} (k : ProperFactorDegree n)
    (a : (Fin k.val.val → 𝒪F) × (Fin (n - k.val.val) → 𝒪F)) : Fin n → F :=
  fun i => ((polynomialOfCoefficients a.1 * polynomialOfCoefficients a.2).map
    (algebraMap 𝒪F F)).coeff i

private def reducibleIntegralCoefficients (n : ℕ) : Set (Fin n → F) :=
  ⋃ k : ProperFactorDegree n, Set.range (factorCoefficientMap F k)

private theorem isClosed_reducibleIntegralCoefficients (n : ℕ) :
    IsClosed (reducibleIntegralCoefficients F n) := by
  let : T2Space F := LocalFieldTopology.t2Space F
  apply IsCompact.isClosed
  unfold reducibleIntegralCoefficients
  apply isCompact_iUnion
  intro k
  apply isCompact_range
  apply continuous_pi
  intro j
  simp only [factorCoefficientMap, Polynomial.map_mul, map_monicPolynomialFromCoefficients, coeff_mul]
  apply continuous_finsetSum _
  intro i _
  apply Continuous.mul
  · apply continuous_coeff_monicPolynomialFromCoefficients
    exact continuous_pi fun t => continuous_subtype_val.comp ((continuous_apply t).comp continuous_fst)
  · apply continuous_coeff_monicPolynomialFromCoefficients
    exact continuous_pi fun t => continuous_subtype_val.comp ((continuous_apply t).comp continuous_snd)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem irreducible_iff_coefficients_notMem {n : ℕ} (hn : 0 < n) (p : F[X])
    (hp : p.Monic) (hdeg : p.natDegree = n) (hint : ∀ i : ℕ, p.coeff i ∈ 𝒪F) :
    Irreducible p ↔ (fun i : Fin n => p.coeff i) ∉ reducibleIntegralCoefficients F n := by
  constructor
  · intro hi hm
    obtain ⟨k, ⟨a, ha⟩⟩ := Set.mem_iUnion.mp hm
    let f : F[X] := (polynomialOfCoefficients a.1).map (algebraMap 𝒪F F)
    let g : F[X] := (polynomialOfCoefficients a.2).map (algebraMap 𝒪F F)
    have hf : f.Monic := (monic_monicPolynomialFromCoefficients a.1).map _
    have hg : g.Monic := (monic_monicPolynomialFromCoefficients a.2).map _
    have hdf : f.natDegree = k.val.val := by
      change ((polynomialOfCoefficients a.1).map (algebraMap 𝒪F F)).natDegree = _
      rw [(monic_monicPolynomialFromCoefficients a.1).natDegree_map,
        natDegree_monicPolynomialFromCoefficients]
    have hdg : g.natDegree = n - k.val.val := by
      change ((polynomialOfCoefficients a.2).map (algebraMap 𝒪F F)).natDegree = _
      rw [(monic_monicPolynomialFromCoefficients a.2).natDegree_map,
        natDegree_monicPolynomialFromCoefficients]
    have hdm : (f * g).natDegree = n := by
      rw [hf.natDegree_mul hg, hdf, hdg]
      exact Nat.add_sub_of_le k.val.isLt.le
    have he : f * g = p := by
      apply eq_of_monic_of_lower_coefficients (hf.mul hg) hp hdm hdeg
      intro i
      have hei := congrFun ha i
      simpa only [factorCoefficientMap, Polynomial.map_mul, f, g] using hei
    have hpos := (hp.irreducible_iff_natDegree.mp hi).2 f g hf hg he
    have hk₁ := k.property
    have hk₂ := k.val.isLt
    rw [hdf, hdg] at hpos
    omega
  · intro hnmem
    by_contra hi
    have hl : p ∈ lifts (algebraMap 𝒪F F) :=
      (lifts_iff_coeff_lifts p).mpr fun i => ⟨⟨p.coeff i, hint i⟩, rfl⟩
    obtain ⟨p₀, he, hd, hp₀⟩ := lifts_and_natDegree_eq_and_monic hl hp
    rw [hdeg] at hd
    have hi₀ : ¬ Irreducible p₀ := by
      intro hpirr
      apply hi
      rw [← he]
      exact (hp₀.irreducible_iff_irreducible_map_fraction_map (K := F)).mp hpirr
    have h1 : p₀ ≠ 1 := by
      intro h
      rw [h, natDegree_one] at hd
      omega
    rw [hp₀.irreducible_iff_natDegree, and_iff_right h1] at hi₀
    push Not at hi₀
    obtain ⟨f, g, hf, hg, hmul, hdf, hdg⟩ := hi₀
    have hdegMul : f.natDegree + g.natDegree = n := by
      rw [← hf.natDegree_mul hg, hmul, hd]
    let k : ProperFactorDegree n := ⟨⟨f.natDegree, by omega⟩, Nat.pos_of_ne_zero hdf⟩
    have hdk : g.natDegree = n - k.val.val := by dsimp [k]; omega
    apply hnmem
    refine Set.mem_iUnion.mpr ⟨k, ?_⟩
    refine ⟨(fun i => f.coeff i, fun i => g.coeff i), ?_⟩
    funext i
    change ((polynomialOfCoefficients (fun j : Fin k.val.val => f.coeff j) *
      polynomialOfCoefficients (fun j : Fin (n - k.val.val) => g.coeff j)).map
        (algebraMap 𝒪F F)).coeff i = _
    rw [monicPolynomialFromCoefficients_eq f hf rfl, monicPolynomialFromCoefficients_eq g hg hdk,
      hmul, he]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem exists_clearIntegralDenominators {n : ℕ} (b : Fin n → F) :
    ∃ a : F, a ≠ 0 ∧ a ∈ 𝒪F ∧ ∀ i, a * b i ∈ 𝒪F := by
  classical
  have hSingle (x : F) : ∃ a : F, a ≠ 0 ∧ a ∈ 𝒪F ∧ a * x ∈ 𝒪F := by
    by_cases hx : x ∈ 𝒪F
    · exact ⟨1, one_ne_zero, (𝒪F).one_mem, by simpa only [one_mul] using hx⟩
    · have hx₀ : x ≠ 0 := fun h => hx (h.symm ▸ (𝒪F).zero_mem)
      have hVal : 1 < ValuativeRel.valuation F x := lt_of_not_ge hx
      refine ⟨x⁻¹, inv_ne_zero hx₀, ?_, ?_⟩
      · change ValuativeRel.valuation F x⁻¹ ≤ 1
        rw [map_inv₀]
        exact (inv_le_one₀ (zero_lt_one.trans hVal)).mpr hVal.le
      · rw [inv_mul_cancel₀ hx₀]
        exact (𝒪F).one_mem
  choose a hNe hA hB using fun i => hSingle (b i)
  refine ⟨∏ i, a i, Finset.prod_ne_zero_iff.mpr (fun i _ => hNe i),
    (𝒪F).prod_mem (fun i _ => hA i), ?_⟩
  intro i
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_right_comm]
  exact (𝒪F).mul_mem (hB i) ((𝒪F).prod_mem (fun j _ => hA j))

private theorem isOpen_irreducible_charpoly (n : ℕ) :
    IsOpen {g : GeneralLinear n F | Irreducible g.val.charpoly} := by
  rw [isOpen_iff_mem_nhds]
  intro g₀ hg₀
  have hdegree (g : GeneralLinear n F) : g.val.charpoly.natDegree = n := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hpos : 0 < n := hdegree g₀ ▸ (show Irreducible g₀.val.charpoly from hg₀).natDegree_pos
  obtain ⟨a, ha, haInt, hclear⟩ :=
    exists_clearIntegralDenominators F (charpolyCoeffs n g₀)
  let p (g : GeneralLinear n F) := g.val.charpoly.scaleRoots a
  let φ (g : GeneralLinear n F) (i : Fin n) := (p g).coeff i
  have hp (g : GeneralLinear n F) : (p g).Monic :=
    (monic_scaleRoots_iff a).mpr g.val.charpoly_monic
  have hpdeg (g : GeneralLinear n F) : (p g).natDegree = n := by
    change (g.val.charpoly.scaleRoots a).natDegree = n
    rw [natDegree_scaleRoots, hdegree]
  have hφ : Continuous φ := by
    apply continuous_pi
    intro i
    simp only [φ, p, coeff_scaleRoots, hdegree]
    exact ((continuous_apply i).comp (continuous_charpolyCoeffs n)).mul continuous_const
  let box : Set (Fin n → F) := Set.univ.pi fun _ => (𝒪F : Set F)
  have hBox : IsOpen box :=
    isOpen_set_pi Set.finite_univ (fun _ _ => Valuation.isOpen_integer (v := ValuativeRel.valuation F))
  have hMem₀ : φ g₀ ∈ box := by
    intro i _
    change (g₀.val.charpoly.scaleRoots a).coeff i ∈ 𝒪F
    have hExp : n - (i : ℕ) = n - (i : ℕ) - 1 + 1 := by omega
    rw [coeff_scaleRoots, hdegree, hExp, pow_succ]
    have hInt := (𝒪F).mul_mem (hclear i) ((𝒪F).pow_mem haInt (n - (i : ℕ) - 1))
    convert hInt using 1
    simp only [charpolyCoeffs]
    ac_rfl
  have hAll (g : GeneralLinear n F) (hg : φ g ∈ box) (j : ℕ) : (p g).coeff j ∈ 𝒪F := by
    by_cases hlt : j < n
    · exact hg ⟨j, hlt⟩ (Set.mem_univ _)
    · by_cases he : j = n
      · rw [he, ← hpdeg g, (hp g).coeff_natDegree]
        exact (𝒪F).one_mem
      · rw [coeff_eq_zero_of_natDegree_lt (show (p g).natDegree < j by rw [hpdeg]; omega)]
        exact (𝒪F).zero_mem
  have hg₀' : Irreducible (p g₀) := irreducible_scaleRoots_of_ne_zero g₀.val.charpoly_monic hg₀ ha
  have hAvoid₀ : φ g₀ ∉ reducibleIntegralCoefficients F n :=
    (irreducible_iff_coefficients_notMem F hpos _ (hp g₀) (hpdeg g₀) (hAll g₀ hMem₀)).mp hg₀'
  let W : Set (GeneralLinear n F) := φ ⁻¹' (box ∩ (reducibleIntegralCoefficients F n)ᶜ)
  have hW : IsOpen W := (hBox.inter (isClosed_reducibleIntegralCoefficients F n).isOpen_compl).preimage hφ
  refine Filter.mem_of_superset (hW.mem_nhds ⟨hMem₀, hAvoid₀⟩) (fun g hg => ?_)
  have hInt : φ g ∈ box := hg.1
  have hAvoid : φ g ∉ reducibleIntegralCoefficients F n := hg.2
  have h := (irreducible_iff_coefficients_notMem F hpos _ (hp g) (hpdeg g) (hAll g hInt)).mpr hAvoid
  exact (irreducible_scaleRoots_iff g.val.charpoly_monic ha).mp h

/-- Over a characteristic-zero nonarchimedean local field, the regular elliptic
elements form an open subset in the actual general linear group topology. -/
theorem isOpen_regularElliptic [CharZero F] (n : ℕ) :
    IsOpen {g : GeneralLinear n F | IsRegularElliptic g} := by
  convert isOpen_irreducible_charpoly F n using 1
  ext g
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨PerfectField.separable_of_irreducible h, h⟩

end LocalField

/-- Openness of the regular elliptic locus used to choose a split auxiliary
test function in cyclic base change. -/
def RegularEllipticOpenStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] (n : ℕ),
    IsOpen {g : GeneralLinear n F | IsRegularElliptic g}

theorem regularEllipticOpen : RegularEllipticOpenStatement.{u} :=
  fun F _ _ _ _ _ n => isOpen_regularElliptic F n

end Langlands.BaseChange
