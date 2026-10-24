import Langlands.Representation.Unramified.StandardMonomialTop
import Langlands.Representation.Unramified.SphericalHeckeGenerationStatement
import Langlands.Representation.Hecke.DoubleCosetSandwich

/-! # Generation of the spherical Hecke algebra by the standard elements up to central powers -/

noncomputable section

namespace Langlands.Unramified

open Correspondence GeneralLinear.Iwasawa GeneralLinear.Cartan

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance generationProofFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance generationProofFieldValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance generationProofFieldLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance generationProofGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) := F.canonicalGeneralLinearTopology n
local instance generationProofGeneralLinearTopologicalGroup (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n F.Carrier) := F.canonicalGeneralLinearTopologicalGroup n
local instance generationProofGeneralLinearT2 (n : ℕ) : T2Space (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearT2Space n
local instance generationProofGeneralLinearMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear n F.Carrier) := borel _
local instance generationProofGeneralLinearBorel (n : ℕ) :
    BorelSpace (GeneralLinear n F.Carrier) := ⟨rfl⟩

namespace SphericalGeneration

/-! ### Double cosets and the Cartan decomposition -/

/-- The spherical double coset `K g K`. -/
abbrev cosetSet {r : ℕ} (g : GeneralLinear (r + 1) F.Carrier) :
    Set (GeneralLinear (r + 1) F.Carrier) :=
  Hecke.TestFunction.doubleCosetSet (sphericalOpenSubgroup F r) g

/-- The double-coset element of `K g K` in the spherical corner. -/
abbrev cosetElement {r : ℕ} (g : GeneralLinear (r + 1) F.Carrier) : SphericalHeckeAlgebra F r :=
  Hecke.HeckeAlgebra.Corner.doubleCoset (sphericalOpenSubgroup F r)
    (sphericalOpenSubgroup_isCompact F r) (sphericalHaar F r) g

theorem cosetElement_apply {r : ℕ} (g x : GeneralLinear (r + 1) F.Carrier) :
    cosetElement F g x = (cosetSet F g).indicator (fun _ => (1 : ℂ)) x :=
  Hecke.HeckeAlgebra.Corner.doubleCoset_apply_of_mass_one _ _ _ (sphericalHaar_real_self F r) _ _

/-- Every element lies in the double coset of an antitone power of the uniformizer. -/
theorem exists_antitone_mem {r : ℕ} (g : GeneralLinear (r + 1) F.Carrier) :
    ∃ lam : Fin (r + 1) → ℤ, Antitone lam ∧ g ∈ cosetSet F (standardTorus F lam) := by
  obtain ⟨lam, hlam, k₁, hk₁, k₂, hk₂, hg⟩ :=
    exists_cartan (standardUniformizer_isUniformizing F) (r + 1) g
  exact ⟨lam, hlam, (Hecke.TestFunction.mem_doubleCosetSet _ _ _).2 ⟨k₁, hk₁, k₂, hk₂, hg⟩⟩

/-- Distinct antitone exponents give distinct double cosets. -/
theorem eq_of_torus_mem {r : ℕ} {ν ν' : Fin (r + 1) → ℤ} (hν : Antitone ν) (hν' : Antitone ν')
    (h : standardTorus F ν ∈ cosetSet F (standardTorus F ν')) : ν = ν' := by
  obtain ⟨a, ha, b, hb, hab⟩ := (Hecke.TestFunction.mem_doubleCosetSet _ _ _).1 h
  refine exponent_unique (standardUniformizer_isUniformizing F) hν hν' (one_mem _) (one_mem _)
    ha hb ?_
  rw [one_mul, mul_one]
  exact hab

/-! ### Expansion along double cosets -/

/-- Evaluation at a point, as a linear functional on the spherical corner. -/
def evalAt {r : ℕ} (x : GeneralLinear (r + 1) F.Carrier) : SphericalHeckeAlgebra F r →ₗ[ℂ] ℂ where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A spherical element supported on the double cosets of a finite set of antitone
exponents is the combination of their double-coset elements with its values as
coefficients. -/
theorem eq_sum_of_support {r : ℕ} (f : SphericalHeckeAlgebra F r)
    (S : Finset (Fin (r + 1) → ℤ)) (hS : ∀ ν ∈ S, Antitone ν)
    (hf : ∀ x, f x ≠ 0 → ∃ ν ∈ S, x ∈ cosetSet F (standardTorus F ν)) :
    f = ∑ ν ∈ S, f (standardTorus F ν) • torusHeckeElement F ν := by
  classical
  apply Hecke.HeckeAlgebra.Corner.ext'
  intro x
  change f x = evalAt F x (∑ ν ∈ S, f (standardTorus F ν) • torusHeckeElement F ν)
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  change f x = ∑ ν ∈ S, f (standardTorus F ν) * cosetElement F (standardTorus F ν) x
  simp only [cosetElement_apply]
  by_cases hx : ∃ μ ∈ S, x ∈ cosetSet F (standardTorus F μ)
  · obtain ⟨μ, hμS, hxμ⟩ := hx
    rw [Finset.sum_eq_single μ, Set.indicator_of_mem hxμ, mul_one,
      Hecke.HeckeAlgebra.Corner.apply_eq_of_mem_doubleCosetSet _ _ _ f hxμ]
    · intro ν hνS hνμ
      rw [Set.indicator_of_notMem, mul_zero]
      intro hxν
      apply hνμ
      have hset : cosetSet F (standardTorus F μ) = cosetSet F (standardTorus F ν) :=
        (Hecke.TestFunction.doubleCosetSet_eq_of_mem _ hxμ).symm.trans
          (Hecke.TestFunction.doubleCosetSet_eq_of_mem _ hxν)
      have hmem : standardTorus F μ ∈ cosetSet F (standardTorus F ν) :=
        hset ▸ Hecke.TestFunction.mem_doubleCosetSet_self _ _
      exact (eq_of_torus_mem F (hS μ hμS) (hS ν hνS) hmem).symm
    · intro hμ
      exact absurd hμS hμ
  · push Not at hx
    rw [Finset.sum_eq_zero]
    · by_contra hfx
      obtain ⟨μ, hμS, hxμ⟩ := hf x hfx
      exact hx μ hμS hxμ
    · intro ν hνS
      rw [Set.indicator_of_notMem (hx ν hνS), mul_zero]

/-! ### Exponents of standard monomials -/

/-- The successive gaps of an exponent tuple, the last gap being the last entry; the
zeroth entry is unused. -/
def gapExponent {r : ℕ} (lam : Fin (r + 1) → ℤ) : Fin (r + 2) → ℕ :=
  Fin.cases 0 fun i => (lam i - if h : i.val + 1 < r + 1 then lam ⟨i.val + 1, h⟩ else 0).toNat

theorem gapExponent_succ {r : ℕ} (lam : Fin (r + 1) → ℤ) (i : Fin (r + 1)) :
    gapExponent lam i.succ =
      (lam i - if h : i.val + 1 < r + 1 then lam ⟨i.val + 1, h⟩ else 0).toNat :=
  rfl

theorem monomialExponent_sub {r : ℕ} (a : Fin (r + 2) → ℕ) (j : Fin (r + 1))
    (hj : j.val + 1 < r + 1) :
    monomialExponent a j - monomialExponent a ⟨j.val + 1, hj⟩ = (a j.succ : ℤ) := by
  simp only [monomialExponent, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single j.succ]
  · simp
  · intro i _ hi
    have : i.val ≠ j.val + 1 := fun h => hi (Fin.ext (by simp [h]))
    split_ifs <;> omega
  · simp

theorem monomialExponent_last {r : ℕ} (a : Fin (r + 2) → ℕ) :
    monomialExponent a (Fin.last r) = (a (Fin.last (r + 1)) : ℤ) := by
  simp only [monomialExponent]
  rw [Finset.sum_eq_single (Fin.last (r + 1))]
  · simp
  · intro i _ hi
    have : i.val ≠ r + 1 := fun h => hi (Fin.ext h)
    have := i.isLt
    simp only [Fin.val_last]
    split_ifs <;> omega
  · simp

/-- An antitone exponent with nonnegative last entry is the exponent of a monomial. -/
theorem monomialExponent_gapExponent {r : ℕ} {lam : Fin (r + 1) → ℤ} (hlam : Antitone lam)
    (h0 : 0 ≤ lam (Fin.last r)) : monomialExponent (gapExponent lam) = lam := by
  have key : ∀ t : ℕ, ∀ j : Fin (r + 1), j.val + t = r →
      monomialExponent (gapExponent lam) j = lam j := by
    intro t
    induction t with
    | zero =>
      intro j hj
      have hjl : j = Fin.last r := Fin.ext (by simp only [Fin.val_last]; omega)
      subst hjl
      rw [monomialExponent_last, ← Fin.succ_last, gapExponent_succ]
      have hnot : ¬ ((Fin.last r).val + 1 < r + 1) := by simp
      simp only [hnot, ↓reduceDIte, sub_zero, Int.toNat_of_nonneg h0]
    | succ t ih =>
      intro j hj
      have hj1 : j.val + 1 < r + 1 := by omega
      have h1 := ih ⟨j.val + 1, hj1⟩ (by simp only; omega)
      have h2 := monomialExponent_sub (gapExponent lam) j hj1
      have hle : lam ⟨j.val + 1, hj1⟩ ≤ lam j := hlam (Fin.mk_le_mk.2 (by omega))
      rw [gapExponent_succ] at h2
      simp only [hj1, ↓reduceDIte, Int.toNat_of_nonneg (sub_nonneg.2 hle)] at h2
      linarith
  funext j
  exact key (r - j.val) j (by omega)

/-- Standard monomials lie in the subalgebra generated by the standard elements. -/
theorem standardMonomial_mem {r : ℕ} (a : Fin (r + 2) → ℕ) :
    standardMonomial F a ∈ Algebra.adjoin ℂ (Set.range (standardHeckeElement F r)) := by
  unfold standardMonomial
  apply list_prod_mem
  intro x hx
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
  exact pow_mem (Algebra.subset_adjoin (Set.mem_range_self i)) _

/-! ### Tail sums and the dominance weight -/

theorem tailSum_last {r : ℕ} (ν : Fin (r + 1) → ℤ) : tailSum ν r = ν (Fin.last r) := by
  simp only [tailSum, Finset.sum_filter]
  rw [Finset.sum_eq_single (Fin.last r)]
  · simp
  · intro j _ hj
    have : j.val ≠ r := fun h => hj (Fin.ext h)
    have := j.isLt
    split_ifs <;> omega
  · simp

theorem tailSum_of_le {r : ℕ} (ν : Fin (r + 1) → ℤ) {k : ℕ} (hk : r + 1 ≤ k) :
    tailSum ν k = 0 := by
  simp only [tailSum]
  apply Finset.sum_eq_zero
  intro j hj
  have := (Finset.mem_filter.1 hj).2
  have := j.isLt
  omega

theorem tailSum_le_total {r : ℕ} {ν : Fin (r + 1) → ℤ} (hν : ∀ j, 0 ≤ ν j) (k : ℕ) :
    tailSum ν k ≤ ∑ j, ν j :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j _ _ => hν j)

/-- The sum of all tail sums. -/
def weight {r : ℕ} (ν : Fin (r + 1) → ℤ) : ℤ := ∑ k : Fin (r + 1), tailSum ν k

theorem weight_le {r : ℕ} {ν : Fin (r + 1) → ℤ} (hν : ∀ j, 0 ≤ ν j) :
    weight ν ≤ (r + 1 : ℤ) * ∑ j, ν j := by
  calc weight ν ≤ ∑ _k : Fin (r + 1), ∑ j, ν j :=
        Finset.sum_le_sum fun k _ => tailSum_le_total hν k
    _ = _ := by simp

theorem weight_lt {r : ℕ} {lam ν : Fin (r + 1) → ℤ} (hne : ν ≠ lam)
    (hdom : ∀ k, tailSum lam k ≤ tailSum ν k) : weight lam < weight ν := by
  unfold weight
  apply Finset.sum_lt_sum (fun k _ => hdom k.val)
  by_contra hall
  push Not at hall
  apply hne
  apply eq_of_tailSum_eq
  intro k
  by_cases hk : k < r + 1
  · exact le_antisymm (hall ⟨k, hk⟩ (Finset.mem_univ _)) (hdom k)
  · have hk' : r + 1 ≤ k := by omega
    rw [tailSum_of_le _ hk', tailSum_of_le _ hk']

theorem nonneg_of_dominated {r : ℕ} {lam ν : Fin (r + 1) → ℤ} (hν : Antitone ν)
    (h0 : 0 ≤ lam (Fin.last r)) (hdom : ∀ k, tailSum lam k ≤ tailSum ν k) (j : Fin (r + 1)) :
    0 ≤ ν j := by
  have h := hdom r
  rw [tailSum_last, tailSum_last] at h
  exact h0.trans (h.trans (hν (Fin.le_last j)))

/-! ### Triangular induction -/

variable {F}

/-- Under triangularity, every double coset of an antitone nonnegative exponent lies in
the subalgebra generated by the standard elements. -/
theorem torusHeckeElement_mem (htri : StandardMonomialTriangularity F) {r : ℕ} :
    ∀ (n : ℕ) (lam : Fin (r + 1) → ℤ), Antitone lam → 0 ≤ lam (Fin.last r) →
      (r + 1 : ℤ) * ∑ j, lam j - weight lam < n →
        torusHeckeElement F lam ∈ Algebra.adjoin ℂ (Set.range (standardHeckeElement F r)) := by
  classical
  intro n
  induction n with
  | zero =>
    intro lam hlam h0 hn
    have hnn : ∀ j, 0 ≤ lam j := fun j => h0.trans (hlam (Fin.le_last j))
    have := weight_le hnn
    push_cast at hn
    linarith
  | succ n ih =>
    intro lam hlam h0 hn
    set A := Algebra.adjoin ℂ (Set.range (standardHeckeElement F r))
    set T := ∑ j, lam j
    have hnn : ∀ j, 0 ≤ lam j := fun j => h0.trans (hlam (Fin.le_last j))
    obtain ⟨hsupp, hval⟩ := htri r (gapExponent lam)
    rw [monomialExponent_gapExponent hlam h0] at hsupp hval
    set M := standardMonomial F (gapExponent lam)
    have hM : M ∈ A := standardMonomial_mem F _
    let S : Finset (Fin (r + 1) → ℤ) :=
      (Fintype.piFinset fun _ => Finset.Icc 0 T).filter fun ν =>
        Antitone ν ∧ (∀ k, tailSum lam k ≤ tailSum ν k) ∧ ∑ j, ν j = T
    have hmemS : ∀ ν : Fin (r + 1) → ℤ, Antitone ν → (∀ k, tailSum lam k ≤ tailSum ν k) →
        ∑ j, ν j = T → ν ∈ S := by
      intro ν hν hdom hsum
      have hνnn := nonneg_of_dominated hν h0 hdom
      refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun j => Finset.mem_Icc.2
        ⟨hνnn j, ?_⟩, hν, hdom, hsum⟩
      rw [← hsum]
      exact Finset.single_le_sum (fun i _ => hνnn i) (Finset.mem_univ j)
    have hS : ∀ ν ∈ S, Antitone ν := fun ν hν => (Finset.mem_filter.1 hν).2.1
    have hexp := eq_sum_of_support F M S hS fun x hx => by
      obtain ⟨ν, hν, hxν, hdom, hsum⟩ := hsupp x hx
      exact ⟨ν, hmemS ν hν hdom hsum, hxν⟩
    have hlamS : lam ∈ S := hmemS lam hlam (fun _ => le_rfl) rfl
    rw [← Finset.add_sum_erase S _ hlamS] at hexp
    set R := ∑ ν ∈ S.erase lam, M (standardTorus F ν) • torusHeckeElement F ν
    have hR : R ∈ A := by
      apply sum_mem
      intro ν hν
      obtain ⟨hνlam, hνS⟩ := Finset.mem_erase.1 hν
      obtain ⟨-, hνa, hdom, hsum⟩ := Finset.mem_filter.1 hνS
      have hνnn := nonneg_of_dominated hνa h0 hdom
      refine Subalgebra.smul_mem _ (ih ν hνa (hνnn _) ?_) _
      have h1 := weight_lt hνlam hdom
      have h2 := weight_le hνnn
      rw [hsum] at h2 ⊢
      push_cast at hn ⊢
      linarith
    have hcoef : M (standardTorus F lam) ≠ 0 := hval
    have hdiff : M - R = M (standardTorus F lam) • torusHeckeElement F lam := by
      rw [sub_eq_iff_eq_add]
      exact hexp
    have heq : torusHeckeElement F lam = (M (standardTorus F lam))⁻¹ • (M - R) := by
      rw [hdiff, smul_smul, inv_mul_cancel₀ hcoef, one_smul]
    rw [heq]
    exact Subalgebra.smul_mem _ (sub_mem hM hR) _

/-! ### The central shift -/

variable (F) in
/-- The last standard diagonal element is the scalar uniformizer. -/
theorem standardDiagonal_last (r : ℕ) :
    standardDiagonal F r (Fin.last (r + 1)) = diagonalUnits fun _ => standardUniformizer F := by
  unfold standardDiagonal
  congr 1
  funext j
  have hj : j.val < (Fin.last (r + 1)).val := by simp only [Fin.val_last]; exact j.isLt
  simp only [hj, ↓reduceIte]

variable (F) in
theorem standardDiagonal_last_mem_center (r : ℕ) :
    standardDiagonal F r (Fin.last (r + 1)) ∈ Subgroup.center (GeneralLinear (r + 1) F.Carrier) := by
  rw [Subgroup.mem_center_iff]
  intro g
  rw [standardDiagonal_last]
  apply Units.ext
  ext i j
  simp [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

variable (F) in
theorem pow_standardDiagonal_last_mul_torus (r m : ℕ) (lam : Fin (r + 1) → ℤ) :
    standardDiagonal F r (Fin.last (r + 1)) ^ m * standardTorus F lam =
      standardTorus F fun j => lam j + m := by
  rw [standardDiagonal_last]
  show (diagonalUnits fun _ => standardUniformizer F) ^ m *
      diagonalUnits (fun j => standardUniformizer F ^ lam j) =
    diagonalUnits fun j => standardUniformizer F ^ (lam j + (m : ℤ))
  rw [← map_pow, ← map_mul]
  congr 1
  funext j
  simp only [Pi.pow_apply, Pi.mul_apply]
  rw [← zpow_natCast, ← zpow_add, add_comm]

variable (F) in
theorem pow_mul_cosetElement (r m : ℕ) (x : GeneralLinear (r + 1) F.Carrier) :
    standardHeckeElement F r (Fin.last (r + 1)) ^ m * cosetElement F x =
      cosetElement F (standardDiagonal F r (Fin.last (r + 1)) ^ m * x) := by
  have hz : standardDiagonal F r (Fin.last (r + 1)) ∈
      Subgroup.normalizer ((sphericalOpenSubgroup F r).toSubgroup :
        Set (GeneralLinear (r + 1) F.Carrier)) :=
    Subgroup.center_le_normalizer _ (standardDiagonal_last_mem_center F r)
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', mul_assoc, ih]
    have h := Hecke.HeckeAlgebra.Corner.doubleCoset_mul_mul_of_mem_normalizer
      (sphericalOpenSubgroup F r) (sphericalOpenSubgroup_isCompact F r) (sphericalHaar F r)
      hz (one_mem _) (standardDiagonal F r (Fin.last (r + 1)) ^ m * x)
    rw [Hecke.HeckeAlgebra.Corner.doubleCoset_one, mul_one, mul_one] at h
    rw [pow_succ', mul_assoc]
    exact h

/-! ### Generation -/

/-- Under triangularity, a power of the last standard element moves every spherical
element into the subalgebra generated by the standard elements. -/
theorem exists_pow_mul_mem (htri : StandardMonomialTriangularity F) {r : ℕ}
    (f : SphericalHeckeAlgebra F r) :
    ∃ m : ℕ, standardHeckeElement F r (Fin.last (r + 1)) ^ m * f ∈
      Algebra.adjoin ℂ (Set.range (standardHeckeElement F r)) := by
  have hf : f ∈ Submodule.span ℂ (Set.range (Hecke.HeckeAlgebra.Corner.doubleCoset
      (sphericalOpenSubgroup F r) (sphericalOpenSubgroup_isCompact F r) (sphericalHaar F r))) := by
    rw [Hecke.HeckeAlgebra.Corner.span_range_doubleCoset]
    exact Submodule.mem_top
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    obtain ⟨lam, hlam, hg⟩ := exists_antitone_mem F g
    refine ⟨(-lam (Fin.last r)).toNat, ?_⟩
    rw [Hecke.HeckeAlgebra.Corner.doubleCoset_eq_of_mem _ _ _ hg, pow_mul_cosetElement,
      pow_standardDiagonal_last_mul_torus]
    have hanti : Antitone fun j => lam j + ((-lam (Fin.last r)).toNat : ℤ) :=
      fun i j hij => by have := hlam hij; simp only; linarith
    have h0 : 0 ≤ lam (Fin.last r) + ((-lam (Fin.last r)).toNat : ℤ) := by
      have := Int.self_le_toNat (-lam (Fin.last r))
      omega
    obtain ⟨n, hn⟩ := exists_nat_gt ((r + 1 : ℤ) *
      ∑ j, (lam j + ((-lam (Fin.last r)).toNat : ℤ)) -
        weight fun j => lam j + ((-lam (Fin.last r)).toNat : ℤ))
    exact torusHeckeElement_mem htri n _ hanti h0 hn
  | zero => exact ⟨0, by rw [mul_zero]; exact zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨m₁, h₁⟩ := hx
    obtain ⟨m₂, h₂⟩ := hy
    refine ⟨m₁ + m₂, ?_⟩
    have hT : standardHeckeElement F r (Fin.last (r + 1)) ∈
        Algebra.adjoin ℂ (Set.range (standardHeckeElement F r)) :=
      Algebra.subset_adjoin ⟨_, rfl⟩
    rw [mul_add]
    apply add_mem
    · rw [Nat.add_comm m₁ m₂, pow_add, mul_assoc]
      exact mul_mem (pow_mem hT _) h₁
    · rw [pow_add, mul_assoc]
      exact mul_mem (pow_mem hT _) h₂
  | smul c x _ hx =>
    obtain ⟨m, h⟩ := hx
    exact ⟨m, by rw [mul_smul_comm]; exact Subalgebra.smul_mem _ h c⟩

end SphericalGeneration

open SphericalGeneration in
/-- Generation of the spherical Hecke algebra, assuming the triangularity of the
standard monomials. -/
theorem sphericalHeckeGeneration_of_triangularity
    (htri : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p), StandardMonomialTriangularity F) :
    SphericalHeckeGenerationStatement.{uF} := by
  intro p _ F r f
  exact exists_pow_mul_mem (htri p F) f

/-- Generation of the spherical Hecke algebra: after multiplication by a power of the
last standard element, every spherical element lies in the subalgebra generated by the
standard elements. -/
theorem sphericalHeckeGeneration : SphericalHeckeGenerationStatement.{uF} :=
  sphericalHeckeGeneration_of_triangularity fun _ _ F => standardMonomialTriangularity F

end Langlands.Unramified
