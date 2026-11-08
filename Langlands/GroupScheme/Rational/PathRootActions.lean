import Langlands.GroupScheme.Rational.PathFundamentalWeights
import Langlands.GroupScheme.MatrixRepresentation.TorusEquivariantAdditive
import Mathlib.Tactic.Module

/-! # Root maps acting on the path weight lines -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Polynomial

/-! ### Shifts of path weights by path roots -/

namespace Langlands.LinearAlgebra.RootDatumPathWeights

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] {P : RootDatum ι M N} {b : P.Base}
  {L : ℕ} {β : Fin L → b.support}

/-- The difference of two path weights is the sum of the path roots between them. -/
theorem pathWeight_sub_pathWeight (ω : M) {l j : ℕ} (h : l ≤ j) :
    pathWeight β ω l - pathWeight β ω j = ∑ t ∈ Finset.Ico l j, pathRoot β t := by
  simp only [pathWeight]
  rw [Finset.sum_Ico_eq_sub _ h]
  abel

/-- A path root is the difference of consecutive path weights. -/
theorem pathRoot_eq_sub (ω : M) (i : ℕ) :
    pathRoot β i = pathWeight β ω i - pathWeight β ω (i + 1) := by
  rw [pathWeight_succ]
  abel

/-- The indicator coefficient of an initial segment. -/
private def ind (j t : ℕ) : ℤ := if t < j then 1 else 0

private theorem sum_range_eq_sum_ind {j : ℕ} (hj : j ≤ L) :
    ∑ t ∈ Finset.range j, pathRoot β t = ∑ t ∈ Finset.range L, ind j t • pathRoot β t := by
  simp only [ind, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  congr 1
  ext t
  simp only [Finset.mem_range, Finset.mem_filter]
  omega

private theorem coeff_eq_zero (hβ : IsPathComponent β) {e : ℕ → ℤ}
    (h : ∑ t ∈ Finset.range L, e t • pathRoot β t = 0) {t : ℕ} (ht : t < L) : e t = 0 := by
  have hli : LinearIndependent ℤ (fun i : Fin L => P.root (β i : ι)) :=
    b.linearIndepOn_root.linearIndependent.comp β hβ.injective
  rw [Finset.sum_range] at h
  have h' : ∑ i : Fin L, e i • P.root (β i : ι) = 0 := by
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pathRoot_of_lt β i.2]
  exact Fintype.linearIndependent_iff.mp hli _ h' ⟨t, ht⟩

/-- Coefficient equations for a shift of a path weight by a multiple of a difference of path
weights. -/
private theorem coeff_shift (hβ : IsPathComponent β) (ω : M) {j l' a c : ℕ} (hj : j ≤ L)
    (hl' : l' ≤ L) (ha : a ≤ L) (hc : c ≤ L) (z : ℤ)
    (h : pathWeight β ω j + z • (pathWeight β ω a - pathWeight β ω c) = pathWeight β ω l')
    {t : ℕ} (ht : t < L) : ind l' t - ind j t + z * (ind c t - ind a t) = 0 := by
  apply coeff_eq_zero hβ _ ht
  simp only [pathWeight] at h
  have h0 : (∑ i ∈ Finset.range l', pathRoot β i) - ∑ i ∈ Finset.range j, pathRoot β i +
      z • ((∑ i ∈ Finset.range c, pathRoot β i) - ∑ i ∈ Finset.range a, pathRoot β i) = 0 := by
    rw [← sub_eq_zero.mpr h]
    module
  rw [sum_range_eq_sum_ind hl', sum_range_eq_sum_ind hj, sum_range_eq_sum_ind ha,
    sum_range_eq_sum_ind hc] at h0
  rw [← h0]
  simp only [smul_sub, Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  module

/-- Shifting a path weight by a positive multiple of the path root `ε_i - ε_l` (`i < l`) gives a
path weight exactly when the multiple is one and the start is `ε_l`; the result is `ε_i`. -/
theorem pathWeight_add_nsmul_sub_eq_iff (hβ : IsPathComponent β) (ω : M) {i l j l' m : ℕ}
    (hil : i < l) (hl : l ≤ L) (hj : j ≤ L) (hl' : l' ≤ L) (hm : 1 ≤ m) :
    pathWeight β ω j + m • (pathWeight β ω i - pathWeight β ω l) = pathWeight β ω l' ↔
      m = 1 ∧ j = l ∧ l' = i := by
  constructor
  · intro h
    rw [← natCast_zsmul] at h
    have e := fun t (ht : t < L) => coeff_shift hβ ω hj hl' (by omega) hl (m : ℤ) h ht
    have e1 := e i (by omega)
    simp only [ind] at e1
    have h1 : m = 1 ∧ i < j ∧ l' ≤ i := by split_ifs at e1 <;> omega
    have e2 := e (l - 1) (by omega)
    simp only [ind] at e2
    have h2 : l ≤ j := by split_ifs at e2 <;> omega
    have h3 : j ≤ l := by
      by_cases hlL : l < L
      · have e3 := e l hlL
        simp only [ind] at e3
        split_ifs at e3 <;> omega
      · omega
    have h4 : i ≤ l' := by
      by_cases hi0 : i = 0
      · omega
      · have e4 := e (i - 1) (by omega)
        simp only [ind] at e4
        split_ifs at e4 <;> omega
    exact ⟨h1.1, by omega, by omega⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rw [one_smul, add_sub_cancel]

/-- Shifting a path weight by a positive multiple of the negative path root `ε_l - ε_i`
(`i < l`) gives a path weight exactly when the multiple is one and the start is `ε_i`; the
result is `ε_l`. -/
theorem pathWeight_add_nsmul_sub_eq_iff' (hβ : IsPathComponent β) (ω : M) {i l j l' m : ℕ}
    (hil : i < l) (hl : l ≤ L) (hj : j ≤ L) (hl' : l' ≤ L) (hm : 1 ≤ m) :
    pathWeight β ω j + m • (pathWeight β ω l - pathWeight β ω i) = pathWeight β ω l' ↔
      m = 1 ∧ j = i ∧ l' = l := by
  constructor
  · intro h
    rw [← natCast_zsmul] at h
    have e := fun t (ht : t < L) => coeff_shift hβ ω hj hl' hl (by omega) (m : ℤ) h ht
    have e1 := e i (by omega)
    simp only [ind] at e1
    have h1 : m = 1 ∧ i < l' ∧ j ≤ i := by split_ifs at e1 <;> omega
    have e2 := e (l - 1) (by omega)
    simp only [ind] at e2
    have h2 : l ≤ l' := by split_ifs at e2 <;> omega
    have h3 : l' ≤ l := by
      by_cases hlL : l < L
      · have e3 := e l hlL
        simp only [ind] at e3
        split_ifs at e3 <;> omega
      · omega
    have h4 : i ≤ j := by
      by_cases hi0 : i = 0
      · omega
      · have e4 := e (i - 1) (by omega)
        simp only [ind] at e4
        split_ifs at e4 <;> omega
    exact ⟨h1.1, by omega, by omega⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rw [one_smul, add_sub_cancel]

/-- No positive multiple of a simple root off the path shifts a path weight to a path weight. -/
theorem pathWeight_add_nsmul_root_ne (hβ : IsPathComponent β) {ω : M}
    (hω : IsPathFundamental β ω) {z : b.support} (hz : z ∉ Set.range β) {m : ℕ} (hm : 1 ≤ m)
    (j l : ℕ) : pathWeight β ω j + m • P.root (z : ι) ≠ pathWeight β ω l := by
  intro h
  have e := congrArg (fun x => P.toLinearMap x (P.coroot (z : ι))) h
  simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply,
    pairing_pathWeight_of_not_mem hβ hω hz, RootPairing.root_coroot_eq_pairing,
    P.pairing_same, zero_add, nsmul_eq_mul] at e
  omega

/-- No positive multiple of the negative of a simple root off the path shifts a path weight to a
path weight. -/
theorem pathWeight_add_nsmul_neg_root_ne (hβ : IsPathComponent β) {ω : M}
    (hω : IsPathFundamental β ω) {z : b.support} (hz : z ∉ Set.range β) {m : ℕ} (hm : 1 ≤ m)
    (j l : ℕ) : pathWeight β ω j + m • (-P.root (z : ι)) ≠ pathWeight β ω l := by
  intro h
  have e := congrArg (fun x => P.toLinearMap x (P.coroot (z : ι))) h
  simp only [map_add, map_nsmul, map_neg, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.neg_apply, pairing_pathWeight_of_not_mem hβ hω hz,
    RootPairing.root_coroot_eq_pairing, P.pairing_same, zero_add, nsmul_eq_mul] at e
  omega

end Langlands.LinearAlgebra.RootDatumPathWeights

/-! ### Additive-group representations with at most linear coefficients -/

namespace Langlands.GroupScheme.MatrixRepresentation.AdditiveDividedPowers

variable {k : Type u} [Field k] {n : Type} [Fintype n] [DecidableEq n]
  (σ : MatrixRepresentation (VectorGroup.groupScheme (CommRingCat.of k) 1) n)

theorem coefficientMatrix_eq_zero_of_dividedPower {m : ℕ} (h : dividedPower σ m = 0) :
    coefficientMatrix σ m = 0 := by
  have h' : Matrix.toLin' (coefficientMatrix σ m) = Matrix.toLin' (0 : Matrix n n k) := by
    rw [← dividedPower_eq_toLin, h, map_zero]
  exact Matrix.toLin'.injective h'

/-- If all divided powers of degree at least two vanish, the universal matrix is linear. -/
theorem univariateMatrix_eq_of_dividedPower (h : ∀ m, 2 ≤ m → dividedPower σ m = 0) :
    univariateMatrix σ =
      1 + (Polynomial.X : k[X]) • (coefficientMatrix σ 1).map (Polynomial.C : k →+* k[X]) := by
  ext i j m
  have hc : (univariateMatrix σ i j).coeff m = coefficientMatrix σ m i j := rfl
  rw [hc, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Polynomial.coeff_add,
    smul_eq_mul, mul_comm, Polynomial.coeff_C_mul_X, Matrix.one_apply]
  rcases m with _ | _ | m
  · rw [coefficientMatrix_zero, Matrix.one_apply]
    split_ifs <;> simp_all [Polynomial.coeff_one]
  · split_ifs <;> simp_all [Polynomial.coeff_one]
  · rw [coefficientMatrix_eq_zero_of_dividedPower σ (h (m + 2) (by omega))]
    split_ifs <;> simp_all [Polynomial.coeff_one]

/-- If all divided powers of degree at least two vanish, the actual matrix at coordinate `c` is
`1 + c A₁`. -/
theorem affineMatrix_eq_one_add (h : ∀ m, 2 ≤ m → dividedPower σ m = 0)
    (S : CommAlgCat.{u} k) (c : S) :
    (σ.affineMatrix S (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1) S (fun _ => c)) :
        Matrix n n S) =
      1 + c • (coefficientMatrix σ 1).map (algebraMap k S) := by
  rw [← univariateMatrix_aeval, univariateMatrix_eq_of_dividedPower σ h]
  ext i j
  simp [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.map_apply,
    Polynomial.aeval_C, apply_ite]
  ring

/-- If all positive divided powers vanish, the actual matrix is the identity at every coordinate. -/
theorem affineMatrix_eq_one (h : ∀ m, 1 ≤ m → dividedPower σ m = 0)
    (S : CommAlgCat.{u} k) (c : S) :
    (σ.affineMatrix S (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1) S (fun _ => c)) :
        Matrix n n S) = 1 := by
  rw [affineMatrix_eq_one_add σ (fun m hm => h m (by omega)),
    coefficientMatrix_eq_zero_of_dividedPower σ (h 1 le_rfl)]
  simp

end Langlands.GroupScheme.MatrixRepresentation.AdditiveDividedPowers

/-! ### Root maps on the path weight lines -/

namespace Langlands.GroupScheme.SplitPinning

open Langlands.LinearAlgebra.RootDatumPathWeights
open MatrixRepresentation.AdditiveDividedPowers

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {p : SplitPinning G} {n : Type} [Fintype n] [DecidableEq n]
  {ρ : MatrixRepresentation G n} {L : ℕ} {β : Fin L → p.base.support}
  {lam : characterLattice p.torus}
  {x : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G} {γ : characterLattice p.torus}

/-- A divided power of an equivariant additive map kills a path line whose shifted weight is not a
path weight. -/
theorem dividedPower_eq_zero_of_shift_ne (hρ : p.IsHighestWeight ρ lam)
    (hβ : IsPathComponent β) (hlam : IsPathFundamental β lam)
    (hx : VectorGroup.IsTorusEquivariant p.inclusion x γ) {m j : ℕ}
    (h : ∀ l ≤ L, pathWeight β lam j + m • γ ≠ pathWeight β lam l) {v : n → k}
    (hv : v ∈ p.representationWeightSpace ρ (pathWeight β lam j)) :
    dividedPower (ρ.restrict x) m v = 0 := by
  have hmem := dividedPower_mem_representationWeightSpace_of_equivariant hx ρ m hv
  have hbot : p.representationWeightSpace ρ (pathWeight β lam j + m • γ) = ⊥ := by
    by_contra hne
    obtain ⟨l, hl, he⟩ := exists_eq_pathWeight_of_isHighestWeight hρ hβ hlam hne
    exact h l hl he
  rw [hbot, Submodule.mem_bot] at hmem
  exact hmem

/-- A divided power vanishes when no shift of a path weight is a path weight. -/
theorem dividedPower_eq_zero_of_forall_shift_ne (hρ : p.IsHighestWeight ρ lam)
    (hβ : IsPathComponent β) (hlam : IsPathFundamental β lam)
    (hx : VectorGroup.IsTorusEquivariant p.inclusion x γ) {m : ℕ}
    (h : ∀ j ≤ L, ∀ l ≤ L, pathWeight β lam j + m • γ ≠ pathWeight β lam l) :
    dividedPower (ρ.restrict x) m = 0 := by
  apply (pathWeightBasis hρ hβ hlam).ext
  intro j
  rw [LinearMap.zero_apply]
  exact dividedPower_eq_zero_of_shift_ne hρ hβ hlam hx (h j (by omega))
    (pathWeightBasis_mem hρ hβ hlam j)

/-- A divided power maps a path line to the path line of the shifted weight. -/
theorem dividedPower_mem_of_shift_eq (hx : VectorGroup.IsTorusEquivariant p.inclusion x γ)
    {m j l : ℕ} (h : pathWeight β lam j + m • γ = pathWeight β lam l) {v : n → k}
    (hv : v ∈ p.representationWeightSpace ρ (pathWeight β lam j)) :
    dividedPower (ρ.restrict x) m v ∈ p.representationWeightSpace ρ (pathWeight β lam l) := by
  rw [← h]
  exact dividedPower_mem_representationWeightSpace_of_equivariant hx ρ m hv

/-- The `m`-th divided power of an equivariant additive map, as a linear map between two path
lines whose weights differ by `m` times its character. -/
def pathLineShiftMap (hx : VectorGroup.IsTorusEquivariant p.inclusion x γ) {m j l : ℕ}
    (h : pathWeight β lam j + m • γ = pathWeight β lam l) :
    p.representationWeightSpace ρ (pathWeight β lam j) →ₗ[k]
      p.representationWeightSpace ρ (pathWeight β lam l) where
  toFun v := ⟨dividedPower (ρ.restrict x) m v, dividedPower_mem_of_shift_eq hx h v.2⟩
  map_add' v w := Subtype.ext (map_add (dividedPower (ρ.restrict x) m) (v : n → k) w)
  map_smul' c v := Subtype.ext (map_smul (dividedPower (ρ.restrict x) m) c (v : n → k))

@[simp] theorem pathLineShiftMap_apply (hx : VectorGroup.IsTorusEquivariant p.inclusion x γ)
    {m j l : ℕ} (h : pathWeight β lam j + m • γ = pathWeight β lam l)
    (v : p.representationWeightSpace ρ (pathWeight β lam j)) :
    (pathLineShiftMap hx h v : n → k) = dividedPower (ρ.restrict x) m v := rfl

section PathRoot

variable (hρ : p.IsHighestWeight ρ lam) (hβ : IsPathComponent β)
  (hlam : IsPathFundamental β lam) {i l : ℕ} (hil : i < l) (hl : l ≤ L)
include hρ hβ hlam hil hl

/-- For a map of the path root `ε_i - ε_l`, divided powers of degree at least two vanish. -/
theorem pathRootMap_dividedPower_eq_zero
    (hx : VectorGroup.IsTorusEquivariant p.inclusion x
      (pathWeight β lam i - pathWeight β lam l)) {m : ℕ} (hm : 2 ≤ m) :
    dividedPower (ρ.restrict x) m = 0 :=
  dividedPower_eq_zero_of_forall_shift_ne hρ hβ hlam hx fun j hj l' hl' h => by
    have := (pathWeight_add_nsmul_sub_eq_iff hβ lam hil hl hj hl' (by omega)).mp h
    omega

omit hρ hlam in
/-- For a map of the path root `ε_i - ε_l`, the first divided power maps line `l` into line
`i`. -/
theorem pathRootMap_dividedPower_one_mem
    (hx : VectorGroup.IsTorusEquivariant p.inclusion x
      (pathWeight β lam i - pathWeight β lam l)) {v : n → k}
    (hv : v ∈ p.representationWeightSpace ρ (pathWeight β lam l)) :
    dividedPower (ρ.restrict x) 1 v ∈ p.representationWeightSpace ρ (pathWeight β lam i) :=
  dividedPower_mem_of_shift_eq hx
    ((pathWeight_add_nsmul_sub_eq_iff hβ lam hil hl hl (by omega) le_rfl).mpr
      ⟨rfl, rfl, rfl⟩) hv

/-- For a map of the path root `ε_i - ε_l`, the first divided power kills every other path
line. -/
theorem pathRootMap_dividedPower_one_eq_zero
    (hx : VectorGroup.IsTorusEquivariant p.inclusion x
      (pathWeight β lam i - pathWeight β lam l)) {j : ℕ} (hj : j ≤ L) (hjl : j ≠ l)
    {v : n → k} (hv : v ∈ p.representationWeightSpace ρ (pathWeight β lam j)) :
    dividedPower (ρ.restrict x) 1 v = 0 :=
  dividedPower_eq_zero_of_shift_ne hρ hβ hlam hx (fun _l' hl' h =>
    hjl ((pathWeight_add_nsmul_sub_eq_iff hβ lam hil hl hj hl' le_rfl).mp h).2.1) hv

/-- For a map of the negative path root `ε_l - ε_i`, divided powers of degree at least two
vanish. -/
theorem negPathRootMap_dividedPower_eq_zero
    (hx : VectorGroup.IsTorusEquivariant p.inclusion x
      (pathWeight β lam l - pathWeight β lam i)) {m : ℕ} (hm : 2 ≤ m) :
    dividedPower (ρ.restrict x) m = 0 :=
  dividedPower_eq_zero_of_forall_shift_ne hρ hβ hlam hx fun j hj l' hl' h => by
    have := (pathWeight_add_nsmul_sub_eq_iff' hβ lam hil hl hj hl' (by omega)).mp h
    omega

omit hρ hlam in
/-- For a map of the negative path root `ε_l - ε_i`, the first divided power maps line `i` into
line `l`. -/
theorem negPathRootMap_dividedPower_one_mem
    (hx : VectorGroup.IsTorusEquivariant p.inclusion x
      (pathWeight β lam l - pathWeight β lam i)) {v : n → k}
    (hv : v ∈ p.representationWeightSpace ρ (pathWeight β lam i)) :
    dividedPower (ρ.restrict x) 1 v ∈ p.representationWeightSpace ρ (pathWeight β lam l) :=
  dividedPower_mem_of_shift_eq hx
    ((pathWeight_add_nsmul_sub_eq_iff' hβ lam hil hl (by omega) hl le_rfl).mpr
      ⟨rfl, rfl, rfl⟩) hv

/-- For a map of the negative path root `ε_l - ε_i`, the first divided power kills every other
path line. -/
theorem negPathRootMap_dividedPower_one_eq_zero
    (hx : VectorGroup.IsTorusEquivariant p.inclusion x
      (pathWeight β lam l - pathWeight β lam i)) {j : ℕ} (hj : j ≤ L) (hji : j ≠ i)
    {v : n → k} (hv : v ∈ p.representationWeightSpace ρ (pathWeight β lam j)) :
    dividedPower (ρ.restrict x) 1 v = 0 :=
  dividedPower_eq_zero_of_shift_ne hρ hβ hlam hx (fun _l' hl' h =>
    hji ((pathWeight_add_nsmul_sub_eq_iff' hβ lam hil hl hj hl' le_rfl).mp h).2.1) hv

end PathRoot

/-- An additive map equivariant for a simple root off the path acts trivially on the
representation. -/
theorem offPathRootMap_dividedPower_eq_zero (hρ : p.IsHighestWeight ρ lam)
    (hβ : IsPathComponent β) (hlam : IsPathFundamental β lam) {z : p.base.support}
    (hz : z ∉ Set.range β)
    (hx : VectorGroup.IsTorusEquivariant p.inclusion x (p.rootDatum.root (z : p.rootIndex)))
    {m : ℕ} (hm : 1 ≤ m) : dividedPower (ρ.restrict x) m = 0 :=
  dividedPower_eq_zero_of_forall_shift_ne hρ hβ hlam hx fun j _ l _ =>
    pathWeight_add_nsmul_root_ne hβ hlam hz hm j l

/-- An additive map equivariant for the negative of a simple root off the path acts trivially on
the representation. -/
theorem offPathNegRootMap_dividedPower_eq_zero (hρ : p.IsHighestWeight ρ lam)
    (hβ : IsPathComponent β) (hlam : IsPathFundamental β lam) {z : p.base.support}
    (hz : z ∉ Set.range β)
    (hx : VectorGroup.IsTorusEquivariant p.inclusion x (-p.rootDatum.root (z : p.rootIndex)))
    {m : ℕ} (hm : 1 ≤ m) : dividedPower (ρ.restrict x) m = 0 :=
  dividedPower_eq_zero_of_forall_shift_ne hρ hβ hlam hx fun j _ l _ =>
    pathWeight_add_nsmul_neg_root_ne hβ hlam hz hm j l

end Langlands.GroupScheme.SplitPinning
