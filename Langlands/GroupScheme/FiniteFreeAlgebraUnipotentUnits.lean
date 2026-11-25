import Langlands.GroupScheme.FiniteFreeAlgebraUnitsQuotient
import Langlands.GroupScheme.Torus.Split
import Langlands.GroupScheme.AffineLinearEmbedding.Coordinate
import Langlands.GroupScheme.Unipotent.CoordinateBialgebra
import Langlands.GroupScheme.UnitriangularUnipotent.WeightCore
import Langlands.GroupScheme.Rational.TorusQuotientRadicalDescent

/-! # The unipotent part of the unit group of a split finite free algebra

For an algebra map `π : A → B` with a basis of `A` adapted to `π`, the kernel `1 + J` of the
unit-group map is a smooth connected unipotent group scheme, and it is the unipotent radical of
the unit group of `A` when the unit group of `B` is a torus and `π` has an algebra section. The
unit group of `R^N` is the split torus. See the paired Markdown file.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.FiniteFreeAlgebraUnits.UnipotentPart

variable {R : Type u} [CommRing R] {A : Type u} [Ring A] [Algebra R A]
  {B : Type u} [Ring B] [Algebra R B] (π : A →ₐ[R] B)
  {N d : ℕ} (b : Module.Basis (Fin N ⊕ Fin d) R A)

/-- The radical part `Σ c_j ⊗ e_j` of a point, for the basis vectors `e_j = b (inr j)`. -/
def radicalPart {S : Type u} [CommRing S] [Algebra R S] (c : Fin d → S) : S ⊗[R] A :=
  ∑ j, c j ⊗ₜ[R] b (Sum.inr j)

theorem map_radicalPart (hb : ∀ j, π (b (Sum.inr j)) = 0)
    {S : Type u} [CommRing S] [Algebra R S] (c : Fin d → S) :
    Algebra.TensorProduct.map (AlgHom.id R S) π (radicalPart b c) = 0 := by
  simp [radicalPart, hb]

/-- The radical part of the universal point. -/
abbrev universalRadical : MvPolynomial (Fin d) R ⊗[R] A :=
  radicalPart b (fun j => (MvPolynomial.X j : MvPolynomial (Fin d) R))

theorem radicalPart_eq_map {S : Type u} [CommRing S] [Algebra R S] (c : Fin d → S) :
    radicalPart b c =
      Algebra.TensorProduct.map (MvPolynomial.aeval c) (AlgHom.id R A) (universalRadical b) := by
  simp [radicalPart, map_sum]

theorem isNilpotent_radicalPart (hnil : IsNilpotent (universalRadical b))
    {S : Type u} [CommRing S] [Algebra R S] (c : Fin d → S) :
    IsNilpotent (radicalPart b c) := by
  rw [radicalPart_eq_map]
  exact hnil.map _

section Coordinates

variable {S : Type u} [CommRing S] [Algebra R S]

/-- The kernel coordinates of an element of `S ⊗[R] A`. -/
def coords (x : S ⊗[R] A) : Fin d → S :=
  fun j => (Algebra.TensorProduct.basis S b).repr x (Sum.inr j)

/-- The base change of `π` is `S`-linear. -/
theorem map_smul_tensor (c : S) (y : S ⊗[R] A) :
    Algebra.TensorProduct.map (AlgHom.id R S) π (c • y) =
      c • Algebra.TensorProduct.map (AlgHom.id R S) π y := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  congr 1
  simp [Algebra.TensorProduct.algebraMap_apply]

variable (b' : Module.Basis (Fin N) R B)

theorem eq_radicalPart_of_map_eq_zero (hb' : ∀ i, π (b (Sum.inl i)) = b' i)
    (hb : ∀ j, π (b (Sum.inr j)) = 0) (x : S ⊗[R] A)
    (hx : Algebra.TensorProduct.map (AlgHom.id R S) π x = 0) :
    x = radicalPart b (coords b x) := by
  set e := Algebra.TensorProduct.basis S b
  have hsum := e.sum_repr x
  rw [Fintype.sum_sum_type] at hsum
  have himg : ∑ i, e.repr x (Sum.inl i) • Algebra.TensorProduct.basis S b' i = 0 := by
    have := congrArg (Algebra.TensorProduct.map (AlgHom.id R S) π) hsum
    rw [hx, map_add, map_sum, map_sum] at this
    simp only [map_smul_tensor, e, Algebra.TensorProduct.basis_apply,
      Algebra.TensorProduct.map_tmul, map_one, hb, hb',
      TensorProduct.tmul_zero, smul_zero, Finset.sum_const_zero, add_zero] at this
    simpa [Algebra.TensorProduct.basis_apply] using this
  have hzero : ∀ i, e.repr x (Sum.inl i) = 0 := by
    intro i
    have := (Algebra.TensorProduct.basis S b').linearIndependent
    exact Fintype.linearIndependent_iff.mp this _ himg i
  conv_lhs => rw [← hsum]
  simp only [hzero, zero_smul, Finset.sum_const_zero, zero_add]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [e, coords, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem coords_radicalPart (c : Fin d → S) : coords b (radicalPart b c) = c := by
  funext j
  simp only [coords, radicalPart, map_sum, Algebra.TensorProduct.basis_repr_tmul]
  simp [Module.Basis.repr_self, Finsupp.single_apply]

end Coordinates

section CoordinateAlgebra

variable {S : Type u} [CommRing S] [Algebra R S]

theorem coords_add (x y : S ⊗[R] A) : coords b (x + y) = coords b x + coords b y := by
  funext j
  simp [coords]

theorem coords_sub (x y : S ⊗[R] A) : coords b (x - y) = coords b x - coords b y := by
  funext j
  simp [coords]

theorem coords_tmul (s : S) (x : A) (m : Fin d) :
    coords b (s ⊗ₜ[R] x) m = s * algebraMap R S (b.repr x (Sum.inr m)) := by
  simp [coords, Algebra.TensorProduct.basis_repr_tmul, Finsupp.mapRange_apply]

theorem coords_sum {κ : Type*} (t : Finset κ) (f : κ → S ⊗[R] A) :
    coords b (∑ i ∈ t, f i) = ∑ i ∈ t, coords b (f i) := by
  funext j
  simp [coords, Finset.sum_apply]

theorem radicalPart_mul_radicalPart (c c' : Fin d → S) :
    radicalPart b c * radicalPart b c' =
      ∑ a, ∑ a', (c a * c' a') ⊗ₜ[R] (b (Sum.inr a) * b (Sum.inr a')) := by
  simp only [radicalPart, Finset.sum_mul, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul]
  rw [Finset.sum_comm]

theorem coords_mul_radicalPart (c c' : Fin d → S) (m : Fin d) :
    coords b (radicalPart b c * radicalPart b c') m =
      ∑ a, ∑ a', c a * c' a' *
        algebraMap R S (b.repr (b (Sum.inr a) * b (Sum.inr a')) (Sum.inr m)) := by
  rw [radicalPart_mul_radicalPart, coords_sum]
  simp only [Finset.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [coords_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [coords_tmul]

end CoordinateAlgebra
/-! ### Nilpotency of the radical from adapted weights -/

section Nilpotency

variable (b' : Module.Basis (Fin N) R B) (w : Fin d → ℕ)

/-- `x` is a radical part whose coefficients vanish below weight `n`. -/
def RadicalOfWeight {S : Type u} [CommRing S] [Algebra R S] (n : ℕ) (x : S ⊗[R] A) : Prop :=
  ∃ c : Fin d → S, (∀ m, c m ≠ 0 → n ≤ w m) ∧ x = radicalPart b c

theorem radicalOfWeight_mul_radicalPart (hb' : ∀ i, π (b (Sum.inl i)) = b' i)
    (hb : ∀ j, π (b (Sum.inr j)) = 0)
    (hw : ∀ a a' m, b.repr (b (Sum.inr a) * b (Sum.inr a')) (Sum.inr m) ≠ 0 → w a + w a' ≤ w m)
    {S : Type u} [CommRing S] [Algebra R S] {n : ℕ} {x : S ⊗[R] A}
    (hx : RadicalOfWeight b w n x) (c' : Fin d → S) (hc' : ∀ j, c' j ≠ 0 → 1 ≤ w j) :
    RadicalOfWeight b w (n + 1) (x * radicalPart b c') := by
  obtain ⟨c, hc, rfl⟩ := hx
  have h0 : Algebra.TensorProduct.map (AlgHom.id R S) π (radicalPart b c * radicalPart b c') = 0 := by
    rw [map_mul, map_radicalPart π b hb, zero_mul]
  refine ⟨coords b (radicalPart b c * radicalPart b c'), fun m hm => ?_,
    eq_radicalPart_of_map_eq_zero π b b' hb' hb _ h0⟩
  rw [coords_mul_radicalPart] at hm
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  obtain ⟨a', -, ha'⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
  have h1 : c a ≠ 0 := fun h => ha' (by rw [h, zero_mul, zero_mul])
  have h2 : c' a' ≠ 0 := fun h => ha' (by rw [h, mul_zero, zero_mul])
  have h3 : b.repr (b (Sum.inr a) * b (Sum.inr a')) (Sum.inr m) ≠ 0 := fun h =>
    ha' (by rw [h, map_zero, mul_zero])
  have := hc a h1
  have := hc' a' h2
  have := hw a a' m h3
  omega

/-- If the kernel basis carries positive weights compatible with its products, the universal
radical element is nilpotent. -/
theorem isNilpotent_universalRadical_of_weights (hb' : ∀ i, π (b (Sum.inl i)) = b' i)
    (hb : ∀ j, π (b (Sum.inr j)) = 0) (hw1 : ∀ j, 1 ≤ w j)
    (hw : ∀ a a' m, b.repr (b (Sum.inr a) * b (Sum.inr a')) (Sum.inr m) ≠ 0 → w a + w a' ≤ w m) :
    IsNilpotent (universalRadical b) := by
  have hpow : ∀ n : ℕ, RadicalOfWeight b w (n + 1) (universalRadical b ^ (n + 1)) := by
    intro n
    induction n with
    | zero =>
      rw [zero_add, pow_one]
      exact ⟨_, fun m _ => hw1 m, rfl⟩
    | succ n ih =>
      rw [pow_succ]
      exact radicalOfWeight_mul_radicalPart π b b' w hb' hb hw ih _ fun j _ => hw1 j
  refine ⟨∑ m, w m + 1, ?_⟩
  obtain ⟨c, hc, hx⟩ := hpow (∑ m, w m)
  rw [hx]
  have hc0 : c = 0 := by
    funext m
    by_contra h
    have h1 := hc m h
    have h2 : w m ≤ ∑ m', w m' := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)
    omega
  simp [hc0, radicalPart]

end Nilpotency


/-! ### Total weights of polynomials with polynomial coefficients

A general-weight version of the `Pos N`-specific `TotalWeightLE` of
`Langlands.GroupScheme.UnitriangularUnipotent.WeightCore`. -/

section TotalWeight

open MvPolynomial

variable {σ : Type*} (w : σ → ℕ) {R' : Type*} [CommRing R']

/-- Every outer monomial `d` times inner monomial `e` occurring in `F` has total weight `≤ s`. -/
def TotalWeightLE (F : MvPolynomial σ (MvPolynomial σ R')) (s : ℕ) : Prop :=
  ∀ d e, (F.coeff d).coeff e ≠ 0 → Finsupp.weight w d + Finsupp.weight w e ≤ s

namespace TotalWeightLE

variable {w} {F G : MvPolynomial σ (MvPolynomial σ R')} {s t : ℕ}

theorem zero (s : ℕ) : TotalWeightLE w (0 : MvPolynomial σ (MvPolynomial σ R')) s := by
  intro d e h
  simp at h

theorem mono (hF : TotalWeightLE w F s) (hst : s ≤ t) : TotalWeightLE w F t :=
  fun d e h => (hF d e h).trans hst

theorem add (hF : TotalWeightLE w F s) (hG : TotalWeightLE w G s) :
    TotalWeightLE w (F + G) s := by
  intro d e h
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply] at h
  by_cases hf : (F.coeff d).coeff e = 0
  · rw [hf, zero_add] at h
    exact hG d e h
  · exact hF d e hf

theorem sum {κ : Type*} (I : Finset κ) {F : κ → MvPolynomial σ (MvPolynomial σ R')}
    (hF : ∀ i ∈ I, TotalWeightLE w (F i) s) : TotalWeightLE w (∑ i ∈ I, F i) s := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using zero s
  | insert a I ha ih =>
    rw [Finset.sum_insert ha]
    exact (hF a (Finset.mem_insert_self a I)).add
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

theorem mul (hF : TotalWeightLE w F s) (hG : TotalWeightLE w G t) :
    TotalWeightLE w (F * G) (s + t) := by
  classical
  intro d e h
  rw [coeff_mul, coeff_sum] at h
  obtain ⟨x, hx, hx0⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [coeff_mul] at hx0
  obtain ⟨y, hy, hy0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx0
  have h1 := hF x.1 y.1 (left_ne_zero_of_mul hy0)
  have h2 := hG x.2 y.2 (right_ne_zero_of_mul hy0)
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx hy
  rw [← hx, ← hy, map_add, map_add]
  omega

theorem C_of {φ : MvPolynomial σ R'}
    (hφ : ∀ e, φ.coeff e ≠ 0 → Finsupp.weight w e ≤ s) :
    TotalWeightLE w (C φ : MvPolynomial σ (MvPolynomial σ R')) s := by
  classical
  intro d e h
  rw [coeff_C] at h
  split_ifs at h with hd
  · subst hd
    simpa using hφ e h
  · simp at h

theorem one : TotalWeightLE w (1 : MvPolynomial σ (MvPolynomial σ R')) 0 := by
  classical
  refine C_of fun e he => ?_
  rw [coeff_one] at he
  split_ifs at he with h
  · subst h; simp
  · exact absurd rfl he

theorem pow (hF : TotalWeightLE w F s) (n : ℕ) : TotalWeightLE w (F ^ n) (n * s) := by
  induction n with
  | zero => simpa using one
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact ih.mul hF

theorem prod {κ : Type*} (I : Finset κ) {F : κ → MvPolynomial σ (MvPolynomial σ R')}
    {t : κ → ℕ} (hF : ∀ i ∈ I, TotalWeightLE w (F i) (t i)) :
    TotalWeightLE w (∏ i ∈ I, F i) (∑ i ∈ I, t i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using one
  | insert a I ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (hF a (Finset.mem_insert_self a I)).mul
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

theorem X_var (q : σ) :
    TotalWeightLE w (X q : MvPolynomial σ (MvPolynomial σ R')) (w q) := by
  classical
  intro d e h
  rw [coeff_X] at h
  split_ifs at h with hd
  · subst hd
    rw [coeff_one] at h
    split_ifs at h with he
    · subst he; simp [Finsupp.weight_single]
    · exact absurd rfl h
  · simp at h

theorem C_X (q : σ) :
    TotalWeightLE w (C (X q) : MvPolynomial σ (MvPolynomial σ R')) (w q) := by
  classical
  refine C_of fun e he => ?_
  rw [coeff_X] at he
  split_ifs at he with h
  · subst h; simp [Finsupp.weight_single]
  · exact absurd rfl he

theorem C_C (r : R') : TotalWeightLE w (C (C r) : MvPolynomial σ (MvPolynomial σ R')) 0 := by
  classical
  refine C_of fun e he => ?_
  rw [coeff_C] at he
  split_ifs at he with h
  · subst h; simp
  · exact absurd rfl he

end TotalWeightLE

end TotalWeight

/-! ### The polynomial form of the comultiplication -/

section ComulPoly

open MvPolynomial

variable (c : Fin d → Fin d → Fin d → R)

/-- The comultiplication in polynomial form: inner variables `C (X q)` are the left tensor
factor, outer variables `X q` the right one; `X m ↦ C (X m) + X m + Σ c a a' m C (X a) X a'`. -/
def comulPolyJ : MvPolynomial (Fin d) R →ₐ[R] MvPolynomial (Fin d) (MvPolynomial (Fin d) R) :=
  aeval fun m => C (X m) + X m + ∑ a, ∑ a', C (C (c a a' m)) * C (X a) * X a'

theorem comulPolyJ_X (m : Fin d) :
    comulPolyJ c (X m) = C (X m) + X m + ∑ a, ∑ a', C (C (c a a' m)) * C (X a) * X a' := by
  simp [comulPolyJ]

variable (w : Fin d → ℕ)

theorem totalWeightLE_comulPolyJ_X (hw : ∀ a a' m, c a a' m ≠ 0 → w a + w a' ≤ w m) (m : Fin d) :
    TotalWeightLE w (comulPolyJ c (X m)) (w m) := by
  rw [comulPolyJ_X]
  refine ((TotalWeightLE.C_X m).add (TotalWeightLE.X_var m)).add ?_
  refine TotalWeightLE.sum _ fun a _ => TotalWeightLE.sum _ fun a' _ => ?_
  by_cases hc : c a a' m = 0
  · rw [hc, C_0, C_0, zero_mul, zero_mul]
    exact TotalWeightLE.zero _
  · refine (((TotalWeightLE.C_C (c a a' m)).mul (TotalWeightLE.C_X a)).mul
      (TotalWeightLE.X_var a')).mono ?_
    have := hw a a' m hc
    omega

theorem totalWeightLE_comulPolyJ_monomial (hw : ∀ a a' m, c a a' m ≠ 0 → w a + w a' ≤ w m)
    (e : Fin d →₀ ℕ) (r : R) :
    TotalWeightLE w (comulPolyJ c (monomial e r)) (Finsupp.weight w e) := by
  rw [monomial_eq, map_mul, Finsupp.prod, map_prod, ← zero_add (Finsupp.weight w e)]
  refine TotalWeightLE.mul ?_ ?_
  · rw [comulPolyJ, aeval_C, MvPolynomial.algebraMap_apply, algebraMap_eq]
    refine TotalWeightLE.C_of fun e' he => ?_
    rw [coeff_C] at he
    split_ifs at he with h
    · subst h; simp
    · exact absurd rfl he
  · rw [Finsupp.weight_apply, Finsupp.sum]
    refine TotalWeightLE.prod _ fun q _ => ?_
    rw [map_pow, smul_eq_mul]
    exact (totalWeightLE_comulPolyJ_X c w hw q).pow (e q)

theorem totalWeightLE_comulPolyJ (hw : ∀ a a' m, c a a' m ≠ 0 → w a + w a' ≤ w m)
    (f : MvPolynomial (Fin d) R) (s : ℕ) (hf : ∀ a ∈ f.support, Finsupp.weight w a ≤ s) :
    TotalWeightLE w (comulPolyJ c f) s := by
  rw [f.as_sum, map_sum]
  exact TotalWeightLE.sum _ fun a ha =>
    (totalWeightLE_comulPolyJ_monomial c w hw a _).mono (hf a ha)

/-- Setting the inner variables to zero undoes the comultiplication. -/
theorem map_constantCoeff_comulPolyJ (f : MvPolynomial (Fin d) R) :
    MvPolynomial.map constantCoeff (comulPolyJ c f) = f := by
  have h : (MvPolynomial.map (constantCoeff (σ := Fin d) (R := R))).comp (comulPolyJ c).toRingHom =
      RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [comulPolyJ, MvPolynomial.algebraMap_apply]
    · intro m
      simp [comulPolyJ_X]
  exact RingHom.congr_fun h f

/-- The outer coefficient at `m` of the comultiplication of `f` is `f.coeff m` when no monomial of
`f` has weight larger than that of `m` and all weights are positive. -/
theorem coeff_comulPolyJ_of_weight_le (hw : ∀ a a' m, c a a' m ≠ 0 → w a + w a' ≤ w m)
    (hw1 : ∀ j, 1 ≤ w j) (f : MvPolynomial (Fin d) R) (m : Fin d →₀ ℕ)
    (hm : ∀ a ∈ f.support, Finsupp.weight w a ≤ Finsupp.weight w m) :
    (comulPolyJ c f).coeff m = C (f.coeff m) := by
  classical
  have hF := totalWeightLE_comulPolyJ c w hw f _ hm
  ext e
  rw [coeff_C]
  split_ifs with he
  · subst he
    have h := congrArg (fun F => F.coeff m) (map_constantCoeff_comulPolyJ c f)
    rwa [coeff_map, constantCoeff_eq] at h
  · by_contra h
    have hle := hF m e h
    obtain ⟨q, hq⟩ : ∃ q, e q ≠ 0 := by
      by_contra! H
      exact he (Finsupp.ext fun q => (H q).symm)
    have h1 := Finsupp.le_weight_of_ne_zero' w hq
    have h2 := hw1 q
    omega

end ComulPoly

section Points

variable {S : Type u} [CommRing S] [Algebra R S]

variable (S) in
/-- The kernel of the unit map of `id ⊗ π`, as a subgroup of `(S ⊗[R] A)ˣ`. -/
abbrev kerSubgroup : Subgroup (S ⊗[R] A)ˣ :=
  (Units.map (Algebra.TensorProduct.map (AlgHom.id R S) π).toMonoidHom).ker

theorem mem_kerSubgroup (u : (S ⊗[R] A)ˣ) :
    u ∈ kerSubgroup π S ↔ Algebra.TensorProduct.map (AlgHom.id R S) π (u : S ⊗[R] A) = 1 := by
  rw [MonoidHom.mem_ker, Units.ext_iff]
  simp

variable (hnil : IsNilpotent (universalRadical b)) (hb : ∀ j, π (b (Sum.inr j)) = 0)

/-- The point `1 + Σ c_j ⊗ e_j` of the kernel. -/
def pointOf (c : Fin d → S) : kerSubgroup π S :=
  ⟨(isNilpotent_radicalPart b hnil c).isUnit_one_add.unit, by
    rw [mem_kerSubgroup]
    simp [map_radicalPart π b hb c]⟩

theorem pointOf_val (c : Fin d → S) :
    ((pointOf π b hnil hb c : (S ⊗[R] A)ˣ) : S ⊗[R] A) = 1 + radicalPart b c := rfl

/-- The kernel coordinates of a point of the kernel. -/
def coordsOf (u : kerSubgroup π S) : Fin d → S :=
  coords b (((u : (S ⊗[R] A)ˣ) : S ⊗[R] A) - 1)

variable (b' : Module.Basis (Fin N) R B) (hb' : ∀ i, π (b (Sum.inl i)) = b' i)

include hb' in
theorem pointOf_coordsOf (u : kerSubgroup π S) : pointOf π b hnil hb (coordsOf π b u) = u := by
  apply Subtype.ext
  apply Units.ext
  rw [pointOf_val, coordsOf]
  have hu := (mem_kerSubgroup π (u : (S ⊗[R] A)ˣ)).mp u.2
  have h0 : Algebra.TensorProduct.map (AlgHom.id R S) π
      (((u : (S ⊗[R] A)ˣ) : S ⊗[R] A) - 1) = 0 := by
    rw [map_sub, hu, map_one, sub_self]
  rw [← eq_radicalPart_of_map_eq_zero π b b' hb' hb _ h0]
  abel

theorem coordsOf_pointOf (c : Fin d → S) : coordsOf π b (pointOf π b hnil hb c) = c := by
  rw [coordsOf, pointOf_val, add_sub_cancel_left, coords_radicalPart]

/-- The group law in kernel coordinates. -/
theorem coordsOf_pointOf_mul (c c' : Fin d → S) (m : Fin d) :
    coordsOf π b (pointOf π b hnil hb c * pointOf π b hnil hb c') m =
      c m + c' m + ∑ a, ∑ a', c a * c' a' *
        algebraMap R S (b.repr (b (Sum.inr a) * b (Sum.inr a')) (Sum.inr m)) := by
  have hval : (((pointOf π b hnil hb c * pointOf π b hnil hb c' : kerSubgroup π S) :
      (S ⊗[R] A)ˣ) : S ⊗[R] A) - 1 =
        radicalPart b c + radicalPart b c' + radicalPart b c * radicalPart b c' := by
    change (1 + radicalPart b c) * (1 + radicalPart b c') - 1 = _
    noncomm_ring
  rw [coordsOf, hval, coords_add, coords_add, coords_radicalPart, coords_radicalPart]
  simp only [Pi.add_apply, coords_mul_radicalPart]

end Points

section Functor

variable {S S' : Type u} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']

theorem map_comm (f : S →ₐ[R] S') (x : S ⊗[R] A) :
    Algebra.TensorProduct.map (AlgHom.id R S') π (Algebra.TensorProduct.map f (AlgHom.id R A) x) =
      Algebra.TensorProduct.map f (AlgHom.id R B)
        (Algebra.TensorProduct.map (AlgHom.id R S) π x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s a => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Changing the coefficients along `f` maps kernels to kernels. -/
def kerMap (f : S →ₐ[R] S') : kerSubgroup π S →* kerSubgroup π S' :=
  ((Units.map (Algebra.TensorProduct.map f (AlgHom.id R A)).toMonoidHom).comp
    (kerSubgroup π S).subtype).codRestrict _ fun u => by
      rw [mem_kerSubgroup]
      have hu := (mem_kerSubgroup π (u : (S ⊗[R] A)ˣ)).mp u.2
      change Algebra.TensorProduct.map (AlgHom.id R S') π
        (Algebra.TensorProduct.map f (AlgHom.id R A) ((u : (S ⊗[R] A)ˣ) : S ⊗[R] A)) = 1
      rw [map_comm, hu, map_one]

theorem kerMap_val (f : S →ₐ[R] S') (u : kerSubgroup π S) :
    ((kerMap π f u : (S' ⊗[R] A)ˣ) : S' ⊗[R] A) =
      Algebra.TensorProduct.map f (AlgHom.id R A) ((u : (S ⊗[R] A)ˣ) : S ⊗[R] A) := rfl

theorem kerMap_pointOf (hnil : IsNilpotent (universalRadical b)) (hb : ∀ j, π (b (Sum.inr j)) = 0)
    (f : S →ₐ[R] S') (c : Fin d → S) :
    kerMap π f (pointOf π b hnil hb c) = pointOf π b hnil hb (fun j => f (c j)) := by
  apply Subtype.ext
  apply Units.ext
  rw [kerMap_val, pointOf_val, pointOf_val, map_add, map_one]
  simp [radicalPart, map_sum]

end Functor

end Langlands.GroupScheme.FiniteFreeAlgebraUnits.UnipotentPart

namespace Langlands.GroupScheme.FiniteFreeAlgebraUnits.UnipotentPart

variable {R : CommRingCat.{u}} {A : Type u} [Ring A] [Algebra R A]
  {B : Type u} [Ring B] [Algebra R B] (π : A →ₐ[R] B)
  {N d : ℕ} (b : Module.Basis (Fin N ⊕ Fin d) R A)

variable (A) in
/-- The kernel functor `S ↦ ker((S ⊗ A)ˣ → (S ⊗ B)ˣ)`. -/
def functor : CommAlgCat.{u} R ⥤ GrpCat.{u} where
  obj S := GrpCat.of (kerSubgroup π S)
  map f := GrpCat.ofHom (kerMap π f.hom)
  map_id S := by
    ext x
    change Algebra.TensorProduct.map (AlgHom.id R S) (AlgHom.id R A) _ = _
    rw [Algebra.TensorProduct.map_id]
    rfl
  map_comp f g := by
    ext x
    change Algebra.TensorProduct.map (g.hom.comp f.hom) (AlgHom.id R A) _ =
      Algebra.TensorProduct.map g.hom (AlgHom.id R A) (Algebra.TensorProduct.map f.hom (AlgHom.id R A) _)
    exact AlgHom.congr_fun
      (Algebra.TensorProduct.map_comp g.hom f.hom (AlgHom.id R A) (AlgHom.id R A)) _

variable (hnil : IsNilpotent (universalRadical b)) (hb : ∀ j, π (b (Sum.inr j)) = 0)
  (b' : Module.Basis (Fin N) R B) (hb' : ∀ i, π (b (Sum.inl i)) = b' i)

/-- Polynomial coordinates on the kernel points. -/
abbrev coordinateAlgebra : CommAlgCat.{u} R := CommAlgCat.of R (MvPolynomial (Fin d) R)

/-- The polynomial ring in the kernel coordinates corepresents the kernel functor. -/
def corepresentableBy :
    (functor A π ⋙ forget GrpCat).CorepresentableBy (coordinateAlgebra (R := R) (d := d)) where
  homEquiv :=
    { toFun := fun φ => pointOf π b hnil hb (fun j => φ.hom (MvPolynomial.X j))
      invFun := fun u => CommAlgCat.ofHom (MvPolynomial.aeval (coordsOf π b u))
      left_inv := fun φ => by
        apply CommAlgCat.hom_ext
        apply MvPolynomial.algHom_ext
        intro j
        simp [coordsOf_pointOf]
      right_inv := fun u => by
        change pointOf π b hnil hb (fun j => MvPolynomial.aeval (coordsOf π b u) (MvPolynomial.X j)) = u
        simp only [MvPolynomial.aeval_X]
        exact pointOf_coordsOf π b hnil hb b' hb' u }
  homEquiv_comp f φ := by
    change pointOf π b hnil hb (fun j => f.hom (φ.hom (MvPolynomial.X j))) =
      kerMap π f.hom (pointOf π b hnil hb (fun j => φ.hom (MvPolynomial.X j)))
    rw [kerMap_pointOf]

/-- The unipotent kernel as an affine group scheme over `Spec R`. -/
abbrev groupScheme : GroupScheme (Spec R) :=
  Corepresented.groupScheme (functor A π) (corepresentableBy π b hnil hb b' hb')

theorem groupScheme_hom :
    (groupScheme π b hnil hb b' hb').X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin d) R))) :=
  rfl

instance groupScheme_isAffineHom : IsAffineHom (groupScheme π b hnil hb b' hb').X.hom := by
  change IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin d) R))))
  infer_instance

theorem smooth : Smooth (groupScheme π b hnil hb b' hb').X.hom := by
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin d) R))))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  change (algebraMap R (MvPolynomial (Fin d) R)).Smooth
  rw [RingHom.smooth_algebraMap]
  infer_instance

/-- The kernel is an affine space over the base: its fibres are geometrically irreducible. -/
theorem geometricallyIrreducible :
    GeometricallyIrreducible (groupScheme π b hnil hb b' hb').X.hom :=
  geometricallyIrreducible_spec_coordinateRing (R := R) d

theorem geometricallyConnected :
    GeometricallyConnected (groupScheme π b hnil hb b' hb').X.hom :=
  have := geometricallyIrreducible π b hnil hb b' hb'
  GeometricallyIrreducible.geometricallyConnectedFLT _

/-! ### The coordinate comultiplication -/

open Algebra.TensorProduct (includeLeft includeRight) in
/-- The comultiplication of the kernel coordinates is `X m ↦ X m ⊗ 1 + 1 ⊗ X m + Σ c^m_{a a'} X a ⊗ X a'`,
with `c^m_{a a'}` the `m`-th kernel coordinate of `e_a * e_{a'}`. -/
theorem comul_X (m : Fin d) :
    AffineLinearEmbedding.comul (corepresentableBy π b hnil hb b' hb') (MvPolynomial.X m) =
      MvPolynomial.X m ⊗ₜ[R] (1 : MvPolynomial (Fin d) R) +
        (1 : MvPolynomial (Fin d) R) ⊗ₜ[R] MvPolynomial.X m +
        ∑ a, ∑ a', b.repr (b (Sum.inr a) * b (Sum.inr a')) (Sum.inr m) •
          (MvPolynomial.X a ⊗ₜ[R] MvPolynomial.X a') := by
  have h := congrArg (fun u => coordsOf π b u m)
    (AffineLinearEmbedding.pt_comul (corepresentableBy π b hnil hb b' hb'))
  change coordsOf π b (pointOf π b hnil hb _) m =
    coordsOf π b (pointOf π b hnil hb _ * pointOf π b hnil hb _) m at h
  rw [coordsOf_pointOf] at h
  refine h.trans ((coordsOf_pointOf_mul π b hnil hb _ _ m).trans ?_)
  simp only [CommAlgCat.hom_ofHom, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.algebraMap_apply]
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
  rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
    mul_one, TensorProduct.smul_tmul', Algebra.smul_def, mul_comm]

/-! ### Comparison with the actual kernel of the unit-group map -/

section Kernel

/-- The basis of `A` reindexed by `Fin (N + d)`, as used by the unit group scheme. -/
abbrev flatBasis : Module.Basis (Fin (N + d)) R A := b.reindex finSumFinEquiv

/-- Points of `Spec R`-schemes of the unipotent kernel, as points of the corepresented group. -/
def unipotentPointsEquiv (T : Over (Spec R)) :
    (T ⟶ (groupScheme π b hnil hb b' hb').X) ≃* kerSubgroup π ((algΓ R).obj T).unop :=
  Corepresented.pointsEquiv (functor A π) (corepresentableBy π b hnil hb b' hb') T

theorem unipotentPointsEquiv_naturality {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ (groupScheme π b hnil hb b' hb').X) :
    unipotentPointsEquiv π b hnil hb b' hb' T' (a ≫ x) =
      kerMap π ((algΓ R).map a).unop.hom (unipotentPointsEquiv π b hnil hb b' hb' T x) :=
  Corepresented.pointsEquiv_naturality (functor A π) (corepresentableBy π b hnil hb b' hb') a x

/-- The unit-group map of `π`, between the unit group schemes of `A` and `B`. -/
abbrev unitMap : FiniteFreeAlgebraUnits.groupScheme (flatBasis b) ⟶
    FiniteFreeAlgebraUnits.groupScheme b' :=
  FiniteFreeAlgebraUnits.map (flatBasis b) b' π

theorem comp_unitMap_eq_one_iff (T : Over (Spec R))
    (x : T ⟶ (FiniteFreeAlgebraUnits.groupScheme (flatBasis b)).X) :
    x ≫ (unitMap π b b').hom.hom = 1 ↔
      FiniteFreeAlgebraUnits.pointsEquiv (flatBasis b) T x ∈ kerSubgroup π ((algΓ R).obj T).unop := by
  rw [MonoidHom.mem_ker, ← (FiniteFreeAlgebraUnits.pointsEquiv b' T).injective.eq_iff, map_one,
    FiniteFreeAlgebraUnits.pointsEquiv_map]

/-- Points of the actual kernel, as kernel elements of `(Γ(T) ⊗ A)ˣ`. -/
def actualKernelPointsEquiv (T : Over (Spec R)) :
    (T ⟶ (kernel (unitMap π b b')).X) ≃* kerSubgroup π ((algΓ R).obj T).unop where
  toFun x := ⟨FiniteFreeAlgebraUnits.pointsEquiv (flatBasis b) T
      (x ≫ (kernelι (unitMap π b b')).hom.hom), by
    rw [← comp_unitMap_eq_one_iff]
    exact (Langlands.GroupScheme.kernelPointsEquiv (unitMap π b b') T x).property⟩
  invFun y := (Langlands.GroupScheme.kernelPointsEquiv (unitMap π b b') T).symm
    ⟨(FiniteFreeAlgebraUnits.pointsEquiv (flatBasis b) T).symm y,
      (comp_unitMap_eq_one_iff π b b' T _).mpr (by rw [MulEquiv.apply_symm_apply]; exact y.2)⟩
  left_inv x := by
    apply (Langlands.GroupScheme.kernelPointsEquiv (unitMap π b b') T).injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    simp only [MulEquiv.symm_apply_apply]
    rfl
  right_inv y := by
    apply Subtype.ext
    change FiniteFreeAlgebraUnits.pointsEquiv (flatBasis b) T
      ((Langlands.GroupScheme.kernelPointsEquiv (unitMap π b b') T
        ((Langlands.GroupScheme.kernelPointsEquiv (unitMap π b b') T).symm _)).val) = _
    rw [MulEquiv.apply_symm_apply]
    exact MulEquiv.apply_symm_apply _ _
  map_mul' x y := by
    apply Subtype.ext
    change FiniteFreeAlgebraUnits.pointsEquiv (flatBasis b) T
        ((x * y) ≫ (kernelι (unitMap π b b')).hom.hom) =
      FiniteFreeAlgebraUnits.pointsEquiv (flatBasis b) T (x ≫ (kernelι (unitMap π b b')).hom.hom) *
        FiniteFreeAlgebraUnits.pointsEquiv (flatBasis b) T (y ≫ (kernelι (unitMap π b b')).hom.hom)
    rw [MonObj.mul_comp, map_mul]

theorem actualKernelPointsEquiv_val (T : Over (Spec R)) (x : T ⟶ (kernel (unitMap π b b')).X) :
    ((actualKernelPointsEquiv π b b' T x : (((algΓ R).obj T).unop ⊗[R] A)ˣ)) =
      FiniteFreeAlgebraUnits.pointsEquiv (flatBasis b) T (x ≫ (kernelι (unitMap π b b')).hom.hom) :=
  rfl

theorem actualKernelPointsEquiv_naturality {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ (kernel (unitMap π b b')).X) :
    actualKernelPointsEquiv π b b' T' (a ≫ x) =
      kerMap π ((algΓ R).map a).unop.hom (actualKernelPointsEquiv π b b' T x) := by
  apply Subtype.ext
  rw [actualKernelPointsEquiv_val, Category.assoc, FiniteFreeAlgebraUnits.pointsEquiv_naturality]
  rfl

/-- The corepresented unipotent group is the actual kernel of the unit-group map of `π`. -/
def kernelIso : groupScheme π b hnil hb b' hb' ≅ kernel (unitMap π b b') :=
  isoOfPointModels (fun T : Over (Spec R) => kerSubgroup π ((algΓ R).obj T).unop)
    (fun a => kerMap π ((algΓ R).map a).unop.hom)
    (unipotentPointsEquiv π b hnil hb b' hb') (actualKernelPointsEquiv π b b')
    (fun a x => unipotentPointsEquiv_naturality π b hnil hb b' hb' a x)
    (fun a x => actualKernelPointsEquiv_naturality π b b' a x)

end Kernel

/-! ### Unipotence over a field -/

section Unipotence

open MvPolynomial AffineLinearEmbedding Unipotent

/-- The structure constants `c a a' m`: the `m`-th kernel coordinate of `e_a * e_{a'}`. -/
abbrev structureConst (a a' m : Fin d) : R :=
  b.repr (b (Sum.inr a) * b (Sum.inr a')) (Sum.inr m)

/-- The ring map `MvPolynomial (outer) (MvPolynomial inner) → B ⊗ B` sending inner variables to the
left and outer variables to the right tensor factor. -/
abbrev kappa : MvPolynomial (Fin d) (MvPolynomial (Fin d) R) →+*
    MvPolynomial (Fin d) R ⊗[R] MvPolynomial (Fin d) R :=
  eval₂Hom (Algebra.TensorProduct.includeLeft : MvPolynomial (Fin d) R →ₐ[R]
      MvPolynomial (Fin d) R ⊗[R] MvPolynomial (Fin d) R).toRingHom
    (fun q => (1 : MvPolynomial (Fin d) R) ⊗ₜ[R] X q)

theorem comul_eq_kappa_comp :
    (comul (corepresentableBy π b hnil hb b' hb')).toRingHom =
      (kappa (R := R) (d := d)).comp (comulPolyJ (structureConst b)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [comulPolyJ, MvPolynomial.algebraMap_apply]
  · intro m
    change comul (corepresentableBy π b hnil hb b' hb') (X m) =
      kappa (comulPolyJ (structureConst b) (X m))
    rw [comul_X, comulPolyJ_X]
    simp [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.tmul_mul_tmul,
      TensorProduct.smul_tmul', MvPolynomial.smul_eq_C_mul]

end Unipotence

section FieldUnipotence

open MvPolynomial AffineLinearEmbedding Unipotent

variable {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra (CommRingCat.of k) A]
  {B : Type u} [Ring B] [Algebra (CommRingCat.of k) B] (π : A →ₐ[CommRingCat.of k] B)
  {N d : ℕ} (b : Module.Basis (Fin N ⊕ Fin d) (CommRingCat.of k) A)
  (hnil : IsNilpotent (universalRadical b)) (hb : ∀ j, π (b (Sum.inr j)) = 0)
  (b' : Module.Basis (Fin N) (CommRingCat.of k) B) (hb' : ∀ i, π (b (Sum.inl i)) = b' i)
  (w : Fin d → ℕ) (hw : ∀ a a' m, structureConst b a a' m ≠ 0 → w a + w a' ≤ w m)
  (hw1 : ∀ j, 1 ≤ w j)

include hw hw1 in
/-- With weights adapted to the products of the kernel basis, every nonzero finite-dimensional
right-translation stable subspace of the coordinate bialgebra contains `1`. -/
theorem oneMemStable :
    letI := bialgebra (corepresentableBy π b hnil hb b' hb')
    OneMemStable k (coordinateAlgebra (R := CommRingCat.of k) (d := d)) := by
  let e := corepresentableBy π b hnil hb b' hb'
  let Bc : Type u := coordinateAlgebra (R := CommRingCat.of k) (d := d)
  let inst : Bialgebra k Bc := bialgebra e
  let instC : Coalgebra k Bc := inst.toCoalgebra
  let θ : MvPolynomial (Fin d) k →ₐ[k] Bc := AlgHom.id k _
  let χ : Bc →ₐ[k] MvPolynomial (Fin d) k := AlgHom.id k _
  intro V _ hV hV0
  obtain ⟨f, hfV, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV0
  have hχ0 : χ f ≠ 0 := hf0
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (χ f).support (Finsupp.weight w)
    (support_nonempty.2 hχ0)
  let κ : MvPolynomial (Fin d) (MvPolynomial (Fin d) k) →+* Bc ⊗[k] Bc :=
    eval₂Hom ((Algebra.TensorProduct.includeLeft : Bc →ₐ[k] Bc ⊗[k] Bc).toRingHom.comp
      θ.toRingHom) (fun q => (1 : Bc) ⊗ₜ[k] θ (X q))
  have hκ : comul e f = κ (comulPolyJ (structureConst b) (χ f)) :=
    RingHom.congr_fun (comul_eq_kappa_comp π b hnil hb b' hb') f
  let φ : Module.Dual k Bc := (lcoeff k m).comp χ.toLinearMap
  have hφ : ∀ d', φ (θ (monomial d' 1)) = if d' = m then 1 else 0 := by
    intro d'
    simp only [φ, θ, χ, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
      AlgHom.id_apply, lcoeff_apply, coeff_monomial]
  have key : rightAct φ f = (χ f).coeff m • (1 : Bc) := by
    rw [rightAct_apply]
    change TensorProduct.rid k Bc (LinearMap.lTensor Bc φ (comul e f)) = _
    rw [hκ, UnitriangularUnipotent.rid_lTensor_eval₂Hom k θ φ m hφ,
      coeff_comulPolyJ_of_weight_le (structureConst b) w hw hw1 (χ f) m fun a ha => hmax a ha,
      algHom_C, Algebra.algebraMap_eq_smul_one]
  have hc : (χ f).coeff m ≠ 0 := mem_support_iff.1 hm
  have h1 : (1 : Bc) = ((χ f).coeff m)⁻¹ • rightAct φ f := by
    rw [key, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [h1]
  exact V.smul_mem _ (hV φ f hfV)

include hw hw1 in
/-- The unipotent kernel is a unipotent group scheme. -/
theorem isUnipotent : IsUnipotent (groupScheme π b hnil hb b' hb') :=
  Unipotent.isUnipotent_of_oneMemStable (corepresentableBy π b hnil hb b' hb')
    (oneMemStable π b hnil hb b' hb' w hw hw1)

/-- The unipotent kernel, as a subgroup of the unit group of `A`. -/
abbrev radicalInclusion :
    groupScheme π b hnil hb b' hb' ⟶ FiniteFreeAlgebraUnits.groupScheme (flatBasis b) :=
  (kernelIso π b hnil hb b' hb').hom ≫ kernelι (unitMap π b b')

theorem connectedSpace : ConnectedSpace (groupScheme π b hnil hb b' hb').X.left := by
  change ConnectedSpace (Spec (CommRingCat.of (MvPolynomial (Fin d) (CommRingCat.of k))))
  infer_instance

include hw hw1 in
/-- If the unit group of `B` is a torus and `π` has an algebra section, the unipotent kernel is
the unipotent radical of the unit group of `A`, and the unit-group map of `π` is the fppf
quotient by it. -/
theorem isUnipotentRadical (s : B →ₐ[CommRingCat.of k] A) (hs : π.comp s = AlgHom.id _ B)
    (hD : IsTorus (FiniteFreeAlgebraUnits.groupScheme b')) :
    IsUnipotentRadical (radicalInclusion π b hnil hb b' hb') ∧
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (radicalInclusion π b hnil hb b' hb'))
        (unitMap π b b') := by
  have := FiniteFreeAlgebraUnits.groupScheme_isAffineHom (flatBasis b)
  have := FiniteFreeAlgebraUnits.groupScheme_isAffineHom b'
  have hrange : SubgroupFunctor.range (radicalInclusion π b hnil hb b' hb') =
      SubgroupFunctor.range (kernelι (unitMap π b b')) :=
    SubgroupFunctor.range_iso_comp _ _
  have hq : RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range (radicalInclusion π b hnil hb b' hb')) (unitMap π b b') := by
    rw [hrange]
    exact FiniteFreeAlgebraUnits.isFppfQuotient_map_of_section (flatBasis b) b' π s hs
  refine ⟨IsUnipotentRadical.of_torus_quotient ?_ (smooth π b hnil hb b' hb')
    (connectedSpace π b hnil hb b' hb') (isUnipotent π b hnil hb b' hb' w hw hw1)
    (unitMap π b b') hq hD, hq⟩
  have : IsSeparated (FiniteFreeAlgebraUnits.groupScheme b').X.hom := inferInstance
  have hiso : IsIso (kernelIso π b hnil hb b' hb').hom.hom.hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map ((Grp.forget _).map
      (kernelIso π b hnil hb b' hb').hom)))
  change IsClosedImmersion ((kernelIso π b hnil hb b' hb').hom.hom.hom.left ≫
    (kernelι (unitMap π b b')).hom.hom.left)
  infer_instance

end FieldUnipotence

end Langlands.GroupScheme.FiniteFreeAlgebraUnits.UnipotentPart

/-! ### Units of `R^N` form the split torus -/

namespace Langlands.GroupScheme.FiniteFreeAlgebraUnits

section PiUnits

variable (R : CommRingCat.{u}) (N : ℕ)

/-- `S ⊗[R] R^N ≃ S^N`. -/
def tensorPiEquiv (S : Type u) [CommRing S] [Algebra R S] :
    S ⊗[R] (Fin N → R) ≃ₐ[R] (Fin N → S) :=
  (Algebra.TensorProduct.piRight R R S (fun _ : Fin N => (R : Type u))).trans
    (AlgEquiv.piCongrRight fun _ => Algebra.TensorProduct.rid R R S)

theorem tensorPiEquiv_tmul {S : Type u} [CommRing S] [Algebra R S] (s : S) (v : Fin N → R) :
    tensorPiEquiv R N S (s ⊗ₜ v) = fun i => v i • s := by
  funext i
  simp [tensorPiEquiv]

theorem tensorPiEquiv_natural {S S' : Type u} [CommRing S] [Algebra R S] [CommRing S']
    [Algebra R S'] (f : S →ₐ[R] S') (x : S ⊗[R] (Fin N → R)) :
    tensorPiEquiv R N S' (Algebra.TensorProduct.map f (AlgHom.id R (Fin N → R)) x) =
      fun i => f (tensorPiEquiv R N S x i) := by
  induction x using TensorProduct.inductionOn with
  | tmul s v =>
    funext i
    simp [tensorPiEquiv_tmul]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add]
    funext i
    simp

/-- Points of the units of `R^N` are families of global units. -/
def piUnitsPointsEquiv (T : Over (Spec R)) :
    (T ⟶ (groupScheme (Pi.basisFun R (Fin N))).X) ≃* (ULift.{u} (Fin N) → (Γ(T.left, ⊤))ˣ) :=
  ((pointsEquiv (Pi.basisFun R (Fin N)) T).trans
    ((Units.mapEquiv (tensorPiEquiv R N ((algΓ R).obj T).unop).toMulEquiv).trans
      MulEquiv.piUnits)).trans
    (MulEquiv.arrowCongr Equiv.ulift.symm (MulEquiv.refl _))

theorem piUnitsPointsEquiv_apply (T : Over (Spec R))
    (x : T ⟶ (groupScheme (Pi.basisFun R (Fin N))).X) (i : ULift.{u} (Fin N)) :
    (piUnitsPointsEquiv R N T x i : Γ(T.left, ⊤)) =
      tensorPiEquiv R N ((algΓ R).obj T).unop (pointsEquiv (Pi.basisFun R (Fin N)) T x) i.down :=
  rfl

theorem piUnitsPointsEquiv_naturality {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ (groupScheme (Pi.basisFun R (Fin N))).X) :
    piUnitsPointsEquiv R N T' (a ≫ x) =
      splitTorus.unitsRestrict (ULift.{u} (Fin N)) a (piUnitsPointsEquiv R N T x) := by
  funext i
  apply Units.ext
  rw [piUnitsPointsEquiv_apply, pointsEquiv_naturality, Units.coe_map]
  erw [tensorPiEquiv_natural]
  rfl

/-- The unit group scheme of `R^N` is the split torus on `N` (lifted) indices. -/
def piUnitsIso :
    groupScheme (Pi.basisFun R (Fin N)) ≅ splitTorus (Spec R) (ULift.{u} (Fin N)) :=
  isoOfPointModels (fun T : Over (Spec R) => ULift.{u} (Fin N) → (Γ(T.left, ⊤))ˣ)
    (fun a => splitTorus.unitsRestrict (ULift.{u} (Fin N)) a) (piUnitsPointsEquiv R N)
    (splitTorus.pointsEquiv (ULift.{u} (Fin N)))
    (fun a x => piUnitsPointsEquiv_naturality R N a x)
    (fun a y => splitTorus.pointsEquiv_naturality (ULift.{u} (Fin N)) a y)

/-- The unit group scheme of `R^N` is a split torus. -/
theorem isSplitTorus_pi : IsSplitTorus (groupScheme (Pi.basisFun R (Fin N))) :=
  IsSplitTorus.of_iso (piUnitsIso R N) (isSplitTorus_splitTorus _)

/-- Over a field, the unit group scheme of `k^N` is a torus. -/
theorem isTorus_pi (k : Type u) [Field k] :
    IsTorus (groupScheme (Pi.basisFun (CommRingCat.of k) (Fin N))) :=
  (isSplitTorus_pi (CommRingCat.of k) N).isTorus

end PiUnits

end Langlands.GroupScheme.FiniteFreeAlgebraUnits
