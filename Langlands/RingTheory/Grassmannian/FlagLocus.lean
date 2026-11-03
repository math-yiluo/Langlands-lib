import Langlands.RingTheory.Grassmannian.BaseChangeMembership
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-! # The full-flag locus of a quotient Grassmannian

Fix `n`. The ambient module is `Idx n → R`, a direct sum of copies of `R^n` indexed by
`Copy n = Σ j : Fin (n + 1), Fin ((n + 1) ^ j)`: level `j` carries `(n + 1) ^ j` copies. On the
quotient Grassmannian `G(rank n, A ⊗[R] (Idx n → R); A)`, with
`rank n = ∑ j, (n + 1) ^ j * (n - j)`:

* `GL_n(A)` acts by applying the matrix in every copy (`smul`), naturally in `A`;
* `Stable P` asks that `P` be preserved by the maps copying block `b` into block `a` whenever
  the level of `b` is at most the level of `a`; this condition is preserved by the action and is
  cut out by an ideal (`exists_ideal_stable_map_iff`);
* over a field, a stable point is a product of subspaces of `K^n`, constant on levels and
  increasing with the level; the quotient rank and uniqueness of base-`(n + 1)` digits force the
  subspace at level `j` to have dimension `j`, so these subspaces form a full flag preserved by
  every matrix fixing the point (`exists_fullFlag`);
* the standard flag gives a stable point over every field (`stdPoint`).
-/

universe u

open scoped TensorProduct
open TensorProduct Module Module.Grassmannian Matrix

namespace Langlands.Grassmannian.FlagLocus

variable (n : ℕ)

/-- The copies of `R^n` in the ambient module: level `j` has `(n + 1) ^ j` copies. -/
abbrev Copy : Type := Σ j : Fin (n + 1), Fin ((n + 1) ^ (j : ℕ))

/-- Coordinates of the ambient module: a copy and a coordinate of `R^n`. -/
abbrev Idx : Type := Copy n × Fin n

/-- The quotient rank of the points of the flag locus. -/
def rank : ℕ := ∑ j : Fin (n + 1), (n + 1) ^ (j : ℕ) * (n - j)

/-- The first copy at level `j`. -/
def firstCopy (j : Fin (n + 1)) : Copy n := ⟨j, ⟨0, pow_pos n.succ_pos _⟩⟩

@[simp] theorem firstCopy_fst (j : Fin (n + 1)) : (firstCopy n j).1 = j := rfl

variable {n}

/-! ### Coordinate maps -/

section Coordinates

variable (A : Type*) [CommRing A]

/-- `shift a b` copies block `b` into block `a` and is zero on the other blocks. -/
def shift (a b : Copy n) : (Idx n → A) →ₗ[A] (Idx n → A) :=
  LinearMap.pi fun x => if x.1 = a then LinearMap.proj (b, x.2) else 0

@[simp] theorem shift_apply (a b : Copy n) (v : Idx n → A) (x : Idx n) :
    shift A a b v x = if x.1 = a then v (b, x.2) else 0 := by
  unfold shift
  split_ifs <;> simp [*]

/-- The vector `w` of `A^n` placed in block `c`. -/
def place (c : Copy n) : (Fin n → A) →ₗ[A] (Idx n → A) :=
  LinearMap.pi fun x => if x.1 = c then LinearMap.proj x.2 else 0

@[simp] theorem place_apply (c : Copy n) (w : Fin n → A) (x : Idx n) :
    place A c w x = if x.1 = c then w x.2 else 0 := by
  unfold place
  split_ifs <;> simp [*]

/-- A square matrix acting on every block. -/
def colAct (g : Matrix (Fin n) (Fin n) A) : (Idx n → A) →ₗ[A] (Idx n → A) :=
  LinearMap.pi fun x => ∑ i, g x.2 i • LinearMap.proj (x.1, i)

@[simp] theorem colAct_apply (g : Matrix (Fin n) (Fin n) A) (v : Idx n → A) (x : Idx n) :
    colAct A g v x = ∑ i, g x.2 i * v (x.1, i) := by
  simp [colAct]

theorem colAct_one : colAct A (1 : Matrix (Fin n) (Fin n) A) = LinearMap.id := by
  refine LinearMap.ext fun v => funext fun x => ?_
  simp [Matrix.one_apply]

theorem colAct_mul (g h : Matrix (Fin n) (Fin n) A) :
    colAct A (g * h) = colAct A g ∘ₗ colAct A h := by
  refine LinearMap.ext fun v => funext fun x => ?_
  simp only [colAct_apply, LinearMap.comp_apply, Matrix.mul_apply, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem shift_colAct (a b : Copy n) (g : Matrix (Fin n) (Fin n) A) (v : Idx n → A) :
    shift A a b (colAct A g v) = colAct A g (shift A a b v) := by
  funext x
  simp only [shift_apply, colAct_apply]
  split_ifs <;> simp

theorem colAct_place (g : Matrix (Fin n) (Fin n) A) (c : Copy n) (w : Fin n → A) :
    colAct A g (place A c w) = place A c (g *ᵥ w) := by
  funext x
  simp only [colAct_apply, place_apply, Matrix.mulVec, dotProduct]
  split_ifs <;> simp

theorem shift_place (a b : Copy n) (w : Fin n → A) : shift A a b (place A b w) = place A a w := by
  funext x
  simp

theorem shift_self (c : Copy n) (v : Idx n → A) :
    shift A c c v = place A c (fun i => v (c, i)) := by
  funext x
  simp

theorem sum_place (v : Idx n → A) : ∑ c, place A c (fun i => v (c, i)) = v := by
  funext x
  simp [Finset.sum_apply]

theorem map_colAct {B : Type*} [CommRing B] (φ : A →+* B) (g : Matrix (Fin n) (Fin n) A)
    (v : Idx n → A) :
    (fun x => φ (colAct A g v x)) = colAct B (φ.mapMatrix g) (fun x => φ (v x)) := by
  funext x
  simp [map_sum]

/-- An invertible matrix acting on every block, as a linear equivalence. -/
def colActEquiv (g : GL (Fin n) A) : (Idx n → A) ≃ₗ[A] (Idx n → A) :=
  LinearEquiv.ofLinearMap (colAct A g) (colAct A ↑g⁻¹)
    (by rw [← colAct_mul, Units.mul_inv, colAct_one])
    (by rw [← colAct_mul, Units.inv_mul, colAct_one])

@[simp] theorem colActEquiv_apply (g : GL (Fin n) A) (v : Idx n → A) :
    colActEquiv A g v = colAct A g v := rfl

end Coordinates

/-! ### Tensor coordinates -/

section Tensor

variable (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]

/-- The coordinate identification `A ⊗[R] (Idx n → R) ≃ (Idx n → A)`. -/
abbrev coord : A ⊗[R] (Idx n → R) ≃ₗ[A] (Idx n → A) := piScalarRight R A A (Idx n)

theorem coord_tmul (a : A) (m : Idx n → R) : coord R A (a ⊗ₜ m) = fun x => m x • a := by
  rw [piScalarRight_apply, piScalarRightHom_tmul]

theorem coord_baseChange_shift (a b : Copy n) (z : A ⊗[R] (Idx n → R)) :
    coord R A ((shift R a b).baseChange A z) = shift A a b (coord R A z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a' m =>
    rw [LinearMap.baseChange_tmul, coord_tmul, coord_tmul]
    funext x
    simp only [shift_apply]
    split_ifs <;> simp
  | add y z hy hz => simp only [map_add, hy, hz]

theorem coord_rTensor {B : Type*} [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)
    (z : A ⊗[R] (Idx n → R)) :
    coord R B (φ.toLinearMap.rTensor _ z) = fun x => φ (coord R A z x) := by
  induction z using TensorProduct.inductionOn with
  | tmul a m =>
    rw [LinearMap.rTensor_tmul, coord_tmul, coord_tmul]
    funext x
    simp
  | add y z hy hz =>
    simp only [map_add, hy, hz]
    funext x
    simp

theorem rTensor_baseChange_shift {B : Type*} [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)
    (a b : Copy n) (z : A ⊗[R] (Idx n → R)) :
    φ.toLinearMap.rTensor _ ((shift R a b).baseChange A z) =
      (shift R a b).baseChange B (φ.toLinearMap.rTensor _ z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a' m => simp [LinearMap.baseChange_tmul]
  | add y z hy hz => simp only [map_add, hy, hz]

/-- An invertible matrix acting on every block of `A ⊗[R] (Idx n → R)`. -/
def actEquiv (g : GL (Fin n) A) : (A ⊗[R] (Idx n → R)) ≃ₗ[A] (A ⊗[R] (Idx n → R)) :=
  (coord R A).trans ((colActEquiv A g).trans (coord R A).symm)

theorem coord_actEquiv (g : GL (Fin n) A) (z : A ⊗[R] (Idx n → R)) :
    coord R A (actEquiv R A g z) = colAct A g (coord R A z) := by
  simp [actEquiv]

theorem actEquiv_one (z : A ⊗[R] (Idx n → R)) : actEquiv R A 1 z = z := by
  apply (coord R A).injective
  rw [coord_actEquiv, Units.val_one, colAct_one, LinearMap.id_apply]

theorem actEquiv_mul (g h : GL (Fin n) A) (z : A ⊗[R] (Idx n → R)) :
    actEquiv R A (g * h) z = actEquiv R A g (actEquiv R A h z) := by
  apply (coord R A).injective
  rw [coord_actEquiv, coord_actEquiv, coord_actEquiv, Units.val_mul, colAct_mul,
    LinearMap.comp_apply]

theorem baseChange_shift_actEquiv (a b : Copy n) (g : GL (Fin n) A) (z : A ⊗[R] (Idx n → R)) :
    (shift R a b).baseChange A (actEquiv R A g z) =
      actEquiv R A g ((shift R a b).baseChange A z) := by
  apply (coord R A).injective
  rw [coord_baseChange_shift, coord_actEquiv, coord_actEquiv, coord_baseChange_shift,
    shift_colAct]

theorem rTensor_actEquiv {B : Type*} [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)
    (g : GL (Fin n) A) (z : A ⊗[R] (Idx n → R)) :
    φ.toLinearMap.rTensor _ (actEquiv R A g z) =
      actEquiv R B (Matrix.GeneralLinearGroup.map φ.toRingHom g)
        (φ.toLinearMap.rTensor _ z) := by
  apply (coord R B).injective
  rw [coord_rTensor, coord_actEquiv, coord_actEquiv, coord_rTensor]
  exact map_colAct A φ.toRingHom (g : Matrix (Fin n) (Fin n) A) (coord R A z)

end Tensor

/-! ### Grassmannian points -/

section Points

variable {A : Type*} [CommRing A]

/-- Transport of a Grassmannian point along a linear equivalence of the ambient modules. -/
def transport {V W : Type*} [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
    {k : ℕ} (σ : V ≃ₗ[A] W) (P : G(k, V; A)) : G(k, W; A) where
  toSubmodule := P.toSubmodule.map (σ : V →ₗ[A] W)
  finite_quotient := Module.Finite.equiv (Submodule.Quotient.equiv _ _ σ rfl)
  projective_quotient := Module.Projective.of_equiv (Submodule.Quotient.equiv _ _ σ rfl)
  rankAtStalk_eq p := by
    rw [← rankAtStalk_eq_of_equiv (Submodule.Quotient.equiv _ _ σ rfl)]
    exact P.rankAtStalk_eq p

@[simp] theorem transport_toSubmodule {V W : Type*} [AddCommGroup V] [Module A V]
    [AddCommGroup W] [Module A W] {k : ℕ} (σ : V ≃ₗ[A] W) (P : G(k, V; A)) :
    (transport σ P).toSubmodule = P.toSubmodule.map (σ : V →ₗ[A] W) := rfl

variable (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A] {k : ℕ}

/-- The action of `GL_n(A)` on the points of `G(k, A ⊗[R] (Idx n → R); A)`. -/
def smul (g : GL (Fin n) A) (P : G(k, A ⊗[R] (Idx n → R); A)) : G(k, A ⊗[R] (Idx n → R); A) :=
  transport (actEquiv R A g) P

@[simp] theorem smul_toSubmodule (g : GL (Fin n) A) (P : G(k, A ⊗[R] (Idx n → R); A)) :
    (smul R g P).toSubmodule = P.toSubmodule.map (actEquiv R A g : _ →ₗ[A] _) := rfl

theorem one_smul (P : G(k, A ⊗[R] (Idx n → R); A)) : smul R 1 P = P := by
  ext1
  rw [smul_toSubmodule]
  conv_rhs => rw [← Submodule.map_id P.toSubmodule]
  congr 1
  exact LinearMap.ext (actEquiv_one R A)

theorem mul_smul (g h : GL (Fin n) A) (P : G(k, A ⊗[R] (Idx n → R); A)) :
    smul R (g * h) P = smul R g (smul R h P) := by
  ext1
  rw [smul_toSubmodule, smul_toSubmodule, smul_toSubmodule, ← Submodule.map_comp]
  congr 1
  exact LinearMap.ext (actEquiv_mul R A g h)

/-- The action commutes with base change. -/
theorem map_smul_point {B : Type u} [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) (g : GL (Fin n) A)
    (P : G(k, A ⊗[R] (Idx n → R); A)) :
    Module.Grassmannian.map φ (smul R g P) =
      smul R (Matrix.GeneralLinearGroup.map φ.toRingHom g) (Module.Grassmannian.map φ P) := by
  ext1
  rw [map_toSubmodule_eq_span, smul_toSubmodule, smul_toSubmodule, map_toSubmodule_eq_span,
    Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
  congr 1
  exact Set.image_congr fun z _ => rTensor_actEquiv R A φ g z

/-- The flag condition: the point is preserved by the maps copying block `b` into block `a`
whenever the level of `b` is at most the level of `a`. -/
def Stable (P : G(k, A ⊗[R] (Idx n → R); A)) : Prop :=
  ∀ a b : Copy n, b.1 ≤ a.1 → ∀ z ∈ P.toSubmodule, (shift R a b).baseChange A z ∈ P.toSubmodule

theorem Stable.smul {P : G(k, A ⊗[R] (Idx n → R); A)} (hP : Stable R P) (g : GL (Fin n) A) :
    Stable R (smul R g P) := by
  intro a b hab z hz
  rw [smul_toSubmodule] at hz ⊢
  obtain ⟨y, hy, rfl⟩ := hz
  exact ⟨_, hP a b hab y hy, (baseChange_shift_actEquiv R A a b g y).symm⟩

/-- The flag condition on base changes of a point is cut out by an ideal. -/
theorem exists_ideal_stable_map_iff (P : G(k, A ⊗[R] (Idx n → R); A)) :
    ∃ 𝔞 : Ideal A, ∀ (B : Type u) [CommRing B] [Algebra R B] (φ : A →ₐ[R] B),
      Stable R (Module.Grassmannian.map φ P) ↔ ∀ a ∈ 𝔞, φ a = 0 := by
  let τ := {t : Copy n × Copy n × P.toSubmodule // t.2.1.1 ≤ t.1.1}
  obtain ⟨𝔞, h𝔞⟩ := exists_ideal_forall_rTensor_mem_map_iff P
    (fun t : τ => (shift R t.1.1 t.1.2.1).baseChange A (t.1.2.2 : A ⊗[R] (Idx n → R)))
  refine ⟨𝔞, fun B _ _ φ => Iff.trans ?_ (h𝔞 B φ)⟩
  have hspan := map_toSubmodule_eq_span φ P
  constructor
  · intro h t
    rw [rTensor_baseChange_shift]
    refine h _ _ t.2 _ ?_
    rw [hspan]
    exact Submodule.subset_span ⟨_, t.1.2.2.2, rfl⟩
  · intro h a b hab y hy
    rw [hspan] at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      rw [← rTensor_baseChange_shift]
      exact h ⟨(a, b, ⟨z, hz⟩), hab⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y y' _ _ hy hy' => rw [map_add]; exact Submodule.add_mem _ hy hy'
    | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy

/-- The flag condition is preserved by base change. -/
theorem Stable.map {P : G(k, A ⊗[R] (Idx n → R); A)} (hP : Stable R P) {B : Type u}
    [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) : Stable R (Module.Grassmannian.map φ P) := by
  intro a b hab y hy
  rw [map_toSubmodule_eq_span] at hy ⊢
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, hz, rfl⟩ := hy
    rw [← rTensor_baseChange_shift]
    exact Submodule.subset_span ⟨_, hP a b hab z hz, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y y' _ _ hy hy' => rw [map_add]; exact Submodule.add_mem _ hy hy'
  | smul c y _ hy => rw [_root_.map_smul]; exact Submodule.smul_mem _ c hy

end Points

/-! ### Digits -/

/-- Base-`b` expansions with digits below `b` are unique. -/
theorem digits_eq {b : ℕ} : ∀ {m : ℕ} (x y : Fin m → ℕ), (∀ j, x j < b) → (∀ j, y j < b) →
    ∑ j : Fin m, b ^ (j : ℕ) * x j = ∑ j : Fin m, b ^ (j : ℕ) * y j → x = y
  | 0, _, _, _, _, _ => funext fun j => j.elim0
  | m + 1, x, y, hx, hy, h => by
    have hs : ∀ z : Fin (m + 1) → ℕ, ∑ j : Fin (m + 1), b ^ (j : ℕ) * z j =
        z 0 + b * ∑ j : Fin m, b ^ (j : ℕ) * z j.succ := by
      intro z
      rw [Fin.sum_univ_succ, Finset.mul_sum]
      simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hs, hs] at h
    have h0 : x 0 = y 0 := by
      have := congrArg (· % b) h
      simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hx 0), Nat.mod_eq_of_lt (hy 0)]
        using this
    have hb : 0 < b := lt_of_le_of_lt (Nat.zero_le _) (hx 0)
    rw [h0] at h
    have h' := Nat.eq_of_mul_eq_mul_left hb (Nat.add_left_cancel h)
    have hrest := digits_eq (fun j => x j.succ) (fun j => y j.succ) (fun j => hx _)
      (fun j => hy _) h'
    funext j
    exact Fin.cases h0 (fun j => congrFun hrest j) j

/-! ### Points over a field -/

section Field

variable (R : Type u) [CommRing R] {K : Type u} [Field K] [Algebra R K] {k : ℕ}

/-- The coordinate subspace of a point. -/
def coords (P : G(k, K ⊗[R] (Idx n → R); K)) : Submodule K (Idx n → K) :=
  P.toSubmodule.map (coord (n := n) R K : K ⊗[R] (Idx n → R) →ₗ[K] Idx n → K)

/-- The block of a point at the copy `c`: the vectors which, placed in block `c`, lie in its
coordinate subspace. -/
def block (P : G(k, K ⊗[R] (Idx n → R); K)) (c : Copy n) : Submodule K (Fin n → K) :=
  (coords R P).comap (place K c)

variable {R}

theorem Stable.shift_mem {P : G(k, K ⊗[R] (Idx n → R); K)} (hP : Stable R P) {a b : Copy n}
    (hab : b.1 ≤ a.1) {v : Idx n → K} (hv : v ∈ coords R P) : shift K a b v ∈ coords R P := by
  obtain ⟨z, hz, rfl⟩ := hv
  exact ⟨_, hP a b hab z hz, coord_baseChange_shift R K a b z⟩

theorem Stable.block_mono {P : G(k, K ⊗[R] (Idx n → R); K)} (hP : Stable R P) {a b : Copy n}
    (hab : b.1 ≤ a.1) : block R P b ≤ block R P a := by
  intro w hw
  change place K a w ∈ coords R P
  rw [← shift_place]
  exact hP.shift_mem hab hw

theorem Stable.mem_coords_iff {P : G(k, K ⊗[R] (Idx n → R); K)} (hP : Stable R P)
    (v : Idx n → K) : v ∈ coords R P ↔ ∀ c, (fun i => v (c, i)) ∈ block R P c := by
  constructor
  · intro hv c
    change place K c _ ∈ coords R P
    rw [← shift_self]
    exact hP.shift_mem le_rfl hv
  · intro hv
    rw [← sum_place K v]
    exact Submodule.sum_mem _ fun c _ => hv c

/-- A stable point is the product of its blocks. -/
def Stable.coordsEquiv {P : G(k, K ⊗[R] (Idx n → R); K)} (hP : Stable R P) :
    coords R P ≃ₗ[K] ∀ c, block R P c where
  toFun v c := ⟨fun i => v.1 (c, i), (hP.mem_coords_iff v.1).1 v.2 c⟩
  invFun w := ⟨fun x => (w x.1).1 x.2, (hP.mem_coords_iff _).2 fun c => (w c).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem finrank_quotient_coords (P : G(rank n, K ⊗[R] (Idx n → R); K)) :
    finrank K ((Idx n → K) ⧸ coords R P) = rank n := by
  let q := Submodule.Quotient.equiv P.toSubmodule (coords R P) (coord R K) rfl
  have h := P.rankAtStalk_eq ⟨⊥, Ideal.isPrime_bot⟩
  rw [rankAtStalk_eq_of_equiv q, rankAtStalk_eq_finrank_of_free] at h
  exact h

theorem Stable.finrank_block {P : G(rank n, K ⊗[R] (Idx n → R); K)} (hP : Stable R P)
    (j : Fin (n + 1)) : finrank K (block R P (firstCopy n j)) = j := by
  let d : Fin (n + 1) → ℕ := fun j => finrank K (block R P (firstCopy n j))
  have hblock : ∀ c : Copy n, block R P c = block R P (firstCopy n c.1) := fun c =>
    le_antisymm (hP.block_mono le_rfl) (hP.block_mono le_rfl)
  have hd : ∀ j, d j ≤ n := fun j =>
    (Submodule.finrank_le _).trans (Module.finrank_fin_fun K).le
  have hsum : ∑ c : Copy n, finrank K (block R P c) = ∑ j : Fin (n + 1), (n + 1) ^ (j : ℕ) * d j := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj : ∀ y : Fin ((n + 1) ^ (j : ℕ)), finrank K (block R P ⟨j, y⟩) = d j := fun y => by
      rw [hblock ⟨j, y⟩]
    rw [Finset.sum_congr rfl fun y _ => hj y, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  have hcoords : finrank K (coords R P) = ∑ j : Fin (n + 1), (n + 1) ^ (j : ℕ) * d j := by
    rw [hP.coordsEquiv.finrank_eq, Module.finrank_pi_fintype, hsum]
  have htot := Submodule.finrank_quotient_add_finrank (coords R P)
  rw [finrank_quotient_coords, hcoords, Module.finrank_fintype_fun_eq_card, Fintype.card_prod,
    Fintype.card_sigma, Fintype.card_fin, Finset.sum_mul] at htot
  simp only [Fintype.card_fin] at htot
  have hsplit : ∑ j : Fin (n + 1), (n + 1) ^ (j : ℕ) * n =
      ∑ j : Fin (n + 1), (n + 1) ^ (j : ℕ) * (n - d j) +
        ∑ j : Fin (n + 1), (n + 1) ^ (j : ℕ) * d j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_add, Nat.sub_add_cancel (hd j)]
  rw [hsplit, rank] at htot
  have hdig := digits_eq (b := n + 1) (fun j : Fin (n + 1) => n - j)
    (fun j => n - d j) (fun j => by omega) (fun j => by omega) (Nat.add_right_cancel htot)
  have h1 : n - (j : ℕ) = n - d j := congrFun hdig j
  have hj := j.isLt
  have h2 := hd j
  show d j = j
  omega

theorem mulVec_mem_block {P : G(k, K ⊗[R] (Idx n → R); K)} (g : GL (Fin n) K)
    (hg : smul R g P = P) (c : Copy n) {w : Fin n → K} (hw : w ∈ block R P c) :
    (g : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ block R P c := by
  change place K c _ ∈ coords R P
  obtain ⟨z, hz, hzw⟩ := hw
  have hz' : actEquiv R K g z ∈ P.toSubmodule := by
    rw [← hg, smul_toSubmodule]
    exact Submodule.mem_map_of_mem hz
  refine ⟨_, hz', ?_⟩
  change coord R K (actEquiv R K g z) = _
  rw [coord_actEquiv, ← colAct_place]
  exact congrArg _ hzw

/-- A stable point over a field determines a full flag of `K^n` preserved by every matrix
fixing the point. -/
theorem exists_fullFlag (P : G(rank n, K ⊗[R] (Idx n → R); K)) (hP : Stable R P) :
    ∃ F : Fin (n + 1) → Submodule K (Fin n → K), Monotone F ∧
      (∀ j, finrank K (F j) = j) ∧
      ∀ g : GL (Fin n) K, smul R g P = P → ∀ j, ∀ v ∈ F j,
        (g : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ F j :=
  ⟨fun j => block R P (firstCopy n j), fun _ _ hij => hP.block_mono hij, hP.finrank_block,
    fun g hg _ _ hv => mulVec_mem_block g hg _ hv⟩

/-! ### The standard point -/

/-- The coordinates `(c, i)` with `level c ≤ i`. -/
abbrev StdIdx (n : ℕ) : Type := {x : Idx n // (x.1.1 : ℕ) ≤ x.2}

/-- `StdIdx n` is the disjoint union over copies `c` of `n - level c` coordinates. -/
def stdIdxEquiv : StdIdx n ≃ Σ c : Copy n, Fin (n - c.1) where
  toFun x := ⟨x.1.1, ⟨x.1.2 - x.1.1.1, by have := x.1.2.isLt; have := x.2; omega⟩⟩
  invFun y := ⟨(y.1, ⟨y.2 + y.1.1, by have := y.2.isLt; omega⟩), by simp⟩
  left_inv x := by
    obtain ⟨⟨c, i⟩, h⟩ := x
    simp only at h
    ext <;> simp; omega
  right_inv y := by
    obtain ⟨c, t⟩ := y
    ext <;> simp

theorem card_stdIdx : Fintype.card (StdIdx n) = rank n := by
  rw [Fintype.card_congr stdIdxEquiv, Fintype.card_sigma, Fintype.sum_sigma, rank]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [mul_comm]

variable (R K) in
/-- The coordinate subspace of the standard flag: vectors vanishing at `(c, i)` with
`level c ≤ i`. -/
def stdCoords : Submodule K (Idx n → K) :=
  LinearMap.ker (LinearMap.funLeft K K (Subtype.val : StdIdx n → Idx n))

theorem mem_stdCoords {v : Idx n → K} :
    v ∈ stdCoords K ↔ ∀ x : StdIdx n, v x.1 = 0 := by
  simp [stdCoords, funext_iff, LinearMap.funLeft_apply]

variable (R K n) in
/-- The submodule of the standard full flag point. -/
def stdSub : Submodule K (K ⊗[R] (Idx n → R)) :=
  (stdCoords K).comap (coord (n := n) R K).toLinearMap

theorem map_stdSub : (stdSub n R K).map (coord (n := n) R K).toLinearMap = stdCoords K :=
  Submodule.map_comap_eq_of_surjective (coord (n := n) R K).surjective _

variable (R K n) in
/-- The quotient by the standard submodule is the free module on `StdIdx n`. -/
noncomputable def stdQuotEquiv : (K ⊗[R] (Idx n → R) ⧸ stdSub n R K) ≃ₗ[K] (StdIdx n → K) :=
  (Submodule.Quotient.equiv (stdSub n R K) (stdCoords K) (coord R K) map_stdSub).trans
    ((LinearMap.funLeft K K (Subtype.val : StdIdx n → Idx n)).quotKerEquivOfSurjective
      (LinearMap.funLeft_surjective_of_injective _ _ _ Subtype.val_injective))

variable (R K n) in
/-- The point of the standard full flag over a field. -/
noncomputable def stdPoint : G(rank n, K ⊗[R] (Idx n → R); K) where
  toSubmodule := stdSub n R K
  finite_quotient := Module.Finite.equiv (stdQuotEquiv n R K).symm
  projective_quotient := Module.Projective.of_equiv (stdQuotEquiv n R K).symm
  rankAtStalk_eq p := by
    rw [rankAtStalk_eq_of_equiv (stdQuotEquiv n R K), rankAtStalk_eq_finrank_of_free,
      Module.finrank_fintype_fun_eq_card, card_stdIdx]
    rfl

theorem coords_stdPoint : coords R (stdPoint n R K) = stdCoords K :=
  map_stdSub

theorem stable_stdPoint : Stable R (stdPoint n R K) := by
  intro a b hab z hz
  change coord R K _ ∈ stdCoords K
  change coord R K z ∈ stdCoords K at hz
  rw [coord_baseChange_shift]
  rw [mem_stdCoords] at hz ⊢
  intro x
  rw [shift_apply]
  split_ifs with h
  · exact hz ⟨(b, x.1.2), le_trans (h ▸ hab : (b.1 : ℕ) ≤ x.1.1.1) x.2⟩
  · rfl

end Field

end Langlands.Grassmannian.FlagLocus
