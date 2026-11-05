import Langlands.GroupScheme.SplitExistence.SimpleWeyl
import Langlands.GroupScheme.SplitExistence.ChevalleyLieData

/-!
# Integral Chevalley data with Lie relations from simple `SL₂`-data

For a reduced root datum with finitely many roots, base `b` and integral `SL₂`-data
`S : SimpleRootData P b` for the simple roots, we construct the divided-power root operators of
all roots (`SimpleRootData.rootOp`): `E i` for a simple root `i`, `F i` for its negative, and
otherwise the conjugate `n_w E_i n_w⁻¹` of the operators of a simple root by a Weyl word `w`
with `w α_i = α_j`.

A family `D` is a *family of root operators* of the root `j` (`SimpleRootData.IsRootOp`) when it
is a divided-power family, `D k` has weight `k • α_j`, `D 1` is nonzero modulo every prime, and
`D 1` lies in the rational Lie algebra `lieSpan` of the simple root operators. Two such families
differ by a sign: `D' k = ε ^ k • D k` with `ε = ± 1` (`IsRootOp.exists_eq_pow_smul`), because
the root components of `lieSpan` are lines. Conjugating a family of root operators by a Weyl
element gives one of the reflected root, which yields the Weyl conjugation formula; the
minimal-height argument shows that a nonzero commutator `[e_j, e_j']` has a root as weight,
which yields the Lie relations. Together this gives `SimpleRootData.toChevalleyLieData`.
-/

noncomputable section

universe u

open Matrix

namespace Langlands.GroupScheme.SplitExistence

section Generic

variable {n : ℕ} {R : Type*} [CommRing R]

/-- Conjugating a truncated exponential by integral matrices conjugates its terms. -/
theorem map_mul_divExp_mul (g g' : Matrix (Fin n) (Fin n) ℤ) (D : ℕ → Matrix (Fin n) (Fin n) ℤ)
    (s : R) :
    g.map (Int.castRingHom R) * divExp D s * g'.map (Int.castRingHom R) =
      divExp (fun k => g * D k * g') s := by
  unfold divExp
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.map_mul]

/-- Rescaling the terms of a truncated exponential by `z ^ k` rescales its parameter by `z`. -/
theorem divExp_pow_smul (D : ℕ → Matrix (Fin n) (Fin n) ℤ) (z : ℤ) (s : R) :
    divExp (fun k => z ^ k • D k) s = divExp D ((z : R) * s) := by
  unfold divExp
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_intCast_zsmul, smul_smul]
  congr 1
  push_cast
  ring

/-- Conjugation by an invertible integral matrix preserves divided-power families. -/
theorem IsDividedPowerFamily.conj {D : ℕ → Matrix (Fin n) (Fin n) ℤ} (hD : IsDividedPowerFamily D)
    {g g' : Matrix (Fin n) (Fin n) ℤ} (h1 : g * g' = 1) (h2 : g' * g = 1) :
    IsDividedPowerFamily (fun k => g * D k * g') where
  zero := by
    show g * D 0 * g' = 1
    rw [hD.zero, Matrix.mul_one, h1]
  mul a c := by
    show g * D a * g' * (g * D c * g') = _ • (g * D (a + c) * g')
    rw [show g * D a * g' * (g * D c * g') = g * (D a * D c) * g' by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc g' g, h2, Matrix.one_mul],
      hD.mul, Matrix.mul_smul, Matrix.smul_mul]
  eq_zero k hk := by
    show g * D k * g' = 0
    rw [hD.eq_zero k hk, Matrix.mul_zero, Matrix.zero_mul]

/-- Conjugation of a nonzero rational matrix by an invertible integral matrix is nonzero. -/
theorem map_conj_ne_zero_rat {g g' : Matrix (Fin n) (Fin n) ℤ} (h : g' * g = 1)
    {y : Matrix (Fin n) (Fin n) ℚ} (hy : y ≠ 0) :
    g.map (Int.castRingHom ℚ) * y * g'.map (Int.castRingHom ℚ) ≠ 0 := by
  intro h0
  apply hy
  have h1 : g'.map (Int.castRingHom ℚ) * g.map (Int.castRingHom ℚ) = 1 := by
    rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  calc y = g'.map (Int.castRingHom ℚ) *
        (g.map (Int.castRingHom ℚ) * y * g'.map (Int.castRingHom ℚ)) *
          g.map (Int.castRingHom ℚ) := by
        simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
        rw [Matrix.mul_assoc, h1, Matrix.mul_one]
    _ = 0 := by rw [h0, Matrix.mul_zero, Matrix.zero_mul]

end Generic

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y} {b : P.Base}

/-- The negative of a simple root is not a simple root. -/
theorem reflectionPerm_self_not_mem (i : b.support) : P.reflectionPerm i i ∉ b.support := by
  intro h
  have hne : P.reflectionPerm i i ≠ i := fun h' => P.ne_neg (i := (i : J)) h'.symm
  apply b.root_ne_neg_of_ne h i.2 hne
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]

namespace SimpleRootData

open Classical

variable (S : SimpleRootData P b)

/-- `D` is a family of root operators of the root `j`: a divided-power family of integral
matrices, `D k` of weight `k • α_j`, with `D 1` nonzero modulo every prime and lying in the
rational Lie algebra of the simple root operators. -/
structure IsRootOp (j : J) (D : ℕ → Matrix (Fin S.n) (Fin S.n) ℤ) : Prop where
  dp : IsDividedPowerFamily D
  isWtHom : ∀ k : ℕ, IsWtHom S.wt (k • P.root j) (D k)
  prim : ∀ p : ℕ, p.Prime → (D 1).map (Int.castRingHom (ZMod p)) ≠ 0
  mem : (D 1).map (Int.castRingHom ℚ) ∈ S.toLieGens.lieSpan

variable {S}

theorem isRootOp_E (i : b.support) : S.IsRootOp i (S.E i) where
  dp := S.isDividedPowerFamily_E i
  isWtHom := S.isWtHom_E i
  prim := S.E_one_map_ne_zero i
  mem := S.toLieGens.e_mem i

theorem isRootOp_F (i : b.support) : S.IsRootOp (P.reflectionPerm i i) (S.F i) where
  dp := S.isDividedPowerFamily_F i
  isWtHom k := by
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self, smul_neg]
    exact S.isWtHom_F i k
  prim := S.F_one_map_ne_zero i
  mem := S.toLieGens.f_mem i

/-- Conjugating a family of root operators by an invertible integral matrix that moves weights
by an automorphism `f` and preserves the rational Lie algebra gives a family of root operators
of the root `f α_j`. -/
theorem IsRootOp.conj {j : J} {D : ℕ → Matrix (Fin S.n) (Fin S.n) ℤ} (hD : S.IsRootOp j D)
    {g g' : Matrix (Fin S.n) (Fin S.n) ℤ} (h1 : g * g' = 1) (h2 : g' * g = 1) (f : X ≃ₗ[ℤ] X)
    (hg : MapsWt S.wt f g) (hg' : MapsWt S.wt f.symm g')
    (hmem : ∀ x ∈ S.toLieGens.lieSpan,
      g.map (Int.castRingHom ℚ) * x * g'.map (Int.castRingHom ℚ) ∈ S.toLieGens.lieSpan)
    {j' : J} (hj' : P.root j' = f (P.root j)) :
    S.IsRootOp j' (fun k => g * D k * g') where
  dp := hD.dp.conj h1 h2
  isWtHom k := by
    have h := IsWtHom.conj_linearEquiv f hg hg' (hD.isWtHom k)
    rwa [map_nsmul, ← hj'] at h
  prim p hp := map_conj_ne_zero _ h2 (hD.prim p hp)
  mem := by
    show (g * D 1 * g').map (Int.castRingHom ℚ) ∈ S.toLieGens.lieSpan
    rw [Matrix.map_mul, Matrix.map_mul]
    exact hmem _ hD.mem

/-- Conjugating a family of root operators of `j` by the Weyl element of a simple root `i` gives
a family of root operators of `s_i j`. -/
theorem IsRootOp.weylMat {j : J} {D : ℕ → Matrix (Fin S.n) (Fin S.n) ℤ} (hD : S.IsRootOp j D)
    (i : b.support) :
    S.IsRootOp (P.reflectionPerm i j) (fun k => S.weylMat i * D k * S.weylMatInv i) :=
  hD.conj (S.weylMat_mul_weylMatInv i) (S.weylMatInv_mul_weylMat i) (P.reflection i)
    (S.mapsWt_weylMat i) (S.mapsWt_weylMatInv i) (fun _ hx => S.weylMat_conj_mem i hx)
    (RootPairing.root_reflectionPerm P i j)

variable (S) in
/-- The conjugate `n_w E_i n_w⁻¹` of the root operators of a simple root by a Weyl word. -/
def wordOp (w : List b.support) (i : b.support) : ℕ → Matrix (Fin S.n) (Fin S.n) ℤ :=
  fun k => S.wordMat w * S.E i k * S.wordMatInv w

theorem isRootOp_wordOp (w : List b.support) (i : b.support) {j : J}
    (hj : P.root j = weylWord P b w (P.root i)) : S.IsRootOp j (S.wordOp w i) :=
  (isRootOp_E i).conj (S.wordMat_mul_wordMatInv w) (S.wordMatInv_mul_wordMat w)
    (weylWord P b w) (S.mapsWt_wordMat w) (S.mapsWt_wordMatInv w)
    (fun _ hx => S.wordMat_conj_mem w hx) hj

/-! ### Uniqueness of root operators up to sign -/

variable [Finite J] [P.IsReduced]

/-- The component of `lieSpan` of weight `α_j` is the line of `D 1`, for a family `D` of root
operators of `j`. -/
theorem IsRootOp.exists_eq_smul {j : J} {D : ℕ → Matrix (Fin S.n) (Fin S.n) ℤ}
    (hD : S.IsRootOp j D) {x : Matrix (Fin S.n) (Fin S.n) ℚ} (hx : x ∈ S.toLieGens.lieSpan)
    (hxw : IsWtHom S.wt (P.root j) x) : ∃ q : ℚ, x = q • (D 1).map (Int.castRingHom ℚ) := by
  obtain ⟨y, -, -, -, hline⟩ := S.exists_line_of_root j
  have hD1w := (hD.isWtHom 1).map (Int.castRingHom ℚ)
  rw [one_smul] at hD1w
  obtain ⟨q0, hq0⟩ := hline _ hD.mem hD1w
  obtain ⟨q, hq⟩ := hline x hx hxw
  have hne : (D 1).map (Int.castRingHom ℚ) ≠ 0 := map_rat_ne_zero (hD.prim 2 Nat.prime_two)
  have hq0' : q0 ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hq0
    exact hne hq0
  refine ⟨q * q0⁻¹, ?_⟩
  rw [hq0, smul_smul, mul_assoc, inv_mul_cancel₀ hq0', mul_one, hq]

/-- Two families of root operators of the same root differ by a sign `ε = ± 1`:
`D' k = ε ^ k • D k`. -/
theorem IsRootOp.exists_eq_pow_smul {j : J} {D D' : ℕ → Matrix (Fin S.n) (Fin S.n) ℤ}
    (hD : S.IsRootOp j D) (hD' : S.IsRootOp j D') :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ k, D' k = ε ^ k • D k := by
  have hD'w := (hD'.isWtHom 1).map (Int.castRingHom ℚ)
  rw [one_smul] at hD'w
  obtain ⟨q, hq⟩ := hD.exists_eq_smul hD'.mem hD'w
  obtain ⟨ε, hε, -, h1⟩ := eq_one_or_eq_neg_one_of_map_eq_smul hD'.prim hD.prim hq
  refine ⟨ε, hε, fun k => ?_⟩
  have hpow := hD'.dp.pow_one k
  rw [h1, smul_pow, hD.dp.pow_one k, smul_comm] at hpow
  ext c d
  have h := congrFun (congrFun hpow c) d
  simp only [Matrix.smul_apply, smul_eq_mul] at h
  rw [Matrix.smul_apply, smul_eq_mul]
  exact (mul_left_cancel₀ (by exact_mod_cast k.factorial_ne_zero) h).symm

omit [P.IsReduced] in
/-- A nonzero homogeneous element of `lieSpan` of nonzero weight has a root as weight (the
minimal-height argument). -/
theorem exists_root_of_isWtHom {x : Matrix (Fin S.n) (Fin S.n) ℚ}
    (hx : x ∈ S.toLieGens.lieSpan) (hx0 : x ≠ 0) {μ : X} (hμ0 : μ ≠ 0)
    (hxw : IsWtHom S.wt μ x) : ∃ k : J, P.root k = μ := by
  refine mem_range_root_of_weylStable (P := P) (b := b)
    (Λ := {μ | μ ≠ 0 ∧ ∃ y ∈ S.toLieGens.lieSpan, y ≠ 0 ∧ IsWtHom S.wt μ y}) ?_ ?_ ?_ ?_ μ
    ⟨hμ0, x, hx, hx0, hxw⟩
  · rintro i hi ν ⟨hν, y, hy, hy0, hyw⟩
    exact ⟨(LinearEquiv.map_ne_zero_iff _).2 hν, _, S.weylMat_conj_mem ⟨i, hi⟩ hy,
      map_conj_ne_zero_rat (S.weylMatInv_mul_weylMat ⟨i, hi⟩) hy0,
      S.isWtHom_weylMat_conj ⟨i, hi⟩ hyw⟩
  · rintro ν ⟨hν, y, hy, hy0, hyw⟩
    exact S.toLieGens.exists_coeff_of_isWtHom hy hy0 hν hyw
  · rintro ⟨h, -⟩
    exact h rfl
  · rintro i hi k ⟨hk, y, hy, hy0, hyw⟩
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hk (zero_smul _ _)
    exact S.toLieGens.eq_one_or_eq_neg_one_of_isWtHom hy hy0 ⟨i, hi⟩ k hk0 hyw

/-! ### The root operators of all roots -/

variable (S) in
/-- The divided-power root operators of a root `j`: `E i` if `j` is a simple root `i`, `F i` if
`j` is the negative of a simple root `i`, and otherwise the conjugate of the operators of a
simple root `i` by a Weyl word `w` with `w α_i = α_j`. -/
def rootOp (j : J) : ℕ → Matrix (Fin S.n) (Fin S.n) ℤ :=
  if h : j ∈ b.support then S.E ⟨j, h⟩
  else if h' : ∃ i : b.support, P.reflectionPerm i i = j then S.F h'.choose
  else S.wordOp (exists_weylWord_root (b := b) j).choose
    (exists_weylWord_root (b := b) j).choose_spec.choose

theorem isRootOp_rootOp (j : J) : S.IsRootOp j (S.rootOp j) := by
  unfold rootOp
  split_ifs with h h'
  · exact isRootOp_E ⟨j, h⟩
  · have h2 := isRootOp_F (S := S) h'.choose
    rwa [h'.choose_spec] at h2
  · exact isRootOp_wordOp _ _ (exists_weylWord_root (b := b) j).choose_spec.choose_spec

theorem rootOp_simple (i : b.support) : S.rootOp i = S.E i := by
  rw [rootOp, dite_eq_left i.2]

theorem rootOp_reflectionPerm_self (i : b.support) :
    S.rootOp (P.reflectionPerm i i) = S.F i := by
  have hex : ∃ i' : b.support, P.reflectionPerm i' i' = P.reflectionPerm i i := ⟨i, rfl⟩
  rw [rootOp, dite_eq_right (reflectionPerm_self_not_mem i), dite_eq_left hex]
  congr 1
  apply Subtype.ext
  apply P.root.injective
  have h := congrArg P.root hex.choose_spec
  rwa [RootPairing.root_reflectionPerm, RootPairing.root_reflectionPerm,
    RootPairing.reflection_apply_self, RootPairing.reflection_apply_self, neg_inj] at h

/-- Weyl conjugation of the root operators, up to a sign of the parameter. -/
theorem weyl_conj_rootOp (i : b.support) (j : J) : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
    ∀ (R : Type u) [CommRing R] (s : R),
      ((S.φ i R sl2Weyl : GL (Fin S.n) R) : Matrix (Fin S.n) (Fin S.n) R) *
          divExp (S.rootOp j) s * ((S.φ i R sl2Weyl)⁻¹ : GL (Fin S.n) R) =
        divExp (S.rootOp (P.reflectionPerm i j)) ((ε : R) * s) := by
  obtain ⟨ε, hε, hk⟩ :=
    (isRootOp_rootOp (S := S) (P.reflectionPerm i j)).exists_eq_pow_smul
      ((isRootOp_rootOp (S := S) j).weylMat i)
  refine ⟨ε, hε, fun R _ s => ?_⟩
  rw [← S.map_weylMatInv, ← S.map_weylMat, map_mul_divExp_mul, ← divExp_pow_smul]
  congr 1
  funext k
  exact hk k

/-- The Lie relations among the root operators of two families of root operators. -/
theorem lie_of_isRootOp {j j' : J} {A A' : ℕ → Matrix (Fin S.n) (Fin S.n) ℤ}
    (hA : S.IsRootOp j A) (hA' : S.IsRootOp j' A') (h : P.root j' ≠ -P.root j) :
    A 1 * A' 1 - A' 1 * A 1 = 0 ∨
      ∃ (k : J) (c : ℤ), P.root k = P.root j + P.root j' ∧
        A 1 * A' 1 - A' 1 * A 1 = c • S.rootOp k 1 := by
  rcases eq_or_ne (A 1 * A' 1 - A' 1 * A 1) 0 with hC0 | hC0
  · exact Or.inl hC0
  right
  have hCmem : (A 1 * A' 1 - A' 1 * A 1).map (Int.castRingHom ℚ) ∈ S.toLieGens.lieSpan := by
    rw [Matrix.map_sub _ (map_sub (Int.castRingHom ℚ)), Matrix.map_mul, Matrix.map_mul,
      ← matAd_apply]
    exact S.toLieGens.matAd_mem hA.mem hA'.mem
  have hCw : IsWtHom S.wt (P.root j + P.root j')
      ((A 1 * A' 1 - A' 1 * A 1).map (Int.castRingHom ℚ)) := by
    have h1 := ((hA.isWtHom 1).commutator (hA'.isWtHom 1)).map (Int.castRingHom ℚ)
    rwa [one_smul, one_smul] at h1
  have hCne : (A 1 * A' 1 - A' 1 * A 1).map (Int.castRingHom ℚ) ≠ 0 := by
    intro h0
    apply hC0
    ext c d
    have h1 := congrFun (congrFun h0 c) d
    rw [Matrix.map_apply, Matrix.zero_apply, eq_intCast, Int.cast_eq_zero] at h1
    rw [h1, Matrix.zero_apply]
  have hμ0 : P.root j + P.root j' ≠ 0 := by
    intro h0
    exact h (eq_neg_of_add_eq_zero_right h0)
  obtain ⟨k, hk⟩ := S.exists_root_of_isWtHom hCmem hCne hμ0 hCw
  have hCw' : IsWtHom S.wt (P.root k) ((A 1 * A' 1 - A' 1 * A 1).map (Int.castRingHom ℚ)) := by
    rw [hk]
    exact hCw
  obtain ⟨q, hq⟩ := (isRootOp_rootOp (S := S) k).exists_eq_smul hCmem hCw'
  obtain ⟨z, -, hz⟩ := exists_int_of_map_eq_smul (isRootOp_rootOp (S := S) k).prim hq
  exact ⟨k, z, hk, hz⟩

variable (S) in
/-- **Integral Chevalley data with Lie relations** constructed from integral `SL₂`-data for the
simple roots of a reduced root datum with finitely many roots. -/
def toChevalleyLieData : ChevalleyLieData P b where
  ℓ := S.ℓ
  ℓ_pos := S.ℓ_pos
  n := S.n
  wt := S.wt
  closure_range_wt := S.closure_range_wt
  e := S.rootOp
  e_zero j := (isRootOp_rootOp j).dp.zero
  e_mul j := (isRootOp_rootOp j).dp.mul
  e_eq_zero j := (isRootOp_rootOp j).dp.eq_zero
  e_weight j k := (isRootOp_rootOp j).isWtHom k
  e_one_map_ne_zero j := (isRootOp_rootOp j).prim
  φ := S.φ
  φ_natural := S.φ_natural
  φ_upper i R _ s := by rw [S.φ_upper, rootOp_simple]
  φ_lower i R _ s := by rw [S.φ_lower, rootOp_reflectionPerm_self]
  φ_diag := S.φ_diag
  weyl_weight := S.weyl_weight
  weyl_conj := weyl_conj_rootOp
  lie_e_e j j' h := lie_of_isRootOp (isRootOp_rootOp j) (isRootOp_rootOp j') h

end SimpleRootData

/-- Integral `SL₂`-data for the simple roots of a reduced root datum with finitely many roots
yield integral Chevalley data with Lie relations. -/
theorem nonempty_chevalleyLieData_of_simpleRootData [Finite J] [P.IsReduced]
    (h : Nonempty (SimpleRootData P b)) : Nonempty (ChevalleyLieData P b) :=
  h.map fun S => S.toChevalleyLieData

end Langlands.GroupScheme.SplitExistence
