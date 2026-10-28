import Langlands.Representation.Classification.ProductLeviTemperedSufficiencyProof
import Langlands.Group.GL.CartanCellCountProof

/-!
# Disjoint cells below a diagonal uniformizer element

For a subset `S` of the coordinates of one block, the matrices supported on the
rows in `S` and the columns outside `S` form an abelian unipotent group.
Conjugating it by the diagonal element with the uniformizer on `S` and `1`
elsewhere divides its entries by the uniformizer. Translating the cell of the
`M`-th power of a product-Levi element `g` with this block by the unipotent
elements with uniformizer-digit entries of length `m` gives
`q ^ (m |S| |Sᶜ|)` disjoint translates modulo the centre. This bounds the
integral of a function constant on these translates from below.
-/

noncomputable section

open scoped BigOperators ENNReal Topology

namespace Langlands.ProductLeviNecessity

open GeneralLinear MeasureTheory

universe uF

/-! ### Off-diagonal unipotent matrices -/

section Unipotent

variable {R : Type*} [CommRing R] {N : ℕ} (S : Finset (Fin N))

/-- The index pairs `(a, b)` with `a ∈ S` and `b ∉ S`. -/
abbrev Pairs := {x : Fin N × Fin N // x.1 ∈ S ∧ x.2 ∉ S}

theorem card_pairs : Fintype.card (Pairs S) = S.card * Sᶜ.card := by
  classical
  rw [Fintype.card_subtype, ← Finset.card_product]
  congr 1
  ext x
  simp

/-- The matrix with the entries of `X` at the positions in `Pairs S`. -/
def offMatrix (X : Pairs S → R) : Matrix (Fin N) (Fin N) R :=
  fun a b => if h : a ∈ S ∧ b ∉ S then X ⟨(a, b), h⟩ else 0

theorem offMatrix_mul (X Y : Pairs S → R) : offMatrix S X * offMatrix S Y = 0 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hc : c ∈ S
  · simp [offMatrix, hc]
  · simp [offMatrix, hc]

theorem offMatrix_add (X Y : Pairs S → R) :
    offMatrix S (X + Y) = offMatrix S X + offMatrix S Y := by
  ext a b
  simp only [offMatrix, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

theorem offMatrix_zero : offMatrix S (0 : Pairs S → R) = 0 := by
  ext a b
  simp [offMatrix]

theorem offMatrix_apply_self (X : Pairs S → R) (a : Fin N) : offMatrix S X a a = 0 := by
  simp only [offMatrix]
  split_ifs with h
  · exact absurd h.1 h.2
  · rfl

/-- The unipotent element `1 + offMatrix S X`. -/
def unip (X : Pairs S → R) : GeneralLinear N R :=
  ⟨1 + offMatrix S X, 1 - offMatrix S X,
    by simp only [add_mul, mul_sub, one_mul, mul_one, offMatrix_mul]; abel,
    by simp only [sub_mul, mul_add, one_mul, mul_one, offMatrix_mul, sub_zero]; abel⟩

theorem unip_val (X : Pairs S → R) : (unip S X : Matrix (Fin N) (Fin N) R) = 1 + offMatrix S X :=
  rfl

theorem unip_inv_val (X : Pairs S → R) :
    ((unip S X)⁻¹ : GeneralLinear N R).val = 1 - offMatrix S X :=
  rfl

theorem unip_add (X Y : Pairs S → R) : unip S (X + Y) = unip S X * unip S Y := by
  ext : 1
  simp only [Units.val_mul, unip_val, offMatrix_add, add_mul, mul_add, one_mul, mul_one,
    offMatrix_mul]
  abel

theorem unip_zero : unip S (0 : Pairs S → R) = 1 := by
  ext : 1
  simp [unip_val, offMatrix_zero]

theorem unip_neg (X : Pairs S → R) : unip S (-X) = (unip S X)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← unip_add, neg_add_cancel, unip_zero]

theorem unip_inv_mul (X Y : Pairs S → R) : (unip S X)⁻¹ * unip S Y = unip S (Y - X) := by
  rw [← unip_neg, ← unip_add, neg_add_eq_sub]

/-- Conjugating by the diagonal element with `τ` on `S` divides the entries by `τ`. -/
theorem unip_mul_diagonal (τ : Rˣ) {d : GeneralLinear N R}
    (hd : (d : Matrix (Fin N) (Fin N) R) = Matrix.diagonal (fun a => if a ∈ S then (τ : R) else 1))
    (X : Pairs S → R) :
    unip S X * d = d * unip S (fun x => ((τ⁻¹ : Rˣ) : R) * X x) := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [Units.val_mul, Units.val_mul, unip_val, unip_val, hd, add_mul, mul_add, one_mul, mul_one,
    Matrix.add_apply, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  congr 1
  simp only [offMatrix]
  by_cases h : a ∈ S ∧ b ∉ S
  · simp only [h.1, h.2, not_false_eq_true, and_self, ↓reduceDIte, ↓reduceIte, mul_one]
    rw [← mul_assoc, Units.mul_inv, one_mul]
  · simp only [h, ↓reduceDIte, zero_mul, mul_zero]

theorem inv_mul_unip_mul (τ : Rˣ) {d : GeneralLinear N R}
    (hd : (d : Matrix (Fin N) (Fin N) R) = Matrix.diagonal (fun a => if a ∈ S then (τ : R) else 1))
    (X : Pairs S → R) :
    d⁻¹ * unip S X * d = unip S (fun x => ((τ⁻¹ : Rˣ) : R) * X x) := by
  rw [mul_assoc, unip_mul_diagonal S τ hd, inv_mul_cancel_left]

end Unipotent

theorem offMatrix_apply_pairs {R : Type*} [CommRing R] {N : ℕ} (S : Finset (Fin N))
    (X : Pairs S → R) (x : Pairs S) : offMatrix S X x.1.1 x.1.2 = X x := by
  simp only [offMatrix, x.2.1, x.2.2, not_false_eq_true, and_self, ↓reduceDIte]

/-! ### Integrality modulo the centre -/

section Integral

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable {N : ℕ} (S : Finset (Fin N))

/-- A unipotent element in the integral subgroup times the centre has integral
entries. -/
theorem le_one_of_unip_eq {Y : Pairs S → F.Carrier} {k s : GeneralLinear N F.Carrier}
    (hk : k ∈ CartanQuotient.maximalCompact T N)
    (hs : s ∈ Subgroup.center (GeneralLinear N F.Carrier))
    (h : unip S Y = k * s) (x : Pairs S) : T.discreteValuation (Y x) ≤ 1 := by
  obtain ⟨c, hc⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hs
  have hk' := (CartanQuotient.CellCount.mem_maximalCompact_iff k).mp hk
  have hkinv : k⁻¹ = s * unip S (-Y) := by
    rw [unip_neg, h, mul_inv_rev, mul_inv_cancel_left]
  have hc1 : T.discreteValuation c ≤ 1 := by
    have h1 := hk'.2 x.1.1 x.1.1
    rwa [hkinv, Units.val_mul, ← hc, unip_val, Matrix.scalar_apply, Matrix.diagonal_mul,
      Matrix.add_apply, Matrix.one_apply_eq, offMatrix_apply_self, add_zero, mul_one] at h1
  have hab : x.1.1 ≠ x.1.2 := fun e => x.2.2 (e ▸ x.2.1)
  have hY : Y x = (k : Matrix (Fin N) (Fin N) F.Carrier) x.1.1 x.1.2 * c := by
    have h2 := congrArg
      (fun g : GeneralLinear N F.Carrier => (g : Matrix (Fin N) (Fin N) F.Carrier) x.1.1 x.1.2) h
    simp only [unip_val, Units.val_mul, ← hc, Matrix.scalar_apply, Matrix.mul_diagonal,
      Matrix.add_apply, Matrix.one_apply_ne hab, zero_add, offMatrix_apply_pairs] at h2
    exact h2
  rw [hY, map_mul]
  exact mul_le_one' (hk'.1 _ _) hc1

end Integral

/-! ### Uniformizer digits -/

section Digits

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

open CartanQuotient.CellCount

/-- An integral lift of a residue class. -/
def residueLift (r : T.ResidueField) : F.Carrier :=
  ((IsLocalRing.residue_surjective r).choose : F.Carrier)

theorem residueLift_le_one (r : T.ResidueField) :
    T.discreteValuation (residueLift T r) ≤ 1 :=
  (T.mem_integers_iff_discreteValuation_le_one _).mp
    (IsLocalRing.residue_surjective r).choose.2

theorem res_residueLift (r : T.ResidueField) : res T (residueLift T r) = r := by
  rw [residueLift, res_of_mem (IsLocalRing.residue_surjective r).choose.2]
  exact (IsLocalRing.residue_surjective r).choose_spec

/-- The element `∑ s, ϖ ^ s · lift (δ s)` with residue digits `δ`. -/
def digitVal {m : ℕ} (δ : Fin m → T.ResidueField) : F.Carrier :=
  ∑ s : Fin m, T.uniformizer ^ (s : ℕ) * residueLift T (δ s)

theorem uniformizer_pow_le_one (t : ℕ) : T.discreteValuation (T.uniformizer ^ t) ≤ 1 := by
  rw [map_pow, T.discreteValuation_uniformizer]
  exact pow_le_one' (WithZero.exp_le_one_iff.mpr (by norm_num)) _

theorem digitVal_le_one {m : ℕ} (δ : Fin m → T.ResidueField) :
    T.discreteValuation (digitVal T δ) ≤ 1 := by
  refine T.discreteValuation.map_sum_le fun s _ => ?_
  rw [map_mul]
  exact mul_le_one' (uniformizer_pow_le_one T _) (residueLift_le_one T _)

theorem digitVal_succ {m : ℕ} (δ : Fin (m + 1) → T.ResidueField) :
    digitVal T δ = residueLift T (δ 0) + T.uniformizer * digitVal T (fun s => δ s.succ) := by
  rw [digitVal, Fin.sum_univ_succ, digitVal, Finset.mul_sum]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ]
  congr 1
  exact Finset.sum_congr rfl fun s _ => by ring

variable {T}

theorem level_of_uniformizer_pow_mul {e : ℤ} {x : F.Carrier} (t : ℕ)
    (h : Level T e (T.uniformizer ^ t * x)) : Level T (e - t) x := by
  have h' := (level_uniformizer_mul_iff (T := T) e (-(t : ℤ)) x).mp (by simpa using h)
  rwa [← sub_eq_add_neg] at h'

theorem level_one_uniformizer_mul {x : F.Carrier} (hx : T.discreteValuation x ≤ 1) :
    Level T 1 (T.uniformizer * x) := by
  rw [Level, map_mul, T.discreteValuation_uniformizer]
  exact mul_le_of_le_one_right' hx

variable (T)

/-- Digit expansions of length `m` that agree to level `m` are equal. -/
theorem eq_of_level_digitVal_sub : ∀ {m : ℕ} (δ δ' : Fin m → T.ResidueField),
    Level T m (digitVal T δ' - digitVal T δ) → δ = δ'
  | 0, δ, δ', _ => Subsingleton.elim _ _
  | m + 1, δ, δ', h => by
    rw [digitVal_succ, digitVal_succ] at h
    set A := residueLift T (δ' 0) - residueLift T (δ 0)
    set W := digitVal T (fun s => δ' s.succ) - digitVal T (fun s => δ s.succ)
    have hsplit : residueLift T (δ' 0) + T.uniformizer * digitVal T (fun s => δ' s.succ) -
        (residueLift T (δ 0) + T.uniformizer * digitVal T (fun s => δ s.succ)) =
          A + T.uniformizer * W := by
      simp only [A, W]
      ring
    rw [hsplit] at h
    have hW1 : T.discreteValuation W ≤ 1 :=
      (T.discreteValuation.map_sub _ _).trans (max_le (digitVal_le_one T _) (digitVal_le_one T _))
    have hA : Level T 1 A := by
      have h1 : Level T 1 (A + T.uniformizer * W) := h.mono (by push_cast; omega)
      simpa using h1.sub (level_one_uniformizer_mul hW1)
    have h0 : δ 0 = δ' 0 := by
      rw [← res_residueLift T (δ 0), ← res_residueLift T (δ' 0)]
      have hA1 : T.discreteValuation A ≤ 1 := hA.le_one zero_le_one
      have hres := (res_eq_zero_iff hA1).mpr hA
      have hsum : res T (residueLift T (δ' 0)) = res T A + res T (residueLift T (δ 0)) := by
        rw [← res_add hA1 (residueLift_le_one T _)]
        simp only [A, sub_add_cancel]
      rw [hsum, hres, zero_add]
    have hA0 : A = 0 := by simp only [A, h0, sub_self]
    rw [hA0, zero_add] at h
    have hW : Level T m W := by
      have h1 := level_of_uniformizer_pow_mul 1 (by simpa using h)
      rwa [Nat.cast_one, add_sub_cancel_right] at h1
    have htail := eq_of_level_digitVal_sub (fun s => δ s.succ) (fun s => δ' s.succ) hW
    funext s
    refine Fin.cases h0 (fun s => congrFun htail s) s

end Digits

/-! ### Small unipotent elements -/

section Small

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable {n : ℕ} (C : BlockShape n)

open CartanQuotient.CellCount

theorem level_uniformizer_pow_mul (t : ℕ) {x : F.Carrier} (hx : T.discreteValuation x ≤ 1) :
    Level T t (T.uniformizer ^ t * x) := by
  have h := (level_uniformizer_mul_iff (T := T) (t : ℤ) (-(t : ℤ)) x).mpr
    (by simpa [Level] using hx)
  simpa using h

theorem continuous_unip {N : ℕ} (S : Finset (Fin N)) :
    letI := T.topology
    Continuous (unip S : (Pairs S → F.Carrier) → GeneralLinear N F.Carrier) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hoff : Continuous
      (offMatrix S : (Pairs S → F.Carrier) → Matrix (Fin N) (Fin N) F.Carrier) := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [offMatrix]
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
  exact Units.continuous_iff.mpr ⟨continuous_const.add hoff, continuous_const.sub hoff⟩

/-- Unipotent elements with entries in a small enough lattice lie in a given open
subgroup of the product Levi. -/
theorem exists_unip_mem (j : Fin C.length) (S : Finset (Fin (C.size j))) :
    letI := T.topology
    ∀ K : OpenSubgroup (C.Levi F.Carrier), ∃ t : ℕ, ∀ X : Pairs S → F.Carrier,
      (∀ x, T.discreteValuation (X x) ≤ 1) →
        (Pi.mulSingle j (unip S (fun x => T.uniformizer ^ t * X x)) : C.Levi F.Carrier) ∈ K := by
  let := T.topology
  intro K
  have hcont : Continuous fun X : Pairs S → F.Carrier =>
      (Pi.mulSingle j (unip S X) : C.Levi F.Carrier) :=
    (continuous_mulSingle j).comp (continuous_unip T S)
  have hmem : (fun X : Pairs S → F.Carrier => (Pi.mulSingle j (unip S X) : C.Levi F.Carrier)) ⁻¹'
      (K : Set (C.Levi F.Carrier)) ∈ 𝓝 (0 : Pairs S → F.Carrier) := by
    refine hcont.continuousAt.preimage_mem_nhds ?_
    rw [unip_zero, Pi.mulSingle_one]
    exact K.isOpen.mem_nhds K.one_mem
  rw [nhds_pi, Filter.mem_pi'] at hmem
  obtain ⟨I, u, hu, hsub⟩ := hmem
  choose e he using fun x => T.exists_additiveLattice_subset (hu x)
  refine ⟨∑ x, (e x).natAbs, fun X hX => hsub fun x _ => he x ?_⟩
  have hle : -(((∑ x, (e x).natAbs : ℕ)) : ℤ) ≤ e x := by
    have h1 : (e x).natAbs ≤ ∑ x, (e x).natAbs :=
      Finset.single_le_sum (f := fun x => (e x).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ x)
    have h2 := neg_abs_le (e x)
    rw [← Int.natCast_natAbs] at h2
    have h3 : ((e x).natAbs : ℤ) ≤ ((∑ x, (e x).natAbs : ℕ) : ℤ) := by exact_mod_cast h1
    omega
  rw [SetLike.mem_coe, PadicField.TopologicalData.mem_additiveLattice]
  exact (level_uniformizer_pow_mul T _ (hX x)).trans (WithZero.exp_le_exp.mpr hle)

end Small

/-! ### Disjointness of the cells -/

section Disjoint

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable {n : ℕ} (C : BlockShape n)

open CartanQuotient.CellCount

theorem pow_apply_val_eq_diagonal (j : Fin C.length) (S : Finset (Fin (C.size j)))
    {g : C.Levi F.Carrier}
    (hg : (g j : Matrix (Fin (C.size j)) (Fin (C.size j)) F.Carrier) =
      Matrix.diagonal (fun a => if a ∈ S then T.uniformizer else 1)) (M : ℕ) :
    ((g ^ M) j : Matrix (Fin (C.size j)) (Fin (C.size j)) F.Carrier) =
      Matrix.diagonal (fun a => if a ∈ S then
        ((LocalFactor.PadicAbelian.uniformizerUnit T ^ M : F.Carrierˣ) : F.Carrier) else 1) := by
  rw [Pi.pow_apply, Units.val_pow_eq_pow_val, hg, Matrix.diagonal_pow]
  congr 1
  funext a
  simp only [Pi.pow_apply]
  split_ifs <;> simp

/-- Two translated cells with the same image modulo the centre have unipotent
coordinates agreeing to level `M`. -/
theorem level_of_mk_eq (j : Fin C.length) (S : Finset (Fin (C.size j))) {g : C.Levi F.Carrier}
    (hg : (g j : Matrix (Fin (C.size j)) (Fin (C.size j)) F.Carrier) =
      Matrix.diagonal (fun a => if a ∈ S then T.uniformizer else 1)) (M : ℕ)
    {Y Y' : Pairs S → F.Carrier} {k k' : C.Levi F.Carrier}
    (hk : k j ∈ CartanQuotient.maximalCompact T (C.size j))
    (hk' : k' j ∈ CartanQuotient.maximalCompact T (C.size j))
    (h : (QuotientGroup.mk (Pi.mulSingle j (unip S Y) * g ^ M * k) :
        C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)) =
      QuotientGroup.mk (Pi.mulSingle j (unip S Y') * g ^ M * k')) (x : Pairs S) :
    Level T M (Y' x - Y x) := by
  have hc := QuotientGroup.eq.mp h
  rw [Subgroup.center_pi, Subgroup.mem_pi] at hc
  have hj := hc j (Set.mem_univ j)
  simp only [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_same] at hj
  have hd := pow_apply_val_eq_diagonal T C j S hg M
  set d := (g ^ M) j
  set s := (unip S Y * d * k j)⁻¹ * (unip S Y' * d * k' j) with hs_def
  have hconj := inv_mul_unip_mul S (LocalFactor.PadicAbelian.uniformizerUnit T ^ M) hd (Y' - Y)
  have hU : unip S (fun x => (((LocalFactor.PadicAbelian.uniformizerUnit T ^ M)⁻¹ :
      F.Carrierˣ) : F.Carrier) * (Y' - Y) x) = (k j * (k' j)⁻¹) * s := by
    rw [← hconj, ← unip_inv_mul, mul_assoc (k j), Subgroup.mem_center_iff.mp hj ((k' j)⁻¹),
      hs_def]
    group
  have hint := le_one_of_unip_eq T S (mul_mem hk (inv_mem hk')) hj hU x
  have h0 : Level T 0 (((LocalFactor.PadicAbelian.uniformizerUnit T ^ (-(M : ℤ)) :
      F.Carrierˣ) : F.Carrier) * (Y' x - Y x)) := by
    rw [level_zero_iff, zpow_neg, zpow_natCast]
    simpa using hint
  simpa using (level_uniformizer_mul_iff 0 (M : ℤ) _).mp h0

end Disjoint

/-! ### Lower bound for an integral over disjoint translates -/

section Measure

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (Z : Subgroup G)
  [Z.Normal] [MeasurableSpace (G ⧸ Z)] [BorelSpace (G ⧸ Z)] (μ : Measure (G ⧸ Z))
  [μ.IsMulLeftInvariant]

/-- Pairwise disjoint left translates of the image of an open set, on which a
function is bounded below by `a`, bound its integral below. -/
theorem card_mul_le_lintegral {ι : Type*} [Fintype ι] (h : ι → G) {K : Set G} (hK : IsOpen K)
    (hdisj : Pairwise fun i i' =>
      Disjoint ((fun q => (h i : G ⧸ Z) * q) '' ((↑) '' K))
        ((fun q => (h i' : G ⧸ Z) * q) '' ((↑) '' K)))
    (f : G ⧸ Z → ℝ≥0∞) (a : ℝ≥0∞) (hf : ∀ i, ∀ k ∈ K, a ≤ f ((h i * k : G) : G ⧸ Z)) :
    (Fintype.card ι : ℝ≥0∞) * (a * μ ((↑) '' K)) ≤ ∫⁻ q, f q ∂μ := by
  set s : ι → Set (G ⧸ Z) := fun i => (fun q => (h i : G ⧸ Z) * q) '' ((↑) '' K)
  have hopen0 : IsOpen ((↑) '' K : Set (G ⧸ Z)) := QuotientGroup.isOpenMap_coe K hK
  have hopen : ∀ i, IsOpen (s i) := fun i => isOpenMap_mul_left _ _ hopen0
  have hmeas : ∀ i, μ (s i) = μ ((↑) '' K) := by
    intro i
    simp only [s, Set.image_mul_left]
    exact measure_preimage_mul μ _ _
  calc (Fintype.card ι : ℝ≥0∞) * (a * μ ((↑) '' K)) = ∑ i, ∫⁻ _ in s i, a ∂μ := by
        simp only [setLIntegral_const, hmeas, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ ∑ i, ∫⁻ q in s i, f q ∂μ := by
        refine Finset.sum_le_sum fun i _ => setLIntegral_mono' (hopen i).measurableSet ?_
        rintro q ⟨_, ⟨k, hk, rfl⟩, rfl⟩
        simpa only [QuotientGroup.mk_mul] using hf i k hk
    _ = ∫⁻ q in ⋃ i, s i, f q ∂μ := by
        rw [lintegral_iUnion (fun i => (hopen i).measurableSet) hdisj, tsum_fintype]
    _ ≤ ∫⁻ q, f q ∂μ := setLIntegral_le_lintegral _ _

end Measure

/-! ### The cell lower bound -/

section Lower

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable {n : ℕ} (C : BlockShape n)

/-- A function on the central quotient bounded below by `F0 M` on the images of
`u * g ^ M * k` with `u, k` in an open subgroup `KP` of the integral product
Levi has integral at least `q ^ (m |S| |Sᶜ|) F0 (m + t) μ(KP)` for a fixed `t`
and every `m`, when the `j`-th block of `g` is diagonal with the uniformizer on
`S` and `1` elsewhere. -/
theorem cells_lower_bound (j : Fin C.length) (S : Finset (Fin (C.size j)))
    {g : C.Levi F.Carrier}
    (hg : (g j : Matrix (Fin (C.size j)) (Fin (C.size j)) F.Carrier) =
      Matrix.diagonal (fun a => if a ∈ S then T.uniformizer else 1)) :
    letI := T.topology
    letI := T.leviTopologicalGroup C
    ∀ (KP : OpenSubgroup (C.Levi F.Carrier)),
      (KP : Set (C.Levi F.Carrier)) ⊆ ProductLeviTempered.integralLevi T C →
      ∀ [MeasurableSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier))]
        [BorelSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier))]
        (μ : Measure (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)))
        [μ.IsMulLeftInvariant]
        (f : C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier) → ℝ≥0∞) (F0 : ℕ → ℝ≥0∞),
        (∀ M : ℕ, ∀ u ∈ KP, ∀ k ∈ KP, F0 M ≤ f (QuotientGroup.mk (u * g ^ M * k))) →
        ∃ t : ℕ, ∀ m : ℕ,
          (T.residueCardinality : ℝ≥0∞) ^ (m * (S.card * Sᶜ.card)) *
              (F0 (m + t) * μ (QuotientGroup.mk '' (KP : Set (C.Levi F.Carrier)))) ≤
            ∫⁻ q, f q ∂μ := by
  let := T.topology
  let := T.leviTopologicalGroup C
  intro KP hKP _ _ μ _ f F0 hf
  obtain ⟨t, ht⟩ := exists_unip_mem T C j S KP
  refine ⟨t, fun m => ?_⟩
  classical
  have := T.finite_residueField
  let := Fintype.ofFinite T.ResidueField
  let h : (Pairs S → Fin m → T.ResidueField) → C.Levi F.Carrier := fun δ =>
    Pi.mulSingle j (unip S (fun x => T.uniformizer ^ t * digitVal T (δ x))) * g ^ (m + t)
  have hcard : (Fintype.card (Pairs S → Fin m → T.ResidueField) : ℝ≥0∞) =
      (T.residueCardinality : ℝ≥0∞) ^ (m * (S.card * Sᶜ.card)) := by
    rw [Fintype.card_fun, Fintype.card_fun, card_pairs,
      PadicField.TopologicalData.residueCardinality, Nat.card_eq_fintype_card, ← pow_mul,
      Fintype.card_fin]
    push_cast
    rfl
  rw [← hcard]
  refine card_mul_le_lintegral (Subgroup.center (C.Levi F.Carrier)) μ h KP.isOpen ?_ f
    (F0 (m + t)) ?_
  · intro δ δ' hne
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩ ⟨_, ⟨k', hk', rfl⟩, he⟩
    apply hne
    have hkj := (ProductLeviTempered.mem_integralLevi T C k).mp (hKP hk) j
    have hk'j := (ProductLeviTempered.mem_integralLevi T C k').mp (hKP hk') j
    have heq : (QuotientGroup.mk (h δ * k) :
        C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)) = QuotientGroup.mk (h δ' * k') := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      exact he.symm
    funext x
    have hl := level_of_mk_eq T C j S hg (m + t) hkj hk'j heq x
    rw [← mul_sub] at hl
    have hl' := level_of_uniformizer_pow_mul t hl
    have hm : ((m + t : ℕ) : ℤ) - (t : ℤ) = (m : ℤ) := by push_cast; ring
    rw [hm] at hl'
    exact eq_of_level_digitVal_sub T _ _ hl'
  · intro δ k hk
    exact hf (m + t) _ (ht _ fun x => digitVal_le_one T _) k hk

end Lower

end Langlands.ProductLeviNecessity
