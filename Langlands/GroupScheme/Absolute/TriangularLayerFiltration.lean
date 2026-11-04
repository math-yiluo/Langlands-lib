import Langlands.GroupScheme.Dynamic.GeneralLinear

/-! # The superdiagonal filtration of the upper unitriangular group -/

noncomputable section

open Matrix

namespace Langlands.GroupScheme.TriangularLayer

variable {A B : Type*} [CommRing A] [CommRing B] {N : ℕ}

/-! ### Matrices -/

/-- The matrix is upper triangular. -/
def IsUpper (X : Matrix (Fin N) (Fin N) A) : Prop :=
  ∀ i j : Fin N, j < i → X i j = 0

/-- The matrix vanishes at every position `(i, j)` with `j ≤ i + a`. -/
def IsLevel (a : ℕ) (X : Matrix (Fin N) (Fin N) A) : Prop :=
  ∀ i j : Fin N, (j : ℕ) ≤ i + a → X i j = 0

theorem isUpper_one : IsUpper (1 : Matrix (Fin N) (Fin N) A) :=
  fun _ _ h => one_apply_ne (ne_of_lt h).symm

theorem IsUpper.add {X Y : Matrix (Fin N) (Fin N) A} (hX : IsUpper X) (hY : IsUpper Y) :
    IsUpper (X + Y) := fun i j h => by rw [Matrix.add_apply, hX i j h, hY i j h, add_zero]

theorem IsLevel.isUpper {a : ℕ} {X : Matrix (Fin N) (Fin N) A} (hX : IsLevel a X) :
    IsUpper X := fun i j h => hX i j (by rw [Fin.lt_def] at h; omega)

theorem IsLevel.mono {a b : ℕ} (hab : b ≤ a) {X : Matrix (Fin N) (Fin N) A}
    (hX : IsLevel a X) : IsLevel b X := fun i j h => hX i j (by omega)

theorem isLevel_zero (a : ℕ) : IsLevel a (0 : Matrix (Fin N) (Fin N) A) := fun _ _ _ => rfl

theorem IsLevel.add {a : ℕ} {X Y : Matrix (Fin N) (Fin N) A} (hX : IsLevel a X)
    (hY : IsLevel a Y) : IsLevel a (X + Y) := fun i j h => by
  rw [Matrix.add_apply, hX i j h, hY i j h, add_zero]

theorem IsLevel.neg {a : ℕ} {X : Matrix (Fin N) (Fin N) A} (hX : IsLevel a X) :
    IsLevel a (-X) := fun i j h => by rw [Matrix.neg_apply, hX i j h, neg_zero]

theorem IsLevel.sub {a : ℕ} {X Y : Matrix (Fin N) (Fin N) A} (hX : IsLevel a X)
    (hY : IsLevel a Y) : IsLevel a (X - Y) := by
  rw [sub_eq_add_neg]
  exact hX.add hY.neg

theorem IsUpper.mul {X Y : Matrix (Fin N) (Fin N) A} (hX : IsUpper X) (hY : IsUpper Y) :
    IsUpper (X * Y) := fun i j h => by
  rw [mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l < i
  · rw [hX i l hl, zero_mul]
  · rw [hY l j (lt_of_lt_of_le h (not_lt.1 hl)), mul_zero]

theorem IsLevel.mul_isUpper {a : ℕ} {X Y : Matrix (Fin N) (Fin N) A} (hX : IsLevel a X)
    (hY : IsUpper Y) : IsLevel a (X * Y) := fun i j h => by
  rw [mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : (l : ℕ) ≤ i + a
  · rw [hX i l hl, zero_mul]
  · rw [hY l j (by rw [Fin.lt_def]; omega), mul_zero]

theorem IsUpper.mul_isLevel {a : ℕ} {X Y : Matrix (Fin N) (Fin N) A} (hY : IsUpper Y)
    (hX : IsLevel a X) : IsLevel a (Y * X) := fun i j h => by
  rw [mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l < i
  · rw [hY i l hl, zero_mul]
  · rw [Fin.lt_def] at hl
    rw [hX l j (by omega), mul_zero]

theorem IsLevel.mul {a b : ℕ} {X Y : Matrix (Fin N) (Fin N) A} (hX : IsLevel a X)
    (hY : IsLevel b Y) : IsLevel (a + b + 1) (X * Y) := fun i j h => by
  rw [mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : (l : ℕ) ≤ i + a
  · rw [hX i l hl, zero_mul]
  · rw [hY l j (by omega), mul_zero]

/-- Diagonal entries of a product of upper triangular matrices. -/
theorem IsUpper.mul_apply_self {X Y : Matrix (Fin N) (Fin N) A} (hX : IsUpper X)
    (hY : IsUpper Y) (i : Fin N) : (X * Y) i i = X i i * Y i i := by
  rw [mul_apply, Finset.sum_eq_single i]
  · intro l _ hli
    rcases lt_or_gt_of_ne hli with h | h
    · rw [hX i l h, zero_mul]
    · rw [hY l i h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem IsUpper.map {X : Matrix (Fin N) (Fin N) A} (hX : IsUpper X) (f : A →+* B) :
    IsUpper (X.map f) := fun i j h => by rw [map_apply, hX i j h, map_zero]

theorem IsLevel.map {a : ℕ} {X : Matrix (Fin N) (Fin N) A} (hX : IsLevel a X) (f : A →+* B) :
    IsLevel a (X.map f) := fun i j h => by rw [map_apply, hX i j h, map_zero]

theorem isLevel_top {X : Matrix (Fin N) (Fin N) A} (hX : IsLevel N X) : X = 0 := by
  ext i j
  exact hX i j (by omega)

/-! ### Layers -/

variable (A N) in
/-- The entries on the `(a + 1)`-st superdiagonal, all other entries replaced by zero. -/
def layer (a : ℕ) : Matrix (Fin N) (Fin N) A →+ Matrix (Fin N) (Fin N) A where
  toFun X := Matrix.of fun i j => if (j : ℕ) = i + a + 1 then X i j else 0
  map_zero' := by
    ext i j
    simp
  map_add' X Y := by
    ext i j
    simp only [of_apply, Matrix.add_apply]
    split_ifs <;> simp

theorem layer_apply (a : ℕ) (X : Matrix (Fin N) (Fin N) A) (i j : Fin N) :
    layer A N a X i j = if (j : ℕ) = i + a + 1 then X i j else 0 := rfl

theorem layer_layer (a : ℕ) (X : Matrix (Fin N) (Fin N) A) :
    layer A N a (layer A N a X) = layer A N a X := by
  ext i j
  simp only [layer_apply]
  split_ifs <;> rfl

theorem layer_map (a : ℕ) (X : Matrix (Fin N) (Fin N) A) (f : A →+* B) :
    layer B N a (X.map f) = (layer A N a X).map f := by
  ext i j
  simp only [layer_apply, map_apply]
  split_ifs <;> simp

theorem IsLevel.layer_eq_zero {a : ℕ} {X : Matrix (Fin N) (Fin N) A}
    (hX : IsLevel (a + 1) X) : layer A N a X = 0 := by
  ext i j
  rw [layer_apply]
  split_ifs with h
  · exact hX i j (by omega)
  · rfl

theorem IsLevel.succ_of_layer_eq_zero {a : ℕ} {X : Matrix (Fin N) (Fin N) A}
    (hX : IsLevel a X) (h : layer A N a X = 0) : IsLevel (a + 1) X := fun i j hij => by
  by_cases hj : (j : ℕ) ≤ i + a
  · exact hX i j hj
  · have := congrFun (congrFun h i) j
    simpa [layer_apply, show (j : ℕ) = i + a + 1 by omega] using this

variable (A N) in
/-- Multiplication of the entry at `(i, j)` by `c i i * _ * b j j`. -/
def scale (c b : Matrix (Fin N) (Fin N) A) : Matrix (Fin N) (Fin N) A →+ Matrix (Fin N) (Fin N) A where
  toFun V := Matrix.of fun i j => c i i * V i j * b j j
  map_zero' := by
    ext i j
    simp
  map_add' V W := by
    ext i j
    simp only [of_apply, Matrix.add_apply]
    ring

theorem scale_apply (c b V : Matrix (Fin N) (Fin N) A) (i j : Fin N) :
    scale A N c b V i j = c i i * V i j * b j j := rfl

theorem scale_layer (a : ℕ) (c b V : Matrix (Fin N) (Fin N) A) :
    scale A N c b (layer A N a V) = layer A N a (scale A N c b V) := by
  ext i j
  simp only [scale_apply, layer_apply]
  split_ifs <;> simp

theorem scale_eq_self {c b : Matrix (Fin N) (Fin N) A} (hc : ∀ i, c i i = 1)
    (hb : ∀ i, b i i = 1) (V : Matrix (Fin N) (Fin N) A) : scale A N c b V = V := by
  ext i j
  rw [scale_apply, hc, hb, one_mul, mul_one]

theorem scale_map (c b V : Matrix (Fin N) (Fin N) A) (f : A →+* B) :
    scale B N (c.map f) (b.map f) (V.map f) = (scale A N c b V).map f := by
  ext i j
  simp only [scale_apply, map_apply, map_mul]

theorem scale_congr {c b c' b' : Matrix (Fin N) (Fin N) A} (hc : ∀ i, c i i = c' i i)
    (hb : ∀ i, b i i = b' i i) (V : Matrix (Fin N) (Fin N) A) :
    scale A N c b V = scale A N c' b' V := by
  ext i j
  rw [scale_apply, scale_apply, hc, hb]

/-- The layer of a conjugate of a level-`a` matrix by upper triangular matrices. -/
theorem layer_mul_mul {a : ℕ} {c X b : Matrix (Fin N) (Fin N) A} (hc : IsUpper c)
    (hX : IsLevel a X) (hb : IsUpper b) :
    layer A N a (c * X * b) = scale A N c b (layer A N a X) := by
  ext i j
  rw [scale_apply, layer_apply, layer_apply]
  split_ifs with hij
  · rw [mul_apply, Finset.sum_eq_single j]
    · rw [mul_apply, Finset.sum_eq_single i]
      · intro l _ hli
        rcases lt_or_gt_of_ne hli with h | h
        · rw [hc i l h, zero_mul]
        · rw [Fin.lt_def] at h
          rw [hX l j (by omega), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
    · intro m _ hmj
      rcases lt_or_gt_of_ne hmj with h | h
      · rw [Fin.lt_def] at h
        rw [hc.mul_isLevel hX i m (by omega), zero_mul]
      · rw [hb m j h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  · simp

/-! ### The filtration of the unitriangular group -/

variable (A N) in
/-- Upper triangular invertible matrices: the block parabolic subgroup for the decreasing
weights `i ↦ -i`. -/
abbrev upper : Subgroup (GL (Fin N) A) :=
  GeneralLinear.blockParabolicSubgroup A (fun i : Fin N => -(i.val : ℤ))

theorem mem_upper {g : GL (Fin N) A} : g ∈ upper A N ↔ IsUpper (g : Matrix (Fin N) (Fin N) A) := by
  rw [GeneralLinear.mem_blockParabolicSubgroup]
  refine forall₂_congr fun i j => ?_
  rw [neg_lt_neg_iff, Nat.cast_lt, Fin.lt_def]

theorem isUpper_inv {g : GL (Fin N) A} (hg : IsUpper (g : Matrix (Fin N) (Fin N) A)) :
    IsUpper ((g⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) :=
  mem_upper.1 ((upper A N).inv_mem (mem_upper.2 hg))

/-- The diagonal entries of the inverse of an upper triangular invertible matrix. -/
theorem inv_apply_self_mul {g : GL (Fin N) A} (hg : IsUpper (g : Matrix (Fin N) (Fin N) A))
    (i : Fin N) :
    ((g⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) i i * (g : Matrix (Fin N) (Fin N) A) i i =
      1 := by
  rw [← (isUpper_inv hg).mul_apply_self hg, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    one_apply_eq]

variable (A N) in
/-- The `a`-th term of the superdiagonal filtration: `g - 1` vanishes at `(i, j)` whenever
`j ≤ i + a`. The term `a = 0` is the upper unitriangular group. -/
def W (a : ℕ) : Subgroup (GL (Fin N) A) where
  carrier := {g | IsLevel a ((g : Matrix (Fin N) (Fin N) A) - 1)}
  one_mem' := by
    change IsLevel a (((1 : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) - 1)
    rw [Units.val_one, sub_self]
    exact isLevel_zero a
  mul_mem' := by
    intro g h hg hh
    change IsLevel a ((g : Matrix (Fin N) (Fin N) A) - 1) at hg
    change IsLevel a ((h : Matrix (Fin N) (Fin N) A) - 1) at hh
    change IsLevel a (((g * h : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) - 1)
    have hu : IsUpper (h : Matrix (Fin N) (Fin N) A) := by
      simpa using hh.isUpper.add isUpper_one
    have e : ((g * h : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) - 1 =
        ((g : Matrix (Fin N) (Fin N) A) - 1) * h + ((h : Matrix (Fin N) (Fin N) A) - 1) := by
      rw [Units.val_mul, sub_mul, one_mul]
      abel
    rw [e]
    exact (hg.mul_isUpper hu).add hh
  inv_mem' := by
    intro g hg
    change IsLevel a ((g : Matrix (Fin N) (Fin N) A) - 1) at hg
    change IsLevel a (((g⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) - 1)
    have hu : IsUpper (g : Matrix (Fin N) (Fin N) A) := by
      simpa using hg.isUpper.add isUpper_one
    have e : ((g⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) - 1 =
        -(((g : Matrix (Fin N) (Fin N) A) - 1) * ((g⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A)) := by
      rw [sub_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul, neg_sub]
    rw [e]
    exact (hg.mul_isUpper (isUpper_inv hu)).neg

theorem mem_W {a : ℕ} {g : GL (Fin N) A} :
    g ∈ W A N a ↔ IsLevel a ((g : Matrix (Fin N) (Fin N) A) - 1) := Iff.rfl

theorem isUpper_of_mem_W {a : ℕ} {g : GL (Fin N) A} (hg : g ∈ W A N a) :
    IsUpper (g : Matrix (Fin N) (Fin N) A) := by
  simpa using (mem_W.1 hg).isUpper.add isUpper_one

theorem W_le_upper (a : ℕ) : W A N a ≤ upper A N := fun _ hg => mem_upper.2 (isUpper_of_mem_W hg)

theorem W_anti {a b : ℕ} (hab : a ≤ b) : W A N b ≤ W A N a := fun _ hg => (mem_W.1 hg).mono hab

theorem apply_self_of_mem_W {a : ℕ} {g : GL (Fin N) A} (hg : g ∈ W A N a) (i : Fin N) :
    (g : Matrix (Fin N) (Fin N) A) i i = 1 := by
  have h := mem_W.1 hg i i (by omega)
  rw [Matrix.sub_apply, one_apply_eq, sub_eq_zero] at h
  exact h

theorem eq_one_of_mem_W_top {g : GL (Fin N) A} (hg : g ∈ W A N N) : g = 1 := by
  apply Units.ext
  rw [Units.val_one, ← sub_eq_zero]
  exact isLevel_top (mem_W.1 hg)

theorem coe_map (f : A →+* B) (g : GL (Fin N) A) :
    ((Matrix.GeneralLinearGroup.map f g : GL (Fin N) B) : Matrix (Fin N) (Fin N) B) =
      (g : Matrix (Fin N) (Fin N) A).map f := rfl

theorem map_mem_W {a : ℕ} {g : GL (Fin N) A} (hg : g ∈ W A N a) (f : A →+* B) :
    Matrix.GeneralLinearGroup.map f g ∈ W B N a := by
  rw [mem_W, coe_map]
  have e : (g : Matrix (Fin N) (Fin N) A).map f - 1 =
      ((g : Matrix (Fin N) (Fin N) A) - 1).map f := by
    rw [Matrix.map_sub _ (map_sub f), Matrix.map_one _ (map_zero f) (map_one f)]
  rw [e]
  exact (mem_W.1 hg).map f

theorem W_conj {a : ℕ} {b g : GL (Fin N) A} (hb : b ∈ upper A N) (hg : g ∈ W A N a) :
    b⁻¹ * g * b ∈ W A N a := by
  rw [mem_W]
  have e : ((b⁻¹ * g * b : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) - 1 =
      ((b⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) *
        ((g : Matrix (Fin N) (Fin N) A) - 1) * b := by
    have h1 : ((b⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) * b = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, h1]
  rw [e]
  exact ((isUpper_inv (mem_upper.1 hb)).mul_isLevel (mem_W.1 hg)).mul_isUpper (mem_upper.1 hb)

/-- The layer of a conjugate. -/
theorem layer_conj {a : ℕ} {b g : GL (Fin N) A} (hb : b ∈ upper A N) (hg : g ∈ W A N a) :
    layer A N a (((b⁻¹ * g * b : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) - 1) =
      scale A N ((b⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) b
        (layer A N a ((g : Matrix (Fin N) (Fin N) A) - 1)) := by
  have e : ((b⁻¹ * g * b : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) - 1 =
      ((b⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) *
        ((g : Matrix (Fin N) (Fin N) A) - 1) * b := by
    have h1 : ((b⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) * b = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, h1]
  rw [e]
  exact layer_mul_mul (isUpper_inv (mem_upper.1 hb)) (mem_W.1 hg) (mem_upper.1 hb)

/-- The layer is additive on the `a`-th filtration term. -/
theorem layer_mul {a : ℕ} {g h : GL (Fin N) A} (hg : g ∈ W A N a) (hh : h ∈ W A N a) :
    layer A N a (((g * h : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) - 1) =
      layer A N a ((g : Matrix (Fin N) (Fin N) A) - 1) +
        layer A N a ((h : Matrix (Fin N) (Fin N) A) - 1) := by
  have e : ((g * h : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) - 1 =
      ((g : Matrix (Fin N) (Fin N) A) - 1) + ((h : Matrix (Fin N) (Fin N) A) - 1) +
        ((g : Matrix (Fin N) (Fin N) A) - 1) * ((h : Matrix (Fin N) (Fin N) A) - 1) := by
    rw [Units.val_mul, sub_mul, mul_sub, mul_sub, one_mul, mul_one, mul_one]
    abel
  rw [e, map_add, map_add,
    (((mem_W.1 hg).mul (mem_W.1 hh)).mono (by omega : a + 1 ≤ a + a + 1)).layer_eq_zero,
    add_zero]

theorem layer_inv {a : ℕ} {g : GL (Fin N) A} (hg : g ∈ W A N a) :
    layer A N a (((g⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) - 1) =
      -layer A N a ((g : Matrix (Fin N) (Fin N) A) - 1) := by
  have h := layer_mul hg ((W A N a).inv_mem hg)
  rw [mul_inv_cancel, Units.val_one, sub_self, map_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem mem_W_succ {a : ℕ} {g : GL (Fin N) A} (hg : g ∈ W A N a)
    (h : layer A N a ((g : Matrix (Fin N) (Fin N) A) - 1) = 0) : g ∈ W A N (a + 1) :=
  (mem_W.1 hg).succ_of_layer_eq_zero h

theorem layer_map_W (a : ℕ) (g : GL (Fin N) A) (f : A →+* B) :
    layer B N a (((Matrix.GeneralLinearGroup.map f g : GL (Fin N) B) : Matrix (Fin N) (Fin N) B) - 1) =
      (layer A N a ((g : Matrix (Fin N) (Fin N) A) - 1)).map f := by
  rw [← layer_map, coe_map, Matrix.map_sub _ (map_sub f), Matrix.map_one _ (map_zero f) (map_one f)]

/-- Conjugation by an element of the unitriangular group acts trivially on layers. -/
theorem scale_of_mem_W {a : ℕ} {u : GL (Fin N) A} (hu : u ∈ W A N a)
    (V : Matrix (Fin N) (Fin N) A) :
    scale A N ((u⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) u V = V :=
  scale_eq_self (apply_self_of_mem_W ((W A N a).inv_mem hu)) (apply_self_of_mem_W hu) V

/-! ### Layers modulo a subgroup -/

variable (𝒰 : Subgroup (GL (Fin N) A))

/-- The layers of the elements of `𝒰` lying in the `a`-th filtration term. -/
def layerGroup (a : ℕ) : AddSubgroup (Matrix (Fin N) (Fin N) A) where
  carrier := {V | ∃ w ∈ 𝒰, w ∈ W A N a ∧ layer A N a ((w : Matrix (Fin N) (Fin N) A) - 1) = V}
  zero_mem' := ⟨1, 𝒰.one_mem, (W A N a).one_mem, by rw [Units.val_one, sub_self, map_zero]⟩
  add_mem' := by
    rintro _ _ ⟨w, hw, hwa, rfl⟩ ⟨w', hw', hwa', rfl⟩
    exact ⟨w * w', 𝒰.mul_mem hw hw', (W A N a).mul_mem hwa hwa', layer_mul hwa hwa'⟩
  neg_mem' := by
    rintro _ ⟨w, hw, hwa, rfl⟩
    exact ⟨w⁻¹, 𝒰.inv_mem hw, (W A N a).inv_mem hwa, layer_inv hwa⟩

theorem mem_layerGroup {a : ℕ} {V : Matrix (Fin N) (Fin N) A} :
    V ∈ layerGroup 𝒰 a ↔
      ∃ w ∈ 𝒰, w ∈ W A N a ∧ layer A N a ((w : Matrix (Fin N) (Fin N) A) - 1) = V :=
  Iff.rfl

/-- The element lies in `𝒰 · W a`. -/
def Approx (a : ℕ) (g : GL (Fin N) A) : Prop :=
  ∃ u ∈ 𝒰, ∃ w ∈ W A N a, g = u * w

/-- The element lies in `𝒰 · W a`, and the layer of its `W a`-factor agrees with the layer of
`V` modulo the layers of `𝒰 ∩ W a`. -/
def Rel (a : ℕ) (g : GL (Fin N) A) (V : Matrix (Fin N) (Fin N) A) : Prop :=
  ∃ u ∈ 𝒰, ∃ w ∈ W A N a, g = u * w ∧
    layer A N a ((w : Matrix (Fin N) (Fin N) A) - 1) - layer A N a V ∈ layerGroup 𝒰 a

variable {𝒰}

theorem approx_of_mem_W {a : ℕ} {g : GL (Fin N) A} (hg : g ∈ W A N a) : Approx 𝒰 a g :=
  ⟨1, 𝒰.one_mem, g, hg, (one_mul g).symm⟩

theorem mem_of_approx_top {g : GL (Fin N) A} (hg : Approx 𝒰 N g) : g ∈ 𝒰 := by
  obtain ⟨u, hu, w, hw, rfl⟩ := hg
  rw [eq_one_of_mem_W_top hw, mul_one]
  exact hu

theorem Approx.rel {a : ℕ} {g : GL (Fin N) A} (hg : Approx 𝒰 a g) :
    ∃ V, Rel 𝒰 a g V := by
  obtain ⟨u, hu, w, hw, rfl⟩ := hg
  exact ⟨(w : Matrix (Fin N) (Fin N) A) - 1, u, hu, w, hw, rfl, by
    rw [sub_self]; exact (layerGroup 𝒰 a).zero_mem⟩

theorem Rel.approx {a : ℕ} {g : GL (Fin N) A} {V : Matrix (Fin N) (Fin N) A}
    (h : Rel 𝒰 a g V) : Approx 𝒰 a g := by
  obtain ⟨u, hu, w, hw, rfl, -⟩ := h
  exact ⟨u, hu, w, hw, rfl⟩

theorem rel_of_mem {a : ℕ} {u : GL (Fin N) A} (hu : u ∈ 𝒰) : Rel 𝒰 a u 0 :=
  ⟨u, hu, 1, (W A N a).one_mem, (mul_one u).symm, by
    rw [Units.val_one, sub_self, map_zero, sub_zero]; exact (layerGroup 𝒰 a).zero_mem⟩

theorem rel_of_mem_W {a : ℕ} {w : GL (Fin N) A} (hw : w ∈ W A N a) :
    Rel 𝒰 a w ((w : Matrix (Fin N) (Fin N) A) - 1) :=
  ⟨1, 𝒰.one_mem, w, hw, (one_mul w).symm, by rw [sub_self]; exact (layerGroup 𝒰 a).zero_mem⟩

theorem Rel.congr {a : ℕ} {g : GL (Fin N) A} {V V' : Matrix (Fin N) (Fin N) A}
    (h : Rel 𝒰 a g V) (hV : layer A N a V - layer A N a V' ∈ layerGroup 𝒰 a) :
    Rel 𝒰 a g V' := by
  obtain ⟨u, hu, w, hw, rfl, hl⟩ := h
  refine ⟨u, hu, w, hw, rfl, ?_⟩
  have := (layerGroup 𝒰 a).add_mem hl hV
  rwa [sub_add_sub_cancel] at this

theorem Rel.congr_layer {a : ℕ} {g : GL (Fin N) A} {V V' : Matrix (Fin N) (Fin N) A}
    (h : Rel 𝒰 a g V) (hV : layer A N a V = layer A N a V') : Rel 𝒰 a g V' :=
  h.congr (by rw [hV, sub_self]; exact (layerGroup 𝒰 a).zero_mem)

theorem Rel.mul (h𝒰 : 𝒰 ≤ W A N 0) {a : ℕ} {g h : GL (Fin N) A}
    {V V' : Matrix (Fin N) (Fin N) A} (hg : Rel 𝒰 a g V) (hh : Rel 𝒰 a h V') :
    Rel 𝒰 a (g * h) (V + V') := by
  obtain ⟨u, hu, w, hw, rfl, hl⟩ := hg
  obtain ⟨u', hu', w', hw', rfl, hl'⟩ := hh
  have hu'0 : u' ∈ W A N 0 := h𝒰 hu'
  have hc : u'⁻¹ * w * u' ∈ W A N a := W_conj (W_le_upper 0 hu'0) hw
  refine ⟨u * u', 𝒰.mul_mem hu hu', u'⁻¹ * w * u' * w', (W A N a).mul_mem hc hw', by group, ?_⟩
  rw [layer_mul hc hw', layer_conj (W_le_upper 0 hu'0) hw, scale_of_mem_W hu'0, map_add]
  have := (layerGroup 𝒰 a).add_mem hl hl'
  convert this using 1
  abel

theorem layerGroup_scale {a : ℕ} {b : GL (Fin N) A} (hb : b ∈ upper A N)
    (hb𝒰 : ∀ x ∈ 𝒰, b⁻¹ * x * b ∈ 𝒰) {V : Matrix (Fin N) (Fin N) A}
    (hV : V ∈ layerGroup 𝒰 a) :
    scale A N ((b⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) b V ∈ layerGroup 𝒰 a := by
  obtain ⟨w, hw, hwa, rfl⟩ := hV
  exact ⟨b⁻¹ * w * b, hb𝒰 w hw, W_conj hb hwa, layer_conj hb hwa⟩

theorem Rel.conj {a : ℕ} {b g : GL (Fin N) A} {V : Matrix (Fin N) (Fin N) A}
    (hb : b ∈ upper A N) (hb𝒰 : ∀ x ∈ 𝒰, b⁻¹ * x * b ∈ 𝒰) (hg : Rel 𝒰 a g V) :
    Rel 𝒰 a (b⁻¹ * g * b)
      (scale A N ((b⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) b (layer A N a V)) := by
  obtain ⟨u, hu, w, hw, rfl, hl⟩ := hg
  refine ⟨b⁻¹ * u * b, hb𝒰 u hu, b⁻¹ * w * b, W_conj hb hw, by group, ?_⟩
  rw [layer_conj hb hw, ← scale_layer, layer_layer, ← map_sub]
  exact layerGroup_scale hb hb𝒰 hl

theorem Rel.unique {a : ℕ} {g : GL (Fin N) A} {V V' : Matrix (Fin N) (Fin N) A}
    (h : Rel 𝒰 a g V) (h' : Rel 𝒰 a g V') :
    layer A N a V - layer A N a V' ∈ layerGroup 𝒰 a := by
  obtain ⟨u, hu, w, hw, hg, hl⟩ := h
  obtain ⟨u', hu', w', hw', hg', hl'⟩ := h'
  have hz : w' * w⁻¹ = u'⁻¹ * u := by
    rw [hg] at hg'
    calc w' * w⁻¹ = u'⁻¹ * (u' * w') * w⁻¹ := by group
      _ = u'⁻¹ * (u * w) * w⁻¹ := by rw [hg']
      _ = u'⁻¹ * u := by group
  have hzU : w' * w⁻¹ ∈ 𝒰 := hz ▸ 𝒰.mul_mem (𝒰.inv_mem hu') hu
  have hzW : w' * w⁻¹ ∈ W A N a := (W A N a).mul_mem hw' ((W A N a).inv_mem hw)
  have hzl : layer A N a (((w' * w⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) - 1) ∈
      layerGroup 𝒰 a := ⟨_, hzU, hzW, rfl⟩
  rw [layer_mul hw' ((W A N a).inv_mem hw), layer_inv hw] at hzl
  have := (layerGroup 𝒰 a).sub_mem ((layerGroup 𝒰 a).sub_mem hl' hl) hzl
  convert this using 1
  abel

theorem Rel.approx_succ {a : ℕ} {g : GL (Fin N) A} {V : Matrix (Fin N) (Fin N) A}
    (h : Rel 𝒰 a g V) (hV : layer A N a V ∈ layerGroup 𝒰 a) : Approx 𝒰 (a + 1) g := by
  obtain ⟨u, hu, w, hw, rfl, hl⟩ := h
  obtain ⟨w₀, hw₀, hw₀a, he⟩ := (layerGroup 𝒰 a).add_mem hl hV
  rw [sub_add_cancel] at he
  refine ⟨u * w₀, 𝒰.mul_mem hu hw₀, w₀⁻¹ * w, ?_, by group⟩
  apply mem_W_succ ((W A N a).mul_mem ((W A N a).inv_mem hw₀a) hw)
  rw [layer_mul ((W A N a).inv_mem hw₀a) hw, layer_inv hw₀a, he, neg_add_cancel]

theorem layerGroup_map {𝒰' : Subgroup (GL (Fin N) B)} (f : A →+* B)
    (hf : ∀ x ∈ 𝒰, Matrix.GeneralLinearGroup.map f x ∈ 𝒰') {a : ℕ}
    {V : Matrix (Fin N) (Fin N) A} (hV : V ∈ layerGroup 𝒰 a) : V.map f ∈ layerGroup 𝒰' a := by
  obtain ⟨w, hw, hwa, rfl⟩ := hV
  exact ⟨_, hf w hw, map_mem_W hwa f, layer_map_W a w f⟩

theorem Rel.map {𝒰' : Subgroup (GL (Fin N) B)} (f : A →+* B)
    (hf : ∀ x ∈ 𝒰, Matrix.GeneralLinearGroup.map f x ∈ 𝒰') {a : ℕ} {g : GL (Fin N) A}
    {V : Matrix (Fin N) (Fin N) A} (h : Rel 𝒰 a g V) :
    Rel 𝒰' a (Matrix.GeneralLinearGroup.map f g) (V.map f) := by
  obtain ⟨u, hu, w, hw, rfl, hl⟩ := h
  refine ⟨_, hf u hu, _, map_mem_W hw f, map_mul _ u w, ?_⟩
  rw [layer_map_W, layer_map, ← Matrix.map_sub _ (map_sub f)]
  exact layerGroup_map f hf hl

end Langlands.GroupScheme.TriangularLayer
