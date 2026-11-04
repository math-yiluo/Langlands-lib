import Langlands.GroupScheme.Absolute.TriangularLayerFiltration

/-! # Coordinate refinement of the unitriangular superdiagonal filtration -/

noncomputable section

open Matrix

namespace Langlands.GroupScheme.TriangularLayer

variable {A B : Type*} [CommRing A] [CommRing B] {N : ℕ}

/-- All rows with index below `b` vanish. Applied to one superdiagonal layer,
this imposes one coordinate equation per such row. -/
def ZeroBefore (b : ℕ) (X : Matrix (Fin N) (Fin N) A) : Prop :=
  ∀ i j : Fin N, (i : ℕ) < b → X i j = 0

theorem zeroBefore_zero (b : ℕ) : ZeroBefore b (0 : Matrix (Fin N) (Fin N) A) :=
  fun _ _ _ => rfl

theorem ZeroBefore.add {b : ℕ} {X Y : Matrix (Fin N) (Fin N) A}
    (hX : ZeroBefore b X) (hY : ZeroBefore b Y) : ZeroBefore b (X + Y) := by
  intro i j hi
  rw [Matrix.add_apply, hX i j hi, hY i j hi, add_zero]

theorem ZeroBefore.neg {b : ℕ} {X : Matrix (Fin N) (Fin N) A}
    (hX : ZeroBefore b X) : ZeroBefore b (-X) := by
  intro i j hi
  rw [Matrix.neg_apply, hX i j hi, neg_zero]

theorem ZeroBefore.mono {b c : ℕ} (hbc : b ≤ c)
    {X : Matrix (Fin N) (Fin N) A} (hX : ZeroBefore c X) : ZeroBefore b X :=
  fun i j hi => hX i j (lt_of_lt_of_le hi hbc)

theorem ZeroBefore.scale {b : ℕ} {X : Matrix (Fin N) (Fin N) A}
    (hX : ZeroBefore b X) (c d : Matrix (Fin N) (Fin N) A) :
    ZeroBefore b (scale A N c d X) := by
  intro i j hi
  rw [scale_apply, hX i j hi, mul_zero, zero_mul]

theorem ZeroBefore.map {b : ℕ} {X : Matrix (Fin N) (Fin N) A}
    (hX : ZeroBefore b X) (f : A →+* B) : ZeroBefore b (X.map f) := by
  intro i j hi
  rw [Matrix.map_apply, hX i j hi, map_zero]

variable (A N) in
/-- Refine `W a` by killing the first `b` entries on its next superdiagonal.
The equations are imposed over the original coefficient ring. -/
def refinedW (a b : ℕ) : Subgroup (GL (Fin N) A) where
  carrier := {g | g ∈ W A N a ∧
    ZeroBefore b (layer A N a ((g : Matrix (Fin N) (Fin N) A) - 1))}
  one_mem' := by
    refine ⟨(W A N a).one_mem, ?_⟩
    rw [Units.val_one, sub_self, map_zero]
    exact zeroBefore_zero b
  mul_mem' := by
    rintro g h ⟨hg, hgz⟩ ⟨hh, hhz⟩
    refine ⟨(W A N a).mul_mem hg hh, ?_⟩
    rw [layer_mul hg hh]
    exact hgz.add hhz
  inv_mem' := by
    rintro g ⟨hg, hgz⟩
    refine ⟨(W A N a).inv_mem hg, ?_⟩
    rw [layer_inv hg]
    exact hgz.neg

theorem mem_refinedW {a b : ℕ} {g : GL (Fin N) A} :
    g ∈ refinedW A N a b ↔ g ∈ W A N a ∧
      ZeroBefore b (layer A N a ((g : Matrix (Fin N) (Fin N) A) - 1)) :=
  Iff.rfl

theorem refinedW_le_W (a b : ℕ) : refinedW A N a b ≤ W A N a :=
  fun _ h => h.1

theorem refinedW_anti (a : ℕ) {b c : ℕ} (hbc : b ≤ c) :
    refinedW A N a c ≤ refinedW A N a b :=
  fun _ h => ⟨h.1, h.2.mono hbc⟩

@[simp]
theorem refinedW_zero (a : ℕ) : refinedW A N a 0 = W A N a := by
  ext g
  exact ⟨fun h => h.1, fun h => ⟨h, fun _ _ hi => by omega⟩⟩

/-- After all rows of a layer have been killed, the next superdiagonal
filtration term is reached. -/
@[simp]
theorem refinedW_top (a : ℕ) : refinedW A N a N = W A N (a + 1) := by
  ext g
  constructor
  · rintro ⟨hg, hz⟩
    apply mem_W_succ hg
    ext i j
    exact hz i j i.isLt
  · intro hg
    refine ⟨W_anti (by omega : a ≤ a + 1) hg, ?_⟩
    rw [(mem_W.1 hg).layer_eq_zero]
    exact zeroBefore_zero N

/-- Each refined term is invariant under conjugation by all upper triangular
invertible matrices. -/
theorem refinedW_conj {a b : ℕ} {c g : GL (Fin N) A}
    (hc : c ∈ upper A N) (hg : g ∈ refinedW A N a b) :
    c⁻¹ * g * c ∈ refinedW A N a b := by
  refine ⟨W_conj hc hg.1, ?_⟩
  rw [layer_conj hc hg.1]
  exact hg.2.scale _ _

theorem map_mem_refinedW {a b : ℕ} {g : GL (Fin N) A}
    (hg : g ∈ refinedW A N a b) (f : A →+* B) :
    Matrix.GeneralLinearGroup.map f g ∈ refinedW B N a b := by
  refine ⟨map_mem_W hg.1 f, ?_⟩
  rw [layer_map_W]
  exact hg.2.map f

variable (A N) in
/-- A coordinate on the `a`-th layer, as an additive character of `W a`.
Only coordinates lying on the `(a + 1)`-st superdiagonal can be nonzero. -/
def layerCoordinate (a : ℕ) (i j : Fin N) : W A N a →* Multiplicative A where
  toFun g := Multiplicative.ofAdd
    (layer A N a ((g.val : Matrix (Fin N) (Fin N) A) - 1) i j)
  map_one' := by
    apply Multiplicative.toAdd.injective
    simp
  map_mul' g h := by
    apply Multiplicative.toAdd.injective
    exact congrFun (congrFun (layer_mul g.property h.property) i) j

theorem layerCoordinate_apply (a : ℕ) (i j : Fin N) (g : W A N a) :
    (layerCoordinate A N a i j g).toAdd =
      layer A N a ((g.val : Matrix (Fin N) (Fin N) A) - 1) i j :=
  rfl

/-- At a genuine next-superdiagonal position the layer coordinate is the
original matrix entry. -/
theorem layerCoordinate_eq_entry (a : ℕ) (i j : Fin N)
    (hij : (j : ℕ) = i + a + 1) (g : W A N a) :
    (layerCoordinate A N a i j g).toAdd =
      (g.val : Matrix (Fin N) (Fin N) A) i j := by
  rw [layerCoordinate_apply, layer_apply, ite_eq_left hij, Matrix.sub_apply,
    Matrix.one_apply_ne (show i ≠ j by intro h; subst j; omega), sub_zero]

/-- Within one refined term, the next refined term is exactly the full
zero locus of its single layer coordinate, over any coefficient ring. -/
theorem mem_refinedW_succ_iff {a : ℕ} (i j : Fin N)
    (hij : (j : ℕ) = i + a + 1) {g : GL (Fin N) A}
    (hg : g ∈ refinedW A N a i) :
    g ∈ refinedW A N a (i + 1) ↔
      layerCoordinate A N a i j ⟨g, hg.1⟩ = 1 := by
  constructor
  · intro h
    apply Multiplicative.toAdd.injective
    exact h.2 i j (by omega)
  · intro h
    refine ⟨hg.1, ?_⟩
    intro l m hl
    by_cases hli : (l : ℕ) < i
    · exact hg.2 l m hli
    · have hli' : l = i := Fin.ext (by omega)
      subst l
      by_cases hm : m = j
      · subst m
        exact congrArg Multiplicative.toAdd h
      · rw [layer_apply, ite_eq_right (by
          intro hm'
          apply hm
          exact Fin.ext (by omega))]

/-- The coordinate scales by the two diagonal entries under upper triangular
conjugation. This formula is valid over nonreduced rings as well. -/
theorem layerCoordinate_conj {a : ℕ} (i j : Fin N)
    {c g : GL (Fin N) A} (hc : c ∈ upper A N) (hg : g ∈ W A N a) :
    (layerCoordinate A N a i j ⟨c⁻¹ * g * c, W_conj hc hg⟩).toAdd =
      ((c⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) i i *
        (layerCoordinate A N a i j ⟨g, hg⟩).toAdd *
          (c : Matrix (Fin N) (Fin N) A) j j := by
  exact congrFun (congrFun (layer_conj hc hg) i) j

/-- The layer coordinate commutes with every change of coefficient ring. -/
theorem layerCoordinate_map (a : ℕ) (i j : Fin N)
    {g : GL (Fin N) A} (hg : g ∈ W A N a) (f : A →+* B) :
    (layerCoordinate B N a i j
      ⟨Matrix.GeneralLinearGroup.map f g, map_mem_W hg f⟩).toAdd =
      f ((layerCoordinate A N a i j ⟨g, hg⟩).toAdd) := by
  exact congrFun (congrFun (layer_map_W a g f) i) j

end Langlands.GroupScheme.TriangularLayer
