import Langlands.BushnellKutzko.RefinementDiagonal

/-! # Block filtration for reduction to one field line

Coordinate calculation for the one-field-line reduction in the opening proof of BK93
(2.4.1)(i), printed p. 66, using the splitting basis and diagonal map of `RefinementDiagonal`.
-/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.PureApproximation

universe uF uE uV

/-- The least integer `q` with `t ≤ d*q` when `d > 0`. -/
def ceilDiv (t d : ℤ) : ℤ := -((-t) / d)

theorem ceilDiv_le_iff {d : ℤ} (hd : 0 < d) (t m : ℤ) :
    ceilDiv t d ≤ m ↔ t ≤ d * m := by
  rw [ceilDiv, neg_le, Int.le_ediv_iff_mul_le hd, neg_mul, mul_comm m d]
  omega

theorem ceilDiv_add_mul {d : ℤ} (hd : 0 < d) (t k : ℤ) :
    ceilDiv (t + d * k) d = ceilDiv t d + k := by
  have h₁ := (ceilDiv_le_iff hd t _).mp (le_refl (ceilDiv t d))
  have h₂ := (ceilDiv_le_iff hd (t + d * k) _).mp
    (le_refl (ceilDiv (t + d * k) d))
  apply le_antisymm
  · rw [ceilDiv_le_iff hd, mul_add]
    omega
  · have h := (ceilDiv_le_iff hd t (ceilDiv (t + d * k) d - k)).mpr (by
      rw [mul_sub]
      omega)
    omega

theorem ceilDiv_zero (d : ℤ) : ceilDiv 0 d = 0 := by
  simp [ceilDiv]

theorem ceilDiv_one {d : ℤ} (hd : 0 < d) : ceilDiv 1 d = 1 := by
  have h₂ : ceilDiv 1 d ≤ 1 := (ceilDiv_le_iff hd 1 1).mpr (by rw [mul_one]; omega)
  have hn : ¬ ceilDiv 1 d ≤ 0 := by rw [ceilDiv_le_iff hd]; simp
  omega

section Blocks

variable {F : Type uF} [Field F] {E : Type uE} [Field E] [Algebra F E]
  {V : Type uV} [AddCommGroup V] [Module F V] [Module E V] [IsScalarTower F E V]
  {n : ℕ} (w : Module.Basis (Fin n) E V)

/-- The `(j,l)` entry of an endomorphism written in a relative basis. -/
def blockEntry (x : Module.End F V) (j l : Fin n) : Module.End F E :=
  lineProj F w j ∘ₗ x ∘ₗ lineIncl F w l

@[simp] theorem blockEntry_apply (x : Module.End F V) (j l : Fin n) (a : E) :
    blockEntry w x j l a = w.repr (x (a • w l)) j := rfl

/-- The endomorphism having the supplied entries. -/
def assembleBlocks (M : Fin n → Fin n → Module.End F E) : Module.End F V :=
  ∑ j, ∑ l, lineIncl F w j ∘ₗ M j l ∘ₗ lineProj F w l

theorem blockEntry_assembleBlocks (M : Fin n → Fin n → Module.End F E) (j l : Fin n) :
    blockEntry w (assembleBlocks w M) j l = M j l := by
  ext a
  have hsum (k : Fin n) :
      (∑ m, M k m (w.repr (a • w l) m) • w k) = M k l a • w k := by
    rw [Finset.sum_eq_single l]
    · rw [repr_smul_basis, ite_eq_left rfl]
    · intro m _ hm
      rw [repr_smul_basis, ite_eq_right hm.symm, map_zero, zero_smul]
    · simp
  simp only [blockEntry_apply, assembleBlocks, LinearMap.sum_apply, LinearMap.comp_apply,
    lineIncl_apply, lineProj_apply, hsum, w.repr_sum_self]

theorem eq_of_blockEntry_eq {x y : Module.End F V}
    (h : ∀ j l, blockEntry w x j l = blockEntry w y j l) : x = y := by
  ext v
  rw [← w.sum_repr v, map_sum, map_sum]
  refine Finset.sum_congr rfl fun l _ => w.repr.injective ?_
  ext j
  exact LinearMap.congr_fun (h j l) (w.repr v l)

theorem blockEntry_sub (x y : Module.End F V) (j l : Fin n) :
    blockEntry w (x - y) j l = blockEntry w x j l - blockEntry w y j l := by
  ext a
  simp

variable [ValuativeRel F]

theorem blockEntry_commutator (b : Module.End F E) (x : Module.End F V) (j l : Fin n) :
    blockEntry w (diagonal F w b * x - x * diagonal F w b) j l =
      b * blockEntry w x j l - blockEntry w x j l * b := by
  ext a
  simp only [blockEntry_sub, LinearMap.sub_apply, blockEntry_apply, Module.End.mul_apply,
    repr_diagonal, diagonal_smul_basis]

theorem blockEntry_diagonal (x : Module.End F E) (j l : Fin n) :
    blockEntry w (diagonal F w x) j l = if l = j then x else 0 := by
  ext a
  simp only [blockEntry_apply, repr_diagonal, repr_smul_basis]
  by_cases h : l = j <;> simp [h]

end Blocks

section Filtration

variable {F : Type uF} [Field F] [ValuativeRel F] {E : Type uE} [Field E] [Algebra F E]
  {V : Type uV} [AddCommGroup V] [Module F V] [Module E V] [IsScalarTower F E V]
  (A : LatticeChain 𝒪[F] F V) (C : LatticeChain 𝒪[F] F E)
  {n : ℕ} (w : Module.Basis (Fin n) E V) (d : ℤ) (p : Fin n → ℤ)

/-- In each relative basis line, lattice membership is read from a common line chain,
with dilation `d` and translation `p j` in the `j`-th line. -/
def ScaledLatticeCoordinates : Prop :=
  ∀ (j : Fin n) (i : ℤ) (a : E),
    a • w j ∈ A.lattice i ↔ a ∈ C.lattice (ceilDiv (i - p j) d)

/-- The ambient filtration at depth `s` consists of blocks in the line filtrations
at depths `⌈(s + p_l − p_j)/d⌉`, under the split and scaled coordinate conditions. -/
def BlockFiltrationStatement : Prop :=
  RelSplits (L := E) A w → 0 < d → ScaledLatticeCoordinates A C w d p →
    ∀ (x : Module.End F V) (s : ℤ), x ∈ A.endFiltration s ↔ ∀ j l,
      blockEntry w x j l ∈ C.endFiltration (ceilDiv (s + p l - p j) d)

theorem blockFiltration : BlockFiltrationStatement A C w d p := by
  intro hw hd hcoord x s
  have hrepr {i : ℤ} {v : V} (hv : v ∈ A.lattice i) (j : Fin n) :
      w.repr v j • w j ∈ A.lattice i :=
    hw i (fun l => w.repr v l) ((w.sum_repr v).symm ▸ hv) j
  constructor
  · intro hx j l i a ha
    have hceil : ceilDiv (p l + d * i - p l) d = i := by
      rw [add_sub_cancel_left, ← zero_add (d * i), ceilDiv_add_mul hd, ceilDiv_zero, zero_add]
    have hmem := (hcoord l (p l + d * i) a).mpr (hceil.symm ▸ ha)
    have hja := (hcoord j _ _).mp (hrepr (hx _ _ hmem) j)
    change blockEntry w x j l a ∈ C.lattice (i + ceilDiv (s + p l - p j) d)
    rw [blockEntry_apply]
    convert hja using 1
    rw [show p l + d * i + s - p j = (s + p l - p j) + d * i by omega,
      ceilDiv_add_mul hd, add_comm]
  · intro hx i v hv
    have hproj := hrepr hv
    rw [← w.sum_repr v, map_sum]
    refine Submodule.sum_mem _ fun l _ => ?_
    rw [← w.sum_repr (x (w.repr v l • w l))]
    refine Submodule.sum_mem _ fun j _ => ?_
    have h₁ := (hcoord l _ _).mp (hproj l)
    have h₂ := hx j l _ _ h₁
    have h₃ : ceilDiv (i + s - p j) d ≤
        ceilDiv (i - p l) d + ceilDiv (s + p l - p j) d := by
      have ha := (ceilDiv_le_iff hd (i - p l) _).mp (le_refl (ceilDiv (i - p l) d))
      have hb := (ceilDiv_le_iff hd (s + p l - p j) _).mp
        (le_refl (ceilDiv (s + p l - p j) d))
      rw [ceilDiv_le_iff hd, mul_add]
      omega
    apply (hcoord j _ _).mpr
    exact C.antitone h₃ h₂

variable (hw : RelSplits (L := E) A w) (hd : 0 < d)
  (hcoord : ScaledLatticeCoordinates A C w d p)

include hw hd hcoord in
/-- The diagonal map reads the rounded ambient depth in the common line chain. -/
theorem diagonal_mem_endFiltration_iff (j₀ : Fin n) (x : Module.End F E) (s : ℤ) :
    diagonal F w x ∈ A.endFiltration s ↔ x ∈ C.endFiltration (ceilDiv s d) := by
  rw [blockFiltration A C w d p hw hd hcoord]
  simp only [blockEntry_diagonal]
  constructor
  · intro h
    simpa using h j₀ j₀
  · intro h j l
    by_cases h' : l = j
    · subst l
      simpa using h
    · rw [ite_eq_right h']
      exact zero_mem _

end Filtration

end Langlands.BushnellKutzko.PureApproximation
