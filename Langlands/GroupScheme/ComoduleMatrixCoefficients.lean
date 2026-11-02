import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Data.Matrix.Basic

/-! # Matrix coefficients of finite-dimensional subcomodules of a coalgebra over a field -/

noncomputable section

open TensorProduct

namespace Langlands.GroupScheme.Comodule

universe u v

section General

variable {k : Type u} [CommRing k] {B : Type v} [AddCommGroup B] [Module k B]

section Operators

variable (Δ : B →ₗ[k] B ⊗[k] B)

/-- The operator `(id ⊗ m) ∘ Δ` attached to a linear functional `m`. -/
def rightOp (m : B →ₗ[k] k) : B →ₗ[k] B :=
  (TensorProduct.rid k B).toLinearMap ∘ₗ m.lTensor B ∘ₗ Δ

/-- The operator `(l ⊗ id) ∘ Δ` attached to a linear functional `l`. -/
def leftOp (l : B →ₗ[k] k) : B →ₗ[k] B :=
  (TensorProduct.lid k B).toLinearMap ∘ₗ l.rTensor B ∘ₗ Δ

/-- The convolution `(m ⊗ l) ∘ Δ` of two linear functionals. -/
def convFun (m l : B →ₗ[k] k) : B →ₗ[k] k :=
  LinearMap.mul' k k ∘ₗ TensorProduct.map m l ∘ₗ Δ

theorem rightOp_apply (m : B →ₗ[k] k) (x : B) :
    rightOp Δ m x = TensorProduct.rid k B (m.lTensor B (Δ x)) := rfl

theorem leftOp_apply (l : B →ₗ[k] k) (x : B) :
    leftOp Δ l x = TensorProduct.lid k B (l.rTensor B (Δ x)) := rfl

end Operators

/-- Applying two functionals to the two factors of a tensor, in either order. -/
theorem apply_rid_lTensor (l m : B →ₗ[k] k) (x : B ⊗[k] B) :
    l (TensorProduct.rid k B (m.lTensor B x)) = m (TensorProduct.lid k B (l.rTensor B x)) := by
  induction x with
  | tmul p q => simp [mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

section Coalgebra

variable (Δ : B →ₗ[k] B ⊗[k] B) (ε : B →ₗ[k] k)

/-- Coassociativity of the comultiplication, in Mathlib's `Coalgebra.coassoc` form. -/
def Coassoc : Prop :=
  (TensorProduct.assoc k B B B).toLinearMap ∘ₗ Δ.rTensor B ∘ₗ Δ = Δ.lTensor B ∘ₗ Δ

/-- The right counit law `(id ⊗ ε) ∘ Δ = id`. -/
def RightCounit : Prop :=
  (TensorProduct.rid k B).toLinearMap ∘ₗ ε.lTensor B ∘ₗ Δ = LinearMap.id

/-- The left counit law `(ε ⊗ id) ∘ Δ = id`. -/
def LeftCounit : Prop :=
  (TensorProduct.lid k B).toLinearMap ∘ₗ ε.rTensor B ∘ₗ Δ = LinearMap.id

/-- Subspaces stable under every right operator: subcomodules. -/
def IsStable (V : Submodule k B) : Prop :=
  ∀ m : B →ₗ[k] k, ∀ v ∈ V, rightOp Δ m v ∈ V

/-- The span of all right translates of `x`. -/
def orbit (x : B) : Submodule k B :=
  Submodule.span k (Set.range fun m : B →ₗ[k] k => rightOp Δ m x)

variable {Δ} {ε}

theorem coassoc_apply (h : Coassoc Δ) (x : B) :
    TensorProduct.assoc k B B B (Δ.rTensor B (Δ x)) = Δ.lTensor B (Δ x) :=
  LinearMap.congr_fun h x

/-- Composition of right operators is the right operator of the convolution. -/
theorem rightOp_rightOp (h : Coassoc Δ) (m l : B →ₗ[k] k) (x : B) :
    rightOp Δ m (rightOp Δ l x) = rightOp Δ (convFun Δ m l) x := by
  -- Commute `Δ` past the right contraction.
  have hA : (rightOp Δ m) ∘ₗ (TensorProduct.rid k B).toLinearMap ∘ₗ l.lTensor B =
      (TensorProduct.rid k B).toLinearMap ∘ₗ m.lTensor B ∘ₗ
        (TensorProduct.rid k (B ⊗[k] B)).toLinearMap ∘ₗ l.lTensor (B ⊗[k] B) ∘ₗ Δ.rTensor B := by
    apply TensorProduct.ext'
    intro p q
    simp [rightOp_apply]
  have hC : (TensorProduct.rid k B).toLinearMap ∘ₗ m.lTensor B ∘ₗ
        (TensorProduct.rid k (B ⊗[k] B)).toLinearMap ∘ₗ l.lTensor (B ⊗[k] B) ∘ₗ
          (TensorProduct.assoc k B B B).symm.toLinearMap =
      (TensorProduct.rid k B).toLinearMap ∘ₗ
        (LinearMap.mul' k k ∘ₗ TensorProduct.map m l).lTensor B := by
    apply TensorProduct.ext_threefold'
    intro p q r
    simp [smul_smul, mul_comm]
  have h1 := LinearMap.congr_fun hA (Δ x)
  have h2 : Δ.rTensor B (Δ x) = (TensorProduct.assoc k B B B).symm (Δ.lTensor B (Δ x)) := by
    rw [← coassoc_apply h x, LinearEquiv.symm_apply_apply]
  have h3 := LinearMap.congr_fun hC (Δ.lTensor B (Δ x))
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at h1 h3
  rw [rightOp_apply Δ l, h1, h2, h3, rightOp_apply, convFun]
  simp only [LinearMap.lTensor_comp_apply]

/-- `Δ` intertwines a left operator with the left contraction of `(id ⊗ Δ) ∘ Δ`. -/
theorem comul_leftOp (h : Coassoc Δ) (l : B →ₗ[k] k) (x : B) :
    Δ (leftOp Δ l x) = TensorProduct.lid k (B ⊗[k] B)
      (l.rTensor (B ⊗[k] B) (TensorProduct.assoc k B B B (Δ.rTensor B (Δ x)))) := by
  have hA : Δ ∘ₗ (TensorProduct.lid k B).toLinearMap ∘ₗ l.rTensor B =
      (TensorProduct.lid k (B ⊗[k] B)).toLinearMap ∘ₗ l.rTensor (B ⊗[k] B) ∘ₗ Δ.lTensor B := by
    apply TensorProduct.ext'
    intro p q
    simp
  have h1 := LinearMap.congr_fun hA (Δ x)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at h1
  rw [leftOp_apply, h1, coassoc_apply h x]

theorem orbit_isStable (h : Coassoc Δ) (x : B) : IsStable Δ (orbit Δ x) := by
  intro m v hv
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, rfl⟩ := hy
    rw [rightOp_rightOp h]
    exact Submodule.subset_span ⟨_, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy

theorem rightOp_counit (hr : RightCounit Δ ε) (x : B) : rightOp Δ ε x = x :=
  LinearMap.congr_fun hr x

theorem leftOp_counit (hl : LeftCounit Δ ε) (x : B) : leftOp Δ ε x = x :=
  LinearMap.congr_fun hl x

theorem mem_orbit (hr : RightCounit Δ ε) (x : B) : x ∈ orbit Δ x := by
  have h : rightOp Δ ε x ∈ orbit Δ x := Submodule.subset_span ⟨ε, rfl⟩
  rwa [rightOp_counit hr] at h

theorem IsStable.sup {V W : Submodule k B} (hV : IsStable Δ V)
    (hW : IsStable Δ W) : IsStable Δ (V ⊔ W) := by
  intro m v hv
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add]
  exact Submodule.add_mem_sup (hV m y hy) (hW m z hz)

end Coalgebra

end General

section Field

variable {k : Type u} [Field k] {B : Type v} [AddCommGroup B] [Module k B]
  {Δ : B →ₗ[k] B ⊗[k] B} {ε : B →ₗ[k] k}

/-- A tensor in `B ⊗ B` is determined by contracting its right factor with all functionals. -/
theorem tensor_ext_of_rid {x y : B ⊗[k] B}
    (h : ∀ m : B →ₗ[k] k,
      TensorProduct.rid k B (m.lTensor B x) = TensorProduct.rid k B (m.lTensor B y)) :
    x = y := by
  classical
  let c := Module.Basis.ofVectorSpace k B
  apply (TensorProduct.equivFinsuppOfBasisRight c).injective
  ext t
  rw [TensorProduct.equivFinsuppOfBasisRight_apply, TensorProduct.equivFinsuppOfBasisRight_apply]
  exact h (c.coord t)

/-- The right contractions of one tensor span a finite-dimensional subspace. -/
theorem exists_finiteDimensional_rid (x : B ⊗[k] B) :
    ∃ W : Submodule k B, FiniteDimensional k W ∧
      ∀ m : B →ₗ[k] k, TensorProduct.rid k B (m.lTensor B x) ∈ W := by
  induction x with
  | tmul p q =>
    refine ⟨k ∙ p, inferInstance, fun m => ?_⟩
    simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self p)
  | add x y hx hy =>
    obtain ⟨W₁, h₁, hW₁⟩ := hx
    obtain ⟨W₂, h₂, hW₂⟩ := hy
    exact ⟨W₁ ⊔ W₂, inferInstance, fun m => by
      rw [map_add, map_add]
      exact Submodule.add_mem_sup (hW₁ m) (hW₂ m)⟩

theorem orbit_finiteDimensional (x : B) : FiniteDimensional k (orbit Δ x) := by
  obtain ⟨W, hW, hmem⟩ := exists_finiteDimensional_rid (Δ x)
  have hle : orbit Δ x ≤ W := Submodule.span_le.mpr (by
    rintro _ ⟨m, rfl⟩
    exact hmem m)
  exact Submodule.finiteDimensional_of_le hle

/-- Every finite set lies in a finite-dimensional subcomodule. -/
theorem exists_stable (h : Coassoc Δ) (hr : RightCounit Δ ε) (s : Finset B) :
    ∃ V : Submodule k B, FiniteDimensional k V ∧ IsStable Δ V ∧ ∀ x ∈ s, x ∈ V := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨⊥, inferInstance, fun m v hv => by simp_all, by simp⟩
  | insert x s _ ih =>
    obtain ⟨V, hfd, hst, hs⟩ := ih
    have := orbit_finiteDimensional (Δ := Δ) x
    refine ⟨orbit Δ x ⊔ V, inferInstance, (orbit_isStable h x).sup hst, ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact Submodule.mem_sup_left (mem_orbit hr y)
    · exact Submodule.mem_sup_right (hs y hy)

/-- A finite-dimensional subcomodule with a basis gives multiplicative matrix coefficients. -/
theorem exists_matrix (h : Coassoc Δ) (hl : LeftCounit Δ ε) (hr : RightCounit Δ ε)
    (s : Finset B) :
    ∃ (n : ℕ) (a : Matrix (Fin n) (Fin n) B),
      (∀ i j, Δ (a i j) = ∑ l, a i l ⊗ₜ[k] a l j) ∧
      (∀ i j, ε (a i j) = (1 : Matrix (Fin n) (Fin n) k) i j) ∧
      ∀ x ∈ s, x ∈ Submodule.span k (Set.range fun p : Fin n × Fin n => a p.1 p.2) := by
  classical
  obtain ⟨V, hfd, hst, hs⟩ := exists_stable h hr s
  let e := Module.finBasis k V
  have hlam : ∀ i, ∃ g : B →ₗ[k] k, g.comp V.subtype = e.coord i :=
    fun i => LinearMap.exists_extend (e.coord i)
  choose lam hlam using hlam
  have lam_apply : ∀ i (w : B) (hw : w ∈ V), lam i w = e.repr ⟨w, hw⟩ i := by
    intro i w hw
    have := LinearMap.congr_fun (hlam i) ⟨w, hw⟩
    simpa using this
  have lam_e : ∀ i j, lam i (e j : B) = if i = j then 1 else 0 := by
    intro i j
    rw [lam_apply i _ (e j).2]
    simp [Finsupp.single_apply, eq_comm]
  -- The coaction formula on `V`.
  have hΔ : ∀ v ∈ V, Δ v = ∑ i, (e i : B) ⊗ₜ[k] leftOp Δ (lam i) v := by
    intro v hv
    apply tensor_ext_of_rid
    intro m
    have hw : rightOp Δ m v ∈ V := hst m v hv
    have hsum := e.sum_repr ⟨rightOp Δ m v, hw⟩
    have hsum' : rightOp Δ m v = ∑ i, e.repr ⟨rightOp Δ m v, hw⟩ i • (e i : B) := by
      have := congrArg Subtype.val hsum
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    rw [← rightOp_apply, hsum']
    simp only [map_sum, LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [← lam_apply i _ hw, rightOp_apply, apply_rid_lTensor, leftOp_apply]
  refine ⟨Module.finrank k V, fun i j => leftOp Δ (lam i) (e j), ?_, ?_, ?_⟩
  · intro i j
    rw [comul_leftOp h, hΔ _ (e j).2]
    simp only [map_sum, LinearMap.rTensor_tmul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [leftOp_apply Δ (lam i) (e l : B)]
    generalize leftOp Δ (lam l) (e j : B) = z
    generalize Δ (e l : B) = y
    induction y with
    | tmul p q => simp [TensorProduct.smul_tmul']
    | add y y' hy hy' => simp only [TensorProduct.add_tmul, map_add, hy, hy']
  · intro i j
    simp only
    rw [leftOp_apply, ← apply_rid_lTensor, ← rightOp_apply, rightOp_counit hr, lam_e,
      Matrix.one_apply]
  · intro x hx
    have hxV := hs x hx
    have hej : ∀ j, (e j : B) ∈ Submodule.span k
        (Set.range fun p : Fin (Module.finrank k V) × Fin (Module.finrank k V) =>
          leftOp Δ (lam p.1) (e p.2)) := by
      intro j
      rw [← leftOp_counit hl (e j : B), leftOp_apply, hΔ _ (e j).2]
      simp only [map_sum, LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)
    have hsum := e.sum_repr ⟨x, hxV⟩
    have hx' : x = ∑ j, e.repr ⟨x, hxV⟩ j • (e j : B) := by
      have := congrArg Subtype.val hsum
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    rw [hx']
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hej j)

end Field

end Langlands.GroupScheme.Comodule
