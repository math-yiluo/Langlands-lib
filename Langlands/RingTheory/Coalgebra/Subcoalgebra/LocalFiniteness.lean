import Langlands.RingTheory.Coalgebra.Subcoalgebra.LocalFinitenessStatement
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Flat.Basic

/-!
# Proof of local finite dimensionality of coalgebras

Every element `c` of a coalgebra `C` over a field `k` lies in the span of its two-sided
slices `(f ⊗ id ⊗ g)(Δ₂ c)` for linear functionals `f, g` on `C`. This span is finite
dimensional, contains `c` (take `f = g = ε`), and is stable under comultiplication; the
last point uses that a tensor in `C ⊗ C` lies in `D ⊗ D` as soon as all of its left and
right slices lie in `D`. The paired Markdown describes the argument.
-/

open TensorProduct

universe u v

namespace Langlands.Subcoalgebra

namespace LocalFiniteness

section VectorSpace

variable {k : Type u} {C : Type v} [Field k] [AddCommGroup C] [Module k C]

/-- A tensor in `C ⊗ W` all of whose left slices by linear functionals on `C` vanish is
zero. -/
theorem eq_zero_of_forall_lid_rTensor {W : Type*} [AddCommGroup W] [Module k W]
    (w : C ⊗[k] W) (h : ∀ f : Module.Dual k C, TensorProduct.lid k W (f.rTensor W w) = 0) :
    w = 0 := by
  classical
  let b := Module.Basis.ofVectorSpace k C
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  ext i
  simp [TensorProduct.equivFinsuppOfBasisLeft_apply, h]

/-- A tensor in `W ⊗ C` all of whose right slices by linear functionals on `C` vanish is
zero. -/
theorem eq_zero_of_forall_rid_lTensor {W : Type*} [AddCommGroup W] [Module k W]
    (w : W ⊗[k] C) (h : ∀ f : Module.Dual k C, TensorProduct.rid k W (f.lTensor W w) = 0) :
    w = 0 := by
  classical
  let b := Module.Basis.ofVectorSpace k C
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  ext i
  simp [TensorProduct.equivFinsuppOfBasisRight_apply, h]

/-- A tensor in `C ⊗ C` lies in the image of `D ⊗ D` when all of its left and right
slices by linear functionals lie in `D`. -/
theorem mem_range_map_subtype_of_slices (D : Submodule k C) (z : C ⊗[k] C)
    (hl : ∀ f : Module.Dual k C, TensorProduct.lid k C (f.rTensor C z) ∈ D)
    (hr : ∀ f : Module.Dual k C, TensorProduct.rid k C (f.lTensor C z) ∈ D) :
    z ∈ LinearMap.range (TensorProduct.map D.subtype D.subtype) := by
  have hl' : D.mkQ.lTensor C z = 0 := by
    refine eq_zero_of_forall_lid_rTensor _ fun f => ?_
    have key : ∀ t : C ⊗[k] C,
        TensorProduct.lid k (C ⧸ D) (f.rTensor (C ⧸ D) (D.mkQ.lTensor C t)) =
          D.mkQ (TensorProduct.lid k C (f.rTensor C t)) := by
      intro t
      induction t using TensorProduct.inductionOn with
      | tmul a b => simp
      | add s t hs ht => simp only [map_add, hs, ht]
    rw [key, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hl f
  have hr' : D.mkQ.rTensor C z = 0 := by
    refine eq_zero_of_forall_rid_lTensor _ fun f => ?_
    have key : ∀ t : C ⊗[k] C,
        TensorProduct.rid k (C ⧸ D) (f.lTensor (C ⧸ D) (D.mkQ.rTensor C t)) =
          D.mkQ (TensorProduct.rid k C (f.lTensor C t)) := by
      intro t
      induction t using TensorProduct.inductionOn with
      | tmul a b => simp
      | add s t hs ht => simp only [map_add, hs, ht]
    rw [key, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hr f
  obtain ⟨y, rfl⟩ :=
    ((lTensor_exact C (LinearMap.exact_subtype_mkQ D) D.mkQ_surjective) z).mp hl'
  have hy : D.mkQ.rTensor D y = 0 := by
    apply Module.Flat.lTensor_preserves_injective_linearMap (M := C ⧸ D) D.subtype
      D.subtype_injective
    rw [map_zero, ← LinearMap.comp_apply (D.subtype.lTensor (C ⧸ D)),
      LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply]
    exact hr'
  obtain ⟨y', rfl⟩ :=
    ((rTensor_exact D (LinearMap.exact_subtype_mkQ D) D.mkQ_surjective) y).mp hy
  refine LinearMap.mem_range.mpr ⟨y', ?_⟩
  rw [← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply]

/-- Left slices of the image of `A ⊗ C` lie in `A`. -/
theorem rid_lTensor_rTensor_subtype_mem (A : Submodule k C) (g : Module.Dual k C)
    (y : A ⊗[k] C) : TensorProduct.rid k C (g.lTensor C (A.subtype.rTensor C y)) ∈ A := by
  induction y using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, TensorProduct.rid_tmul,
      Submodule.subtype_apply]
    exact A.smul_mem _ a.2
  | add s t hs ht =>
    simp only [map_add]
    exact A.add_mem hs ht

/-- Right slices of the image of `C ⊗ B` lie in `B`. -/
theorem lid_rTensor_lTensor_subtype_mem (B : Submodule k C) (f : Module.Dual k C)
    (y : C ⊗[k] B) : TensorProduct.lid k C (f.rTensor C (B.subtype.lTensor C y)) ∈ B := by
  induction y using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul,
      Submodule.subtype_apply]
    exact B.smul_mem _ b.2
  | add s t hs ht =>
    simp only [map_add]
    exact B.add_mem hs ht

end VectorSpace

section Coalgebra

variable {k : Type u} {C : Type v} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

/-- The left slice `x ↦ (f ⊗ id)(Δ x)` by a linear functional `f`. -/
noncomputable def leftSlice (f : Module.Dual k C) : C →ₗ[k] C :=
  (TensorProduct.lid k C).toLinearMap ∘ₗ f.rTensor C ∘ₗ Coalgebra.comul

/-- The right slice `x ↦ (id ⊗ g)(Δ x)` by a linear functional `g`. -/
noncomputable def rightSlice (g : Module.Dual k C) : C →ₗ[k] C :=
  (TensorProduct.rid k C).toLinearMap ∘ₗ g.lTensor C ∘ₗ Coalgebra.comul

theorem leftSlice_apply (f : Module.Dual k C) (x : C) :
    leftSlice f x = TensorProduct.lid k C (f.rTensor C (Coalgebra.comul x)) :=
  rfl

theorem rightSlice_apply (g : Module.Dual k C) (x : C) :
    rightSlice g x = TensorProduct.rid k C (g.lTensor C (Coalgebra.comul x)) :=
  rfl

/-- The counit slices are the identity. -/
theorem leftSlice_counit (x : C) : leftSlice (Coalgebra.counit (R := k)) x = x := by
  rw [leftSlice_apply, Coalgebra.rTensor_counit_comul, TensorProduct.lid_tmul, one_smul]

/-- The counit slices are the identity. -/
theorem rightSlice_counit (x : C) : rightSlice (Coalgebra.counit (R := k)) x = x := by
  rw [rightSlice_apply, Coalgebra.lTensor_counit_comul, TensorProduct.rid_tmul, one_smul]

/-- Coassociativity: comultiplication intertwines a left slice with its left tensor
amplification. -/
theorem comul_leftSlice (f : Module.Dual k C) (x : C) :
    Coalgebra.comul (R := k) (leftSlice f x) = (leftSlice f).rTensor C (Coalgebra.comul x) := by
  have h₁ : Coalgebra.comul (R := k) ∘ₗ ((TensorProduct.lid k C).toLinearMap ∘ₗ f.rTensor C) =
      ((TensorProduct.lid k (C ⊗[k] C)).toLinearMap ∘ₗ f.rTensor (C ⊗[k] C)) ∘ₗ
        (Coalgebra.comul (R := k) (A := C)).lTensor C := by
    ext a b
    simp
  have h₂ : ((TensorProduct.lid k (C ⊗[k] C)).toLinearMap ∘ₗ f.rTensor (C ⊗[k] C)) ∘ₗ
        (TensorProduct.assoc k C C C).toLinearMap =
      ((TensorProduct.lid k C).toLinearMap ∘ₗ f.rTensor C).rTensor C := by
    ext a b c
    simp [TensorProduct.smul_tmul']
  calc Coalgebra.comul (R := k) (leftSlice f x)
      = (Coalgebra.comul (R := k) ∘ₗ ((TensorProduct.lid k C).toLinearMap ∘ₗ f.rTensor C))
          (Coalgebra.comul x) := rfl
    _ = ((TensorProduct.lid k (C ⊗[k] C)).toLinearMap ∘ₗ f.rTensor (C ⊗[k] C))
          ((Coalgebra.comul (R := k) (A := C)).lTensor C (Coalgebra.comul x)) := by
        rw [h₁, LinearMap.comp_apply]
    _ = ((TensorProduct.lid k (C ⊗[k] C)).toLinearMap ∘ₗ f.rTensor (C ⊗[k] C))
          (TensorProduct.assoc k C C C
            ((Coalgebra.comul (R := k) (A := C)).rTensor C (Coalgebra.comul x))) := by
        rw [Coalgebra.coassoc_apply]
    _ = (((TensorProduct.lid k C).toLinearMap ∘ₗ f.rTensor C).rTensor C)
          ((Coalgebra.comul (R := k) (A := C)).rTensor C (Coalgebra.comul x)) := by
        rw [← h₂]
        rfl
    _ = (leftSlice f).rTensor C (Coalgebra.comul x) := by
        rw [← LinearMap.rTensor_comp_apply]
        rfl

/-- Coassociativity: comultiplication intertwines a right slice with its right tensor
amplification. -/
theorem comul_rightSlice (g : Module.Dual k C) (x : C) :
    Coalgebra.comul (R := k) (rightSlice g x) = (rightSlice g).lTensor C (Coalgebra.comul x) := by
  have h₁ : Coalgebra.comul (R := k) ∘ₗ ((TensorProduct.rid k C).toLinearMap ∘ₗ g.lTensor C) =
      ((TensorProduct.rid k (C ⊗[k] C)).toLinearMap ∘ₗ g.lTensor (C ⊗[k] C)) ∘ₗ
        (Coalgebra.comul (R := k) (A := C)).rTensor C := by
    ext a b
    simp
  have h₂ : ((TensorProduct.rid k (C ⊗[k] C)).toLinearMap ∘ₗ g.lTensor (C ⊗[k] C)) ∘ₗ
        (TensorProduct.assoc k C C C).symm.toLinearMap =
      ((TensorProduct.rid k C).toLinearMap ∘ₗ g.lTensor C).lTensor C := by
    ext a b c
    simp
  calc Coalgebra.comul (R := k) (rightSlice g x)
      = (Coalgebra.comul (R := k) ∘ₗ ((TensorProduct.rid k C).toLinearMap ∘ₗ g.lTensor C))
          (Coalgebra.comul x) := rfl
    _ = ((TensorProduct.rid k (C ⊗[k] C)).toLinearMap ∘ₗ g.lTensor (C ⊗[k] C))
          ((Coalgebra.comul (R := k) (A := C)).rTensor C (Coalgebra.comul x)) := by
        rw [h₁, LinearMap.comp_apply]
    _ = ((TensorProduct.rid k (C ⊗[k] C)).toLinearMap ∘ₗ g.lTensor (C ⊗[k] C))
          ((TensorProduct.assoc k C C C).symm
            ((Coalgebra.comul (R := k) (A := C)).lTensor C (Coalgebra.comul x))) := by
        rw [Coalgebra.coassoc_symm_apply]
    _ = (((TensorProduct.rid k C).toLinearMap ∘ₗ g.lTensor C).lTensor C)
          ((Coalgebra.comul (R := k) (A := C)).lTensor C (Coalgebra.comul x)) := by
        rw [← h₂]
        rfl
    _ = (rightSlice g).lTensor C (Coalgebra.comul x) := by
        rw [← LinearMap.lTensor_comp_apply]
        rfl

/-- Left and right slices commute, by coassociativity. -/
theorem leftSlice_rightSlice (f g : Module.Dual k C) (x : C) :
    leftSlice f (rightSlice g x) = rightSlice g (leftSlice f x) := by
  have h : ((TensorProduct.lid k C).toLinearMap ∘ₗ f.rTensor C ∘ₗ
        ((TensorProduct.rid k C).toLinearMap ∘ₗ g.lTensor C).lTensor C) ∘ₗ
        (TensorProduct.assoc k C C C).toLinearMap =
      (TensorProduct.rid k C).toLinearMap ∘ₗ g.lTensor C ∘ₗ
        ((TensorProduct.lid k C).toLinearMap ∘ₗ f.rTensor C).rTensor C := by
    ext a b c
    simp
  calc leftSlice f (rightSlice g x)
      = ((TensorProduct.lid k C).toLinearMap ∘ₗ f.rTensor C ∘ₗ
          ((TensorProduct.rid k C).toLinearMap ∘ₗ g.lTensor C).lTensor C)
          ((Coalgebra.comul (R := k) (A := C)).lTensor C (Coalgebra.comul x)) := by
        rw [leftSlice_apply, comul_rightSlice, rightSlice, ← LinearMap.comp_assoc,
          LinearMap.lTensor_comp_apply]
        rfl
    _ = ((TensorProduct.lid k C).toLinearMap ∘ₗ f.rTensor C ∘ₗ
          ((TensorProduct.rid k C).toLinearMap ∘ₗ g.lTensor C).lTensor C)
          (TensorProduct.assoc k C C C
            ((Coalgebra.comul (R := k) (A := C)).rTensor C (Coalgebra.comul x))) := by
        rw [Coalgebra.coassoc_apply]
    _ = ((TensorProduct.rid k C).toLinearMap ∘ₗ g.lTensor C ∘ₗ
          ((TensorProduct.lid k C).toLinearMap ∘ₗ f.rTensor C).rTensor C)
          ((Coalgebra.comul (R := k) (A := C)).rTensor C (Coalgebra.comul x)) := by
        rw [← h]
        rfl
    _ = rightSlice g (leftSlice f x) := by
        rw [rightSlice_apply, comul_leftSlice, leftSlice,
          ← LinearMap.comp_assoc Coalgebra.comul (f.rTensor C), LinearMap.rTensor_comp_apply]
        rfl

/-- Iterated left slices are left slices. -/
theorem leftSlice_leftSlice (h f : Module.Dual k C) (x : C) :
    leftSlice h (leftSlice f x) = leftSlice (h ∘ₗ leftSlice f) x := by
  rw [leftSlice_apply, comul_leftSlice, ← LinearMap.rTensor_comp_apply]
  rfl

/-- Iterated right slices are right slices. -/
theorem rightSlice_rightSlice (h g : Module.Dual k C) (x : C) :
    rightSlice h (rightSlice g x) = rightSlice (h ∘ₗ rightSlice g) x := by
  rw [rightSlice_apply, comul_rightSlice, ← LinearMap.lTensor_comp_apply]
  rfl

/-- The span of all two-sided slices `(f ⊗ id ⊗ g)(Δ₂ c)` of `c`. -/
noncomputable def sliceSpan (c : C) : Submodule k C :=
  Submodule.span k
    (Set.range fun p : Module.Dual k C × Module.Dual k C => leftSlice p.1 (rightSlice p.2 c))

theorem mem_sliceSpan (c : C) : c ∈ sliceSpan (k := k) c :=
  Submodule.subset_span ⟨(Coalgebra.counit, Coalgebra.counit), by
    change leftSlice _ (rightSlice _ c) = c
    rw [rightSlice_counit, leftSlice_counit]⟩

theorem leftSlice_mem_sliceSpan (c : C) (h : Module.Dual k C) {x : C}
    (hx : x ∈ sliceSpan (k := k) c) : leftSlice h x ∈ sliceSpan (k := k) c := by
  have hle : sliceSpan c ≤ (sliceSpan c).comap (leftSlice h) := Submodule.span_le.mpr (by
    rintro _ ⟨⟨f, g⟩, rfl⟩
    change leftSlice h (leftSlice f (rightSlice g c)) ∈ sliceSpan c
    rw [leftSlice_leftSlice]
    exact Submodule.subset_span ⟨(h ∘ₗ leftSlice f, g), rfl⟩)
  exact hle hx

theorem rightSlice_mem_sliceSpan (c : C) (h : Module.Dual k C) {x : C}
    (hx : x ∈ sliceSpan (k := k) c) : rightSlice h x ∈ sliceSpan (k := k) c := by
  have hle : sliceSpan c ≤ (sliceSpan c).comap (rightSlice h) := Submodule.span_le.mpr (by
    rintro _ ⟨⟨f, g⟩, rfl⟩
    change rightSlice h (leftSlice f (rightSlice g c)) ∈ sliceSpan c
    rw [← leftSlice_rightSlice, rightSlice_rightSlice]
    exact Submodule.subset_span ⟨(f, h ∘ₗ rightSlice g), rfl⟩)
  exact hle hx

/-- The slice span is closed under comultiplication. -/
theorem comul_mem_sliceSpan (c : C) {x : C} (hx : x ∈ sliceSpan (k := k) c) :
    Coalgebra.comul (R := k) x ∈
      LinearMap.range (TensorProduct.map (sliceSpan c).subtype (sliceSpan c).subtype) :=
  mem_range_map_subtype_of_slices _ _ (fun h => leftSlice_mem_sliceSpan c h hx)
    (fun h => rightSlice_mem_sliceSpan c h hx)

/-- The slice span is finite dimensional. -/
theorem finiteDimensional_sliceSpan (c : C) : FiniteDimensional k (sliceSpan (k := k) c) := by
  obtain ⟨A, hAfin, hcA⟩ := TensorProduct.exists_finite_submodule_left_of_setFinite
    ({Coalgebra.comul (R := k) c} : Set (C ⊗[k] C)) (Set.finite_singleton _)
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp (hcA (Set.mem_singleton _))
  have hRA : ∀ g : Module.Dual k C, rightSlice g c ∈ A := fun g => by
    rw [rightSlice_apply, ← hy]
    exact rid_lTensor_rTensor_subtype_mem A g y
  obtain ⟨S, hSfin, hS⟩ := Submodule.fg_def.mp (Module.Finite.iff_fg.mp hAfin)
  obtain ⟨B, hBfin, hSB⟩ := TensorProduct.exists_finite_submodule_right_of_setFinite
    (Coalgebra.comul (R := k) '' S) (hSfin.image _)
  have hLB : ∀ f : Module.Dual k C, A ≤ B.comap (leftSlice f) := fun f => by
    rw [← hS, Submodule.span_le]
    intro s hs
    obtain ⟨z, hz⟩ := LinearMap.mem_range.mp (hSB ⟨s, hs, rfl⟩)
    change leftSlice f s ∈ B
    rw [leftSlice_apply, ← hz]
    exact lid_rTensor_lTensor_subtype_mem B f z
  have hDB : sliceSpan c ≤ B := Submodule.span_le.mpr (by
    rintro _ ⟨⟨f, g⟩, rfl⟩
    exact hLB f (hRA g))
  exact Submodule.finiteDimensional_of_le hDB

end Coalgebra

end LocalFiniteness

open LocalFiniteness in
/-- Proof of `LocalFinitenessStatement`: the span of the two-sided slices of `c` is a
finite-dimensional subcoalgebra containing `c`. -/
theorem localFiniteness : LocalFinitenessStatement.{u, v} := by
  intro k _ C _ _ _ c
  exact ⟨⟨sliceSpan c, fun x hx => comul_mem_sliceSpan c hx⟩, mem_sliceSpan c,
    finiteDimensional_sliceSpan c⟩

end Langlands.Subcoalgebra
