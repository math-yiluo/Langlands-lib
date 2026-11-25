/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.TotalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.ComplexShapeSigns
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-! # Exactness of finite-diagonal totalization and extension

Source: Stacks Project, Homology, Tag 012X, finite-diagonal totalization.
-/

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]
variable [∀ L : HomologicalComplex₂ C (ComplexShape.up ℕ)
  (ComplexShape.up ℕ), L.HasTotal (ComplexShape.up ℕ)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem shortExact_total_aux
    (S : ShortComplex (HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)))
    (hS : S.ShortExact) :
    (ShortComplex.mk (total.map S.f (ComplexShape.up ℕ))
      (total.map S.g (ComplexShape.up ℕ))
      (by rw [← total.map_comp, S.zero, total.map_zero])).ShortExact := by
  classical
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let π := ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)
  let J := {i : ℕ × ℕ // π i = n}
  have : Finite J := by
    refine Set.Finite.to_subtype ((Set.finite_Iic (n, n)).subset ?_)
    rintro ⟨p, q⟩ (h : p + q = n)
    simp only [Set.mem_Iic, Prod.mk_le_mk]
    omega
  have : HasFiniteBiproducts C := Abelian.hasFiniteBiproducts
  let E : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ) ⥤
      (Discrete J ⥤ C) :=
    { obj := fun A ↦ Discrete.functor (fun i : J ↦ (A.X i.val.1).X i.val.2)
      map := fun f ↦ Discrete.natTrans (fun i : Discrete J ↦ (f.f i.as.val.1).f i.as.val.2) }
  have : PreservesFiniteLimits E := preservesFiniteLimits_of_evaluation E (fun i ↦ by
    change PreservesFiniteLimits
      (HomologicalComplex.eval (CochainComplex C ℕ) (ComplexShape.up ℕ) i.as.val.1 ⋙
        HomologicalComplex.eval C (ComplexShape.up ℕ) i.as.val.2)
    infer_instance)
  have : PreservesFiniteColimits E := preservesFiniteColimits_of_evaluation E (fun i ↦ by
    change PreservesFiniteColimits
      (HomologicalComplex.eval (CochainComplex C ℕ) (ComplexShape.up ℕ) i.as.val.1 ⋙
        HomologicalComplex.eval C (ComplexShape.up ℕ) i.as.val.2)
    infer_instance)
  have : E.PreservesZeroMorphisms := by
    constructor
    intro A B
    ext ⟨i⟩
    simp [E]
  let F := E ⋙ colim
  change (S.map F).ShortExact
  exact hS.map_of_exact F

/-- Totalizing a short exact sequence in the first quadrant and extending by zero
preserves short exactness.
Source: Stacks Project, Homology, Tag 012X, total complex construction.
(blueprint: lem-sp-first-quadrant-extended-total-exact)

Proof: evaluate the short exact sequence in both indices. In total degree n >= 0,
its maps are the direct sums of these maps over p + q = n. This is a finite set;
finite biproducts in an abelian category preserve kernels and cokernels, hence the
result is short exact. In negative degrees extension by zero gives the zero sequence.
Short exactness of complexes is detected degreewise. -/
theorem shortExact_extended_total
    (S : ShortComplex (HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)))
    (hS : S.ShortExact) :
    (ShortComplex.mk
      (HomologicalComplex.extendMap (total.map S.f (ComplexShape.up ℕ))
        ComplexShape.embeddingUpNat)
      (HomologicalComplex.extendMap (total.map S.g (ComplexShape.up ℕ))
        ComplexShape.embeddingUpNat)
      (by rw [← HomologicalComplex.extendMap_comp, ← total.map_comp, S.zero,
        total.map_zero, HomologicalComplex.extendMap_zero])).ShortExact := by
  have ht := shortExact_total_aux S hS
  let T := ShortComplex.mk (total.map S.f (ComplexShape.up ℕ))
    (total.map S.g (ComplexShape.up ℕ))
    (by rw [← total.map_comp, S.zero, total.map_zero])
  let T' := ShortComplex.mk
    (HomologicalComplex.extendMap T.f ComplexShape.embeddingUpNat)
    (HomologicalComplex.extendMap T.g ComplexShape.embeddingUpNat)
    (by rw [← HomologicalComplex.extendMap_comp, T.zero,
      HomologicalComplex.extendMap_zero])
  change T'.ShortExact
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro k
  by_cases hk : ∃ m : ℕ, ComplexShape.embeddingUpNat.f m = k
  · obtain ⟨m, hm⟩ := hk
    let e : (T'.map (HomologicalComplex.eval C (ComplexShape.up ℤ) k)) ≅
        (T.map (HomologicalComplex.eval C (ComplexShape.up ℕ) m)) := ShortComplex.isoMk
      (T.X₁.extendXIso ComplexShape.embeddingUpNat hm)
      (T.X₂.extendXIso ComplexShape.embeddingUpNat hm)
      (T.X₃.extendXIso ComplexShape.embeddingUpNat hm)
      (by dsimp [T']; simp [HomologicalComplex.extendMap_f _ _ hm])
      (by dsimp [T']; simp [HomologicalComplex.extendMap_f _ _ hm])
    exact (ShortComplex.shortExact_iff_of_iso e).2
      (ht.map_of_exact (HomologicalComplex.eval C (ComplexShape.up ℕ) m))
  · have h₁ := T.X₁.isZero_extend_X ComplexShape.embeddingUpNat k (by simpa using hk)
    have h₂ := T.X₂.isZero_extend_X ComplexShape.embeddingUpNat k (by simpa using hk)
    have h₃ := T.X₃.isZero_extend_X ComplexShape.embeddingUpNat k (by simpa using hk)
    exact { exact := ShortComplex.exact_of_isZero_X₂ _ h₂
            mono_f := h₁.mono _
            epi_g := h₃.epi _ }

end HomologicalComplex₂
