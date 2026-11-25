/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Tensor homology coordinates

Source: Stacks Project, Varieties, Tag 0BED, `equation-kunneth-on-cech`.
(blueprint: lem-sc-tensor-homology-coordinates)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory DirectSum
open scoped TensorProduct

namespace HomologicalComplex

private theorem term_homology_projection {k : Type u} [Field k]
    (K : CochainComplex (ModuleCat.{u} k) ℤ) (p : ℤ) :
    ∃ P : K.X p →ₗ[k] K.homology p,
      (∀ a, P (K.iCycles p a) = K.homologyπ p a) ∧
      ∀ i x, P (K.d i p x) = 0 := by
  let P := (K.homologyπ p).hom.comp (K.iCycles p).hom.leftInverse
  have hi : LinearMap.ker (K.iCycles p).hom = ⊥ :=
    LinearMap.ker_eq_bot.mpr ((ModuleCat.mono_iff_injective _).mp inferInstance)
  have hP (a : K.cycles p) : P (K.iCycles p a) = K.homologyπ p a := by
    dsimp only [P, LinearMap.comp_apply]
    rw [LinearMap.leftInverse_apply_of_inj hi]
  refine ⟨P, hP, ?_⟩
  intro i x
  rw [← show K.iCycles p (K.toCycles i p x) = K.d i p x from
    congrArg (fun f ↦ f x) (K.toCycles_i i p)]
  rw [hP]
  exact congrArg (fun f ↦ f x) (K.toCycles_comp_homologyπ i p)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Extract tensor homology coordinates from the total homology over a field.
Source: Stacks Project, Varieties, Tag 0BED, `equation-kunneth-on-cech`,
and the complement argument of `lem-sc-qcoh-cech-total-tensor-iso`, steps 1 and 2.
(blueprint: lem-sc-tensor-homology-coordinates)

Proof: Extend the quotient map from cycles to homology linearly to each full
term of A and B, using complements to their cycle subspaces. These extensions
kill boundaries, since on cycles they agree with the homology quotient.
Tensor the two extensions on each bidegree and compose with the corresponding
direct-sum inclusion. The universal property of the total direct sum assembles
these maps into a linear map on the degree-n term. It kills the total
differential: in each of its two terms one factor is a boundary and is
annihilated by its extension. Restrict to total cycles and descend through
boundaries. On a tensor of cycles, the extension equations give exactly the
specified direct-sum element. No boundedness or dimension assumption is needed. -/
theorem tensor_homology_coordinates {k : Type u} [Field k]
    (A B : CochainComplex (ModuleCat.{u} k) ℤ) (n : ℤ) :
    ∃ r : (mapBifunctor A B (curriedTensor (ModuleCat.{u} k))
        (ComplexShape.up ℤ)).homology n →ₗ[k]
        (⨁ s : {pq : ℤ × ℤ // pq.1 + pq.2 = n},
          (A.homology s.1.1) ⊗[k] (B.homology s.1.2)),
      ∀ (s : {pq : ℤ × ℤ // pq.1 + pq.2 = n})
        (a : A.cycles s.1.1) (b : B.cycles s.1.2)
        (z : (mapBifunctor A B (curriedTensor (ModuleCat.{u} k))
          (ComplexShape.up ℤ)).cycles n),
        (mapBifunctor A B (curriedTensor (ModuleCat.{u} k))
          (ComplexShape.up ℤ)).iCycles n z =
          ιMapBifunctor A B (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)
            s.1.1 s.1.2 n s.2
            ((A.iCycles s.1.1 a) ⊗ₜ[k] (B.iCycles s.1.2 b)) →
        r ((mapBifunctor A B (curriedTensor (ModuleCat.{u} k))
          (ComplexShape.up ℤ)).homologyπ n z) =
          DirectSum.lof k _ _ s
            ((A.homologyπ s.1.1 a) ⊗ₜ[k] (B.homologyπ s.1.2 b)) := by
  classical
  let T := mapBifunctor A B (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)
  let S := {pq : ℤ × ℤ // pq.1 + pq.2 = n}
  let H := ⨁ s : S, (A.homology s.1.1) ⊗[k] (B.homology s.1.2)
  choose P hP hPd using term_homology_projection A
  choose Q hQ hQd using term_homology_projection B
  let t : T.X n ⟶ ModuleCat.of k H :=
    mapBifunctorDesc (K₁ := A) (K₂ := B)
      (F := curriedTensor (ModuleCat.{u} k)) (c := ComplexShape.up ℤ)
      (fun p q h ↦ ModuleCat.ofHom
        ((DirectSum.lof k S _ ⟨(p, q), h⟩).comp (TensorProduct.map (P p) (Q q))))
  have ht (p q : ℤ) (h : p + q = n) (x : A.X p) (y : B.X q) :
      t (ιMapBifunctor A B (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)
        p q n h (x ⊗ₜ[k] y)) =
      DirectSum.lof k S _ ⟨(p, q), h⟩ ((P p x) ⊗ₜ[k] (Q q y)) := by
    exact congrArg (fun f ↦ f (x ⊗ₜ[k] y)) (ι_mapBifunctorDesc (K₁ := A) (K₂ := B)
      (F := curriedTensor (ModuleCat.{u} k)) (c := ComplexShape.up ℤ)
      (A := ModuleCat.of k H) (j := n)
      (fun p q h ↦ ModuleCat.ofHom
        ((DirectSum.lof k S _ ⟨(p, q), h⟩).comp (TensorProduct.map (P p) (Q q)))) p q h)
  have hdt : T.d (n - 1) n ≫ t = 0 := by
    apply mapBifunctor.hom_ext
    intro p q hpq
    simp only [T, mapBifunctor.d_eq, Preadditive.comp_add, Preadditive.add_comp,
      mapBifunctor.ι_D₁_assoc, mapBifunctor.ι_D₂_assoc, comp_zero]
    rw [mapBifunctor.d₁_eq A B _ _
        (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl) q n (by
          change p + 1 + q = n
          change p + q = n - 1 at hpq
          omega),
      mapBifunctor.d₂_eq A B _ _ p
        (show (ComplexShape.up ℤ).Rel q (q + 1) from rfl) n (by
          change p + (q + 1) = n
          change p + q = n - 1 at hpq
          omega)]
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    simp only [curriedTensor_obj_obj, ComplexShape.ε₁_def, curriedTensor_map_app,
      one_smul, Category.assoc, ComplexShape.ε₂_def, ComplexShape.ε_up_ℤ,
      curriedTensor_obj_map, Linear.units_smul_comp, ModuleCat.hom_add,
      ModuleCat.hom_comp, ModuleCat.hom_smul, LinearMap.add_apply, LinearMap.coe_comp,
      Function.comp_apply, ModuleCat.MonoidalCategory.whiskerRight_apply,
      LinearMap.smul_apply, ModuleCat.MonoidalCategory.whiskerLeft_apply,
      ModuleCat.hom_zero, LinearMap.zero_apply]
    change t (ιMapBifunctor A B (curriedTensor (ModuleCat.{u} k))
      (ComplexShape.up ℤ) (p + 1) q n _ ((A.d p (p + 1) x) ⊗ₜ[k] y)) +
      p.negOnePow • t (ιMapBifunctor A B (curriedTensor (ModuleCat.{u} k))
        (ComplexShape.up ℤ) p (q + 1) n _ (x ⊗ₜ[k] (B.d q (q + 1) y))) = 0
    rw [ht, ht, hPd, hQd]
    simp
  have hk : (T.sc n).toCycles ≫ (T.iCycles n ≫ t) = 0 := by
    change (T.sc n).toCycles ≫ ((T.sc n).iCycles ≫ t) = 0
    rw [← Category.assoc, (T.sc n).toCycles_i]
    change T.d ((ComplexShape.up ℤ).prev n) n ≫ t = 0
    rw [(ComplexShape.up ℤ).prev_eq' (show
      (ComplexShape.up ℤ).Rel (n - 1) n by change n - 1 + 1 = n; omega)]
    exact hdt
  let r := (T.sc n).descHomology (T.iCycles n ≫ t) hk
  refine ⟨r.hom, ?_⟩
  intro s a b z hz
  have hr := congrArg (fun f ↦ f z) ((T.sc n).π_descHomology (T.iCycles n ≫ t) hk)
  change r (T.homologyπ n z) = _ at hr
  change r (T.homologyπ n z) = _
  rw [hr]
  change t (T.iCycles n z) = _
  rw [hz, ht, hP, hQ]

end HomologicalComplex
