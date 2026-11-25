/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.Order.Directed
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.LinearAlgebra.TensorProduct.DirectLimit

/-!
# Elements in tensor products over directed ring colimits

Source: Stacks Project, Algebra, Tags 00D6, 00D7, 00DD, as used in Tag 07RI
(blueprint: lem-weil-pbc-directed-colimit-base-change-elementwise).
-/

@[expose] public section

universe v w

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace TensorProduct

/-- Base change along a directed ring colimit: every element of `colimit F ⊗[F.obj i₀] M₀`
comes from a stage `F.obj i ⊗[F.obj i₀] M₀` with `i₀ ≤ i`, and an element of a stage whose
image is zero already vanishes at a later stage. Source: Stacks Project, Algebra, Tags 00D6,
00D7 and 00DD, used in Tag 07RI
(blueprint: lem-weil-pbc-directed-colimit-base-change-elementwise).

The `F.obj i₀`-algebra structures on `F.obj i` (`i₀ ≤ i`) and on `colimit F` are those of
`F.map (homOfLE _)` and `colimit.ι F i₀`; the maps `μ_i = α_i ⊗ id` and
`μ_{i'i} = α_{i'i} ⊗ id` are `LinearMap.rTensor M₀` of these ring maps viewed as
`F.obj i₀`-algebra maps.

Proof:
1. Restrict to the nonempty directed upper tail `J = {i | i₀ ≤ i}`. The ring maps
   become `S = F.obj i₀`-linear maps `f`, and the coprojections become linear maps `α`.
   Functoriality and cocone naturality give the directed-system and compatibility laws.
2. Descend `α` to a linear map `g` from `Module.DirectLimit A f` to the ring colimit.
   Mathlib's filtered ring colimit representative lemma makes `g` surjective: move a
   representative to a common upper bound with `i₀`. Its equality lemma makes `g`
   injective: equal representatives become equal at a common later stage, hence have
   equal classes in the module direct limit. This is the module identification of
   Tag 00D6, with no passage through integer algebras.
3. Tensor this linear equivalence with `M₀`, and compose with the inverse of
   `TensorProduct.directLimitLeft` (Tag 00DD). The resulting linear equivalence `e`
   identifies the tensor module direct limit with `R ⊗[S] M₀`. On a stage tensor its
   value is `α.rTensor M₀`, as checked by induction on tensors.
4. `Module.DirectLimit.exists_of` represents `e.symm x` at a stage, proving the first
   clause. If a stage tensor maps to zero, injectivity of `e` makes its direct-limit
   class zero; `Module.DirectLimit.of.zero_exact` (Tag 00D7) gives a later stage where
   its image vanishes. The subtype indices and linear maps give exactly the stated
   upper-tail indices and tensor transition maps.
-/
theorem directedColimitBaseChangeElementwise
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{v}) [HasColimit F]
    (i₀ : I) (M₀ : Type w) [AddCommGroup M₀] [Module (F.obj i₀) M₀] :
    let S := F.obj i₀
    let R := colimit F
    letI : Algebra S R := (colimit.ι F i₀).hom.toAlgebra
    (∀ x : R ⊗[S] M₀, ∃ (i : I) (h : i₀ ≤ i),
      letI : Algebra S (F.obj i) := (F.map (homOfLE h)).hom.toAlgebra
      let αᵢ : F.obj i →ₐ[S] R :=
        { (colimit.ι F i).hom with
          commutes' := fun s ↦
            congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s) (colimit.w F (homOfLE h)) }
      ∃ t : F.obj i ⊗[S] M₀, αᵢ.toLinearMap.rTensor M₀ t = x) ∧
    (∀ (i : I) (h : i₀ ≤ i),
      letI : Algebra S (F.obj i) := (F.map (homOfLE h)).hom.toAlgebra
      let αᵢ : F.obj i →ₐ[S] R :=
        { (colimit.ι F i).hom with
          commutes' := fun s ↦
            congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s) (colimit.w F (homOfLE h)) }
      ∀ t : F.obj i ⊗[S] M₀, αᵢ.toLinearMap.rTensor M₀ t = 0 →
        ∃ (i' : I) (h' : i ≤ i'),
          letI : Algebra S (F.obj i') := (F.map (homOfLE (h.trans h'))).hom.toAlgebra
          let αᵢ'ᵢ : F.obj i →ₐ[S] F.obj i' :=
            { (F.map (homOfLE h')).hom with
              commutes' := fun s ↦
                congrArg (fun f : F.obj i₀ ⟶ F.obj i' ↦ f s)
                  (F.map_comp (homOfLE h) (homOfLE h')).symm }
          αᵢ'ᵢ.toLinearMap.rTensor M₀ t = 0) := by
  classical
  let : Nonempty I := ⟨i₀⟩
  let : IsFiltered I := inferInstance
  let : PreservesColimit F (forget CommRingCat) := inferInstance
  let S := F.obj i₀
  let R := colimit F
  let : Algebra S R := (colimit.ι F i₀).hom.toAlgebra
  let J := {i : I // i₀ ≤ i}
  let : Nonempty J := ⟨⟨i₀, le_rfl⟩⟩
  let : IsDirectedOrder J := ⟨fun i j ↦ by
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.val j.val
    exact ⟨⟨k, i.property.trans hik⟩, hik, hjk⟩⟩
  let A : J → Type v := fun i ↦ F.obj i.val
  let : ∀ i, CommRing (A i) := fun i ↦ inferInstance
  let : ∀ i, Algebra S (A i) := fun i ↦ (F.map (homOfLE i.property)).hom.toAlgebra
  let f (i j : J) (h : i ≤ j) : A i →ₗ[S] A j :=
    AlgHom.toLinearMap
      { (F.map (homOfLE h)).hom with
        commutes' := fun s ↦ congrArg (fun p : F.obj i₀ ⟶ F.obj j.val ↦ p s)
          (F.map_comp (homOfLE i.property) (homOfLE h)).symm }
  let α (i : J) : A i →ₗ[S] R :=
    AlgHom.toLinearMap
      { (colimit.ι F i.val).hom with
        commutes' := fun s ↦ congrArg (fun p : F.obj i₀ ⟶ colimit F ↦ p s)
          (colimit.w F (homOfLE i.property)) }
  have compat (i j : J) (h : i ≤ j) (a : A i) : α j (f i j h a) = α i a := by
    exact ConcreteCategory.congr_hom (colimit.w F (homOfLE h)) a
  let : DirectedSystem A (fun {i j} h ↦ f i j h) :=
    { map_self := by
        intro i a
        change F.map (homOfLE (le_refl i.val)) a = a
        simp
      map_map := by
        intro i j k hij hjk a
        change F.map (homOfLE hjk) (F.map (homOfLE hij) a) =
          F.map (homOfLE (hij.trans hjk)) a
        exact (ConcreteCategory.congr_hom
          (F.map_comp (homOfLE hij) (homOfLE hjk)) a).symm }
  let g : Module.DirectLimit A f →ₗ[S] R :=
    Module.DirectLimit.lift S J A f α compat
  have ginj : Function.Injective g := by
    intro x y hxy
    obtain ⟨i, a, hx⟩ := Module.DirectLimit.exists_of x
    obtain ⟨j, b, hy⟩ := Module.DirectLimit.exists_of y
    rw [← hx, ← hy] at hxy ⊢
    simp only [g, Module.DirectLimit.lift_of] at hxy
    obtain ⟨k, u, v, he⟩ := Concrete.colimit_exists_of_rep_eq F a b hxy
    let k' : J := ⟨k, i.property.trans (leOfHom u)⟩
    have he' : f i k' (leOfHom u) a = f j k' (leOfHom v) b := he
    rw [← Module.DirectLimit.of_f (f := f) (i := i) (j := k') (hij := leOfHom u),
      ← Module.DirectLimit.of_f (f := f) (i := j) (j := k') (hij := leOfHom v), he']
  have gsurj : Function.Surjective g := by
    intro r
    obtain ⟨i, a, ha⟩ := Concrete.colimit_exists_rep F r
    obtain ⟨j, h₀j, hij⟩ := exists_ge_ge i₀ i
    let j' : J := ⟨j, h₀j⟩
    refine ⟨Module.DirectLimit.of S J A f j' (F.map (homOfLE hij) a), ?_⟩
    simp only [g, Module.DirectLimit.lift_of]
    change colimit.ι F j (F.map (homOfLE hij) a) = r
    exact (ConcreteCategory.congr_hom (colimit.w F (homOfLE hij)) a).trans ha
  let E : Module.DirectLimit A f ≃ₗ[S] R := LinearEquiv.ofBijective g ⟨ginj, gsurj⟩
  let ft (i j : J) (h : i ≤ j) := (f i j h).rTensor M₀
  let e : Module.DirectLimit (fun i ↦ A i ⊗[S] M₀) ft ≃ₗ[S] R ⊗[S] M₀ :=
    (TensorProduct.directLimitLeft f M₀).symm.trans (E.rTensor M₀)
  have e_of (i : J) (t : A i ⊗[S] M₀) :
      e (Module.DirectLimit.of S J (fun i ↦ A i ⊗[S] M₀) ft i t) =
        (α i).rTensor M₀ t := by
    induction t using TensorProduct.inductionOn with
    | tmul a m =>
      dsimp only [e, ft]
      rw [LinearEquiv.trans_apply, TensorProduct.directLimitLeft_symm_of_tmul,
        LinearEquiv.rTensor_tmul, LinearMap.rTensor_tmul]
      change g (Module.DirectLimit.of S J A f i a) ⊗ₜ[S] m = α i a ⊗ₜ[S] m
      simp only [g, Module.DirectLimit.lift_of]
    | add t u ht hu => simpa only [map_add] using congrArg₂ (· + ·) ht hu
  let : DirectedSystem (fun i ↦ A i ⊗[S] M₀) (fun {i j} h ↦ ft i j h) :=
    { map_self := by
        intro i t
        induction t using TensorProduct.inductionOn with
        | tmul a m => simp only [ft, LinearMap.rTensor_tmul, DirectedSystem.map_self']
        | add t u ht hu => simpa only [map_add] using congrArg₂ (· + ·) ht hu
      map_map := by
        intro i j k hij hjk t
        induction t using TensorProduct.inductionOn with
        | tmul a m => simp only [ft, LinearMap.rTensor_tmul, DirectedSystem.map_map']
        | add t u ht hu => simpa only [map_add] using congrArg₂ (· + ·) ht hu }
  dsimp only
  constructor
  · intro x
    obtain ⟨i, t, ht⟩ := Module.DirectLimit.exists_of (e.symm x)
    refine ⟨i.val, i.property, t, ?_⟩
    change (α i).rTensor M₀ t = x
    rw [← e_of, ht, e.apply_symm_apply]
  · intro i h t ht
    let i' : J := ⟨i, h⟩
    have hz : Module.DirectLimit.of S J (fun i ↦ A i ⊗[S] M₀) ft i' t = 0 := by
      apply e.injective
      rw [e_of, map_zero]
      exact ht
    obtain ⟨j, hij, he⟩ := Module.DirectLimit.of.zero_exact hz
    exact ⟨j.val, hij, he⟩

end TensorProduct
